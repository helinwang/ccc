package main

import (
	"bufio"
	"bytes"
	"compress/gzip"
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log"
	"net"
	"net/http"
	"net/url"
	"os"
	"os/signal"
	"sort"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"
)

const upstreamURL = "https://api.anthropic.com"

// OAuth constants for token refresh.
const (
	oauthTokenURL    = "https://api.anthropic.com/v1/oauth/token"
	oauthClientID    = "9d1c250a-e61b-44d9-88ed-5944d1962f5e"
	refreshBeforeExp = 5 * time.Minute
)

// Log levels.
const (
	LevelDebug = iota
	LevelInfo
	LevelWarn
	LevelError
)

var logLevel int

func logDebug(format string, args ...any) {
	if logLevel <= LevelDebug {
		log.Printf("[DEBUG] "+format, args...)
	}
}

func logInfo(format string, args ...any) {
	if logLevel <= LevelInfo {
		log.Printf("[INFO]  "+format, args...)
	}
}

func logWarn(format string, args ...any) {
	if logLevel <= LevelWarn {
		log.Printf("[WARN]  "+format, args...)
	}
}

func logError(format string, args ...any) {
	if logLevel <= LevelError {
		log.Printf("[ERROR] "+format, args...)
	}
}

func parseLogLevel(s string) (int, error) {
	switch strings.ToLower(s) {
	case "debug":
		return LevelDebug, nil
	case "info":
		return LevelInfo, nil
	case "warn":
		return LevelWarn, nil
	case "error":
		return LevelError, nil
	default:
		return 0, fmt.Errorf("unknown log level %q (use debug, info, warn, error)", s)
	}
}

// tokenTag returns a short identifier (last 4 chars) of the token for logging.
func tokenTag(token string) string {
	if len(token) <= 8 {
		return "..." + token[len(token)/2:]
	}
	return "..." + token[len(token)-4:]
}

// account tracks one bearer token and whether it is currently skipped.
// skipUntil is set from the upstream Retry-After header when a 429 is received.
// If the upstream sends no Retry-After, skipUntil defaults to 10 minutes.
type account struct {
	mu           sync.Mutex
	token        string
	refreshToken string
	expiresAt    time.Time
	skipUntil    time.Time
}

func (a *account) getToken() string {
	a.mu.Lock()
	defer a.mu.Unlock()
	return a.token
}

func (a *account) update(token, refreshToken string, expiresAt time.Time) {
	a.mu.Lock()
	defer a.mu.Unlock()
	a.token = token
	a.refreshToken = refreshToken
	a.expiresAt = expiresAt
}

// pool manages accounts with fill-first selection.
type pool struct {
	mu       sync.Mutex
	accounts []*account
	current  int
}

type tokenEntry struct {
	token        string
	refreshToken string
	expiresAt    time.Time
}

func newPool(entries []tokenEntry) *pool {
	accs := make([]*account, len(entries))
	for i, e := range entries {
		accs[i] = &account{
			token:        e.token,
			refreshToken: e.refreshToken,
			expiresAt:    e.expiresAt,
		}
	}
	return &pool{accounts: accs}
}

// soonest returns the earliest skipUntil among all accounts.
func (p *pool) soonest() time.Time {
	p.mu.Lock()
	defer p.mu.Unlock()
	var earliest time.Time
	for _, a := range p.accounts {
		if earliest.IsZero() || a.skipUntil.Before(earliest) {
			earliest = a.skipUntil
		}
	}
	return earliest
}

// pick returns the first non-skipped account, or nil if all are skipped.
func (p *pool) pick() *account {
	p.mu.Lock()
	defer p.mu.Unlock()
	now := time.Now()
	n := len(p.accounts)
	for i := 0; i < n; i++ {
		idx := (p.current + i) % n
		a := p.accounts[idx]
		if now.After(a.skipUntil) {
			p.current = idx
			logDebug("picked account %d/%d (%s)", idx+1, n, tokenTag(a.getToken()))
			return a
		}
		logDebug("account %d/%d skipped (resumes %s)", idx+1, n, a.skipUntil.Format(time.RFC3339))
	}
	return nil
}

// skip marks a as unavailable based on the Retry-After header value.
// If retryAfter is empty (no header), the account is skipped for 10 minutes.
func (p *pool) skip(a *account, retryAfter string) {
	p.mu.Lock()
	defer p.mu.Unlock()

	resume := parseRetryAfter(retryAfter)
	a.skipUntil = resume

	for i, acc := range p.accounts {
		if acc == a {
			logWarn("account %d/%d (%s) 429'd, skip until %s (retry-after: %q)",
				i+1, len(p.accounts), tokenTag(a.getToken()), resume.Format(time.RFC3339), retryAfter)
			p.current = (i + 1) % len(p.accounts)
			return
		}
	}
}

// snapshot returns a shallow copy of the accounts slice for iteration outside the lock.
func (p *pool) snapshot() []*account {
	p.mu.Lock()
	defer p.mu.Unlock()
	cp := make([]*account, len(p.accounts))
	copy(cp, p.accounts)
	return cp
}

// hop-by-hop headers must not be forwarded.
var hopHeaders = []string{
	"Connection", "Keep-Alive", "Proxy-Authenticate", "Proxy-Authorization",
	"Te", "Trailers", "Transfer-Encoding", "Upgrade",
}

type proxy struct {
	upstream *url.URL
	pool     *pool
	client   *http.Client
}

const maxBodySize = 32 << 20 // 32 MiB

func (p *proxy) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	start := time.Now()
	logInfo("%s %s %s", r.Method, r.URL.Path, r.RemoteAddr)

	// Buffer body so we can replay it on retry.
	body, err := io.ReadAll(io.LimitReader(r.Body, maxBodySize+1))
	if err != nil {
		logError("read body: %v", err)
		http.Error(w, "read body", http.StatusInternalServerError)
		return
	}
	if int64(len(body)) > maxBodySize {
		logWarn("body too large (%d bytes) from %s", len(body), r.RemoteAddr)
		http.Error(w, "request body too large", http.StatusRequestEntityTooLarge)
		return
	}
	logDebug("body %d bytes", len(body))

	// Retry loop: only 429s are retried with account rotation.
	// Everything else (success, errors, non-429 status) passes through to client.
	// When all accounts are skipped, return 429 with retry timing to client.
	// Bound at len(accounts)+1 attempts so a single request can't loop forever.
	maxAttempts := len(p.pool.accounts) + 1
	for attempt := 0; attempt < maxAttempts; attempt++ {
		acct := p.pool.pick()
		if acct == nil {
			wait := time.Until(p.pool.soonest())
			if wait <= 0 {
				// Race: account un-expired between pick() and soonest(). Retry.
				time.Sleep(10 * time.Millisecond)
				continue
			}
			// Return 429 with retry timing so the client knows when to come back.
			retrySecs := int(wait.Truncate(time.Second).Seconds())
			if retrySecs < 1 {
				retrySecs = 1
			}
			logWarn("all accounts skipped, retry-after %ds (%s %s, %s)",
				retrySecs, r.Method, r.URL.Path, time.Since(start).Round(time.Millisecond))
			w.Header().Set("Retry-After", strconv.Itoa(retrySecs))
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusTooManyRequests)
			errBody, _ := json.Marshal(map[string]any{
				"type": "error",
				"error": map[string]any{
					"type":    "rate_limit_error",
					"message": fmt.Sprintf("Rate limited. Retry after %d seconds.", retrySecs),
				},
			})
			w.Write(errBody) //nolint:errcheck
			return
		}
		resp, err := p.forward(r, acct, body)
		if err != nil {
			logError("forward to upstream: %v", err)
			http.Error(w, "upstream error", http.StatusBadGateway)
			return
		}
		if resp.StatusCode != http.StatusTooManyRequests {
			if resp.StatusCode >= 400 {
				// Stream raw bytes to the client untouched, while teeing the
				// first maxLogBytes into a buffer we can decode for the log.
				capture := &capWriter{max: maxLogBytes}
				writeResponsePrefix(w, resp)
				flusher, canFlush := w.(http.Flusher)
				tee := io.TeeReader(resp.Body, capture)
				buf := make([]byte, 32*1024)
				var copyErr error
				for {
					n, readErr := tee.Read(buf)
					if n > 0 {
						w.Write(buf[:n]) //nolint:errcheck
						if canFlush {
							flusher.Flush()
						}
					}
					if readErr != nil {
						if readErr != io.EOF {
							copyErr = readErr
						}
						break
					}
				}
				resp.Body.Close()
				if copyErr != nil {
					logWarn("error copying response body to client: %v", copyErr)
				}
				decoded, tag := decodeBytes(capture.buf.Bytes(), resp.Header.Get("Content-Encoding"))
				if len(decoded) > maxLogBytes {
					decoded = decoded[:maxLogBytes]
				}
				logWarn("%s %s → %d (%s) headers=[%s] body(%s)=%s",
					r.Method, r.URL.Path, resp.StatusCode,
					time.Since(start).Round(time.Millisecond),
					formatHeaders(resp.Header), tag, decoded)
			} else {
				logInfo("%s %s → %d (%s)", r.Method, r.URL.Path, resp.StatusCode, time.Since(start).Round(time.Millisecond))
				writeResponse(w, resp)
				resp.Body.Close()
			}
			return
		}
		// 429 — body is not forwarded to client; read up to maxLogBytes and decode for log.
		retryAfter := resp.Header.Get("Retry-After")
		raw, _ := io.ReadAll(io.LimitReader(resp.Body, maxLogBytes))
		resp.Body.Close()
		decoded, tag := decodeBytes(raw, resp.Header.Get("Content-Encoding"))
		if len(decoded) > maxLogBytes {
			decoded = decoded[:maxLogBytes]
		}
		logWarn("429 from upstream (account %s) retry-after=%q headers=[%s] body(%s)=%s",
			tokenTag(acct.getToken()), retryAfter, formatHeaders(resp.Header), tag, decoded)
		p.pool.skip(acct, retryAfter)
	}
	// Exhausted all attempts (each account 429'd in this single request).
	logError("retry budget exhausted (%d attempts) for %s %s", maxAttempts, r.Method, r.URL.Path)
	http.Error(w, "all accounts rate-limited", http.StatusTooManyRequests)
}

func (p *proxy) forward(r *http.Request, acct *account, body []byte) (*http.Response, error) {
	target := *p.upstream
	target.Path = r.URL.Path
	target.RawQuery = r.URL.RawQuery

	req, err := http.NewRequestWithContext(r.Context(), r.Method, target.String(), bytes.NewReader(body))
	if err != nil {
		return nil, err
	}
	// Forward all headers as-is. Copy slice values, not references, so the
	// two requests don't alias each other's header storage.
	for k, v := range r.Header {
		vv := make([]string, len(v))
		copy(vv, v)
		req.Header[k] = vv
	}
	for _, h := range hopHeaders {
		req.Header.Del(h)
	}
	// Replace auth with this account's token.
	tok := acct.getToken()
	req.Header.Del("X-Api-Key")
	req.Header.Set("Authorization", "Bearer "+tok)

	logDebug("→ %s %s (%s)", req.Method, req.URL, tokenTag(tok))
	return p.client.Do(req)
}

// writeResponsePrefix writes response headers and status code without the body.
func writeResponsePrefix(w http.ResponseWriter, resp *http.Response) {
	for k, v := range resp.Header {
		w.Header()[k] = v
	}
	for _, h := range hopHeaders {
		w.Header().Del(h)
	}
	w.WriteHeader(resp.StatusCode)
}

func writeResponse(w http.ResponseWriter, resp *http.Response) {
	writeResponsePrefix(w, resp)

	// Flush after each chunk so SSE / streaming reaches the client incrementally.
	flusher, canFlush := w.(http.Flusher)
	buf := make([]byte, 32*1024)
	for {
		n, err := resp.Body.Read(buf)
		if n > 0 {
			w.Write(buf[:n]) //nolint:errcheck
			if canFlush {
				flusher.Flush()
			}
		}
		if err != nil {
			break
		}
	}
}

// maxLogBytes caps how many body bytes we capture for any single log line.
const maxLogBytes = 4096

// decodeBytes decompresses raw according to Content-Encoding for logging
// purposes. Returns the decoded bytes (or raw on failure) plus a tag
// describing what happened so the caller can put it in a log line.
func decodeBytes(raw []byte, contentEncoding string) ([]byte, string) {
	enc := strings.ToLower(strings.TrimSpace(contentEncoding))
	switch enc {
	case "", "identity":
		return raw, "identity"
	case "gzip":
		gr, err := gzip.NewReader(bytes.NewReader(raw))
		if err != nil {
			return raw, fmt.Sprintf("gzip-open-error:%v", err)
		}
		defer gr.Close()
		out, err := io.ReadAll(gr)
		if err != nil && len(out) == 0 {
			return raw, fmt.Sprintf("gzip-read-error:%v", err)
		}
		// Partial reads (truncated capture) may return err with some data —
		// keep what we got.
		return out, "gzip"
	default:
		// br / zstd / deflate — no stdlib decoder we want to pull in. Log the
		// fact so the operator knows why the bytes look like garbage.
		return raw, "encoding=" + enc + " (not decoded)"
	}
}

// capWriter is an io.Writer that buffers up to max bytes and silently drops
// the rest. Used to capture a bounded prefix of a streamed response for logs.
type capWriter struct {
	buf bytes.Buffer
	max int
}

func (c *capWriter) Write(p []byte) (int, error) {
	remaining := c.max - c.buf.Len()
	if remaining > 0 {
		if len(p) <= remaining {
			c.buf.Write(p)
		} else {
			c.buf.Write(p[:remaining])
		}
	}
	return len(p), nil
}

// formatHeaders renders headers as a single-line k=v list for logging.
func formatHeaders(h http.Header) string {
	var keys []string
	for k := range h {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	var b strings.Builder
	for i, k := range keys {
		if i > 0 {
			b.WriteString(" ")
		}
		b.WriteString(k)
		b.WriteString("=")
		b.WriteString(strings.Join(h.Values(k), ","))
	}
	return b.String()
}

// parseRetryAfter converts a Retry-After header value to an absolute time.
// Supports both delay-seconds (e.g. "30") and HTTP-date formats.
// Falls back to 10 minutes if empty or unparseable.
// The result is always clamped to at least 1 second in the future to prevent
// tight retry loops on Retry-After: 0 or HTTP-dates in the past.
func parseRetryAfter(h string) time.Time {
	now := time.Now()
	var resume time.Time
	if h != "" {
		if secs, err := strconv.Atoi(h); err == nil && secs >= 0 {
			resume = now.Add(time.Duration(secs) * time.Second)
		} else if t, err := http.ParseTime(h); err == nil {
			resume = t
		}
	}
	if resume.IsZero() {
		logDebug("no/invalid retry-after %q, defaulting to 10m skip", h)
		return now.Add(10 * time.Minute)
	}
	if minResume := now.Add(time.Second); resume.Before(minResume) {
		return minResume
	}
	return resume
}

// loadTokens reads a token file: one entry per line, blank lines ignored.
// Each line is comma-separated: access_token[,refresh_token[,expires_at_rfc3339]]
func loadTokens(path string) ([]tokenEntry, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()

	var entries []tokenEntry
	sc := bufio.NewScanner(f)
	for sc.Scan() {
		line := strings.TrimSpace(sc.Text())
		if line == "" {
			continue
		}
		parts := strings.SplitN(line, ",", 3)
		e := tokenEntry{token: strings.TrimSpace(parts[0])}
		if len(parts) >= 2 {
			e.refreshToken = strings.TrimSpace(parts[1])
		}
		if len(parts) >= 3 {
			if t, err := time.Parse(time.RFC3339, strings.TrimSpace(parts[2])); err == nil {
				e.expiresAt = t
			}
		}
		entries = append(entries, e)
	}
	return entries, sc.Err()
}

// saveTokens rewrites the token file with updated access tokens and expiry times.
// Blank lines from the original file are preserved.
func saveTokens(path string, accounts []*account) error {
	orig, err := os.ReadFile(path)
	if err != nil {
		return err
	}

	var b strings.Builder
	sc := bufio.NewScanner(bytes.NewReader(orig))
	idx := 0
	for sc.Scan() {
		line := sc.Text()
		trimmed := strings.TrimSpace(line)
		if trimmed == "" {
			fmt.Fprintln(&b, line)
			continue
		}
		if idx < len(accounts) {
			a := accounts[idx]
			a.mu.Lock()
			tok := a.token
			rt := a.refreshToken
			exp := a.expiresAt
			a.mu.Unlock()

			if rt == "" {
				fmt.Fprintln(&b, tok)
			} else if exp.IsZero() {
				fmt.Fprintf(&b, "%s,%s\n", tok, rt)
			} else {
				fmt.Fprintf(&b, "%s,%s,%s\n", tok, rt, exp.Format(time.RFC3339))
			}
			idx++
		}
	}
	// Append any extra accounts not in the original file.
	for ; idx < len(accounts); idx++ {
		a := accounts[idx]
		a.mu.Lock()
		tok := a.token
		rt := a.refreshToken
		exp := a.expiresAt
		a.mu.Unlock()

		if rt == "" {
			fmt.Fprintln(&b, tok)
		} else if exp.IsZero() {
			fmt.Fprintf(&b, "%s,%s\n", tok, rt)
		} else {
			fmt.Fprintf(&b, "%s,%s,%s\n", tok, rt, exp.Format(time.RFC3339))
		}
	}
	tmp := path + ".tmp"
	if err := os.WriteFile(tmp, []byte(b.String()), 0600); err != nil {
		return err
	}
	return os.Rename(tmp, path)
}

// refreshOAuthToken exchanges a refresh token for a new access token.
func refreshOAuthToken(ctx context.Context, client *http.Client, refreshToken string) (accessToken, newRefreshToken string, expiresAt time.Time, err error) {
	body, _ := json.Marshal(map[string]string{
		"client_id":     oauthClientID,
		"grant_type":    "refresh_token",
		"refresh_token": refreshToken,
	})
	req, err := http.NewRequestWithContext(ctx, "POST", oauthTokenURL, bytes.NewReader(body))
	if err != nil {
		return "", "", time.Time{}, err
	}
	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("Accept", "application/json")

	resp, err := client.Do(req)
	if err != nil {
		return "", "", time.Time{}, err
	}
	defer resp.Body.Close()

	respBody, err := io.ReadAll(resp.Body)
	if err != nil {
		return "", "", time.Time{}, err
	}
	if resp.StatusCode != http.StatusOK {
		return "", "", time.Time{}, fmt.Errorf("refresh failed (status %d): %s", resp.StatusCode, respBody)
	}

	var tok struct {
		AccessToken  string `json:"access_token"`
		RefreshToken string `json:"refresh_token"`
		ExpiresIn    int    `json:"expires_in"`
	}
	if err := json.Unmarshal(respBody, &tok); err != nil {
		return "", "", time.Time{}, err
	}

	exp := time.Now().Add(time.Duration(tok.ExpiresIn) * time.Second)
	return tok.AccessToken, tok.RefreshToken, exp, nil
}

// earliestRefreshAt returns the time at which the next scheduled refresh
// should fire (refreshBeforeExp before the earliest expiry), or zero if
// no account has a known expiry.
func earliestRefreshAt(accounts []*account) time.Time {
	var earliest time.Time
	for _, a := range accounts {
		a.mu.Lock()
		rt := a.refreshToken
		exp := a.expiresAt
		a.mu.Unlock()
		if rt == "" || exp.IsZero() {
			continue
		}
		if earliest.IsZero() || exp.Before(earliest) {
			earliest = exp
		}
	}
	if earliest.IsZero() {
		return time.Time{}
	}
	return earliest.Add(-refreshBeforeExp)
}

// refreshTokens refreshes accounts that have a refresh token.
// If onlyExpiring is true, only tokens within refreshBeforeExp of expiry are refreshed.
// Returns counts of refreshed and failed.
func refreshTokens(client *http.Client, accounts []*account, onlyExpiring bool) (refreshed, failed int) {
	now := time.Now()
	for _, a := range accounts {
		a.mu.Lock()
		rt := a.refreshToken
		exp := a.expiresAt
		a.mu.Unlock()
		if rt == "" {
			continue
		}
		if onlyExpiring && !exp.IsZero() && now.Before(exp.Add(-refreshBeforeExp)) {
			continue
		}
		ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
		newAccess, newRefresh, newExp, err := refreshOAuthToken(ctx, client, rt)
		cancel()
		if err != nil {
			logError("refresh token %s: %v", tokenTag(rt), err)
			failed++
			continue
		}
		// Defensively keep the old refresh token if the response omitted one.
		if newRefresh == "" {
			newRefresh = rt
		}
		a.update(newAccess, newRefresh, newExp)
		logDebug("refreshed token %s, expires %s", tokenTag(newAccess), newExp.Format(time.RFC3339))
		refreshed++
	}
	return
}

func main() {
	listenAddr := flag.String("listen", "127.0.0.1:7999", "address to listen on")
	tokenFile := flag.String("tokens", "tokens.txt", "token file: access_token[,refresh_token[,expires_at]] per line")
	level := flag.String("log", "info", "log level (debug, info, warn, error)")
	flag.Parse()

	var err error
	logLevel, err = parseLogLevel(*level)
	if err != nil {
		log.Fatal(err)
	}

	entries, err := loadTokens(*tokenFile)
	if err != nil {
		log.Fatalf("tokens: %v", err)
	}
	if len(entries) == 0 {
		log.Fatal("no tokens found in ", *tokenFile)
	}

	p := newPool(entries)

	upstream, err := url.Parse(upstreamURL)
	if err != nil {
		log.Fatalf("upstream: %v", err)
	}

	// Custom transport: bound connection setup and time-to-first-byte, but
	// no overall request timeout — long SSE streams must be allowed to run.
	transport := &http.Transport{
		Proxy: http.ProxyFromEnvironment,
		DialContext: (&net.Dialer{
			Timeout:   10 * time.Second,
			KeepAlive: 30 * time.Second,
		}).DialContext,
		ForceAttemptHTTP2:     true,
		MaxIdleConns:          100,
		IdleConnTimeout:       90 * time.Second,
		TLSHandshakeTimeout:   10 * time.Second,
		ExpectContinueTimeout: 1 * time.Second,
		ResponseHeaderTimeout: 60 * time.Second,
	}
	httpClient := &http.Client{Transport: transport}
	handler := &proxy{upstream: upstream, pool: p, client: httpClient}

	// Check if any accounts have refresh tokens.
	accounts := p.snapshot()
	hasRefresh := false
	for _, a := range accounts {
		a.mu.Lock()
		rt := a.refreshToken
		a.mu.Unlock()
		if rt != "" {
			hasRefresh = true
			break
		}
	}

	if hasRefresh {
		// Refresh all tokens at startup.
		refreshed, failed := refreshTokens(httpClient, accounts, false)
		total := refreshed + failed
		nextRefresh := earliestRefreshAt(accounts)
		if !nextRefresh.IsZero() {
			logInfo("startup: refreshed %d/%d tokens (%d failed), next refresh at %s (in %s)",
				refreshed, total, failed, nextRefresh.Format(time.RFC3339), time.Until(nextRefresh).Round(time.Second))
		} else {
			logInfo("startup: refreshed %d/%d tokens (%d failed)", refreshed, total, failed)
		}
		if refreshed > 0 {
			if err := saveTokens(*tokenFile, accounts); err != nil {
				logError("save tokens: %v", err)
			}
		}
	} else {
		logWarn("no refresh tokens found, automatic token refresh disabled")
		logInfo("loaded %d accounts", len(entries))
	}

	// Background goroutine: refresh tokens before expiry (only if refresh tokens exist).
	// On failure or unknown expiry: exponential backoff (30s → 1h, then hourly).
	if hasRefresh {
		go func() {
			backoff := []time.Duration{
				30 * time.Second, time.Minute, 2 * time.Minute,
				5 * time.Minute, 15 * time.Minute, 30 * time.Minute, time.Hour,
			}
			failedCount := 0 // 0 = no recent failure; N = N consecutive failures
			for {
				accounts := p.snapshot()
				refreshAt := earliestRefreshAt(accounts)

				var wait time.Duration
				switch {
				case failedCount > 0:
					idx := failedCount - 1
					if idx >= len(backoff) {
						idx = len(backoff) - 1
					}
					wait = backoff[idx]
				case refreshAt.IsZero():
					wait = backoff[0]
					logWarn("no known token expiry, retrying refresh in %s", wait)
				default:
					wait = time.Until(refreshAt)
				}
				if wait > 0 {
					time.Sleep(wait)
				}

				// Refresh all tokens within the refresh window.
				accounts = p.snapshot()
				refreshed, failed := refreshTokens(httpClient, accounts, true)
				total := refreshed + failed
				if refreshed > 0 {
					failedCount = 0
					next := earliestRefreshAt(accounts)
					logInfo("scheduled refresh: refreshed %d/%d tokens (%d failed), next refresh at %s (in %s)",
						refreshed, total, failed, next.Format(time.RFC3339), time.Until(next).Round(time.Second))
					if err := saveTokens(*tokenFile, accounts); err != nil {
						logError("save tokens: %v", err)
					}
				} else if total > 0 {
					failedCount++
					nextIdx := failedCount - 1
					if nextIdx >= len(backoff) {
						nextIdx = len(backoff) - 1
					}
					logWarn("scheduled refresh: all %d tokens failed, retrying in %s", total, backoff[nextIdx])
				}
			}
		}()
	}

	srv := &http.Server{
		Addr:              *listenAddr,
		Handler:           handler,
		ReadHeaderTimeout: 10 * time.Second,
		// No ReadTimeout / WriteTimeout: long SSE streaming responses must
		// be allowed to run for as long as the upstream keeps producing.
	}
	go func() {
		ch := make(chan os.Signal, 1)
		signal.Notify(ch, syscall.SIGINT, syscall.SIGTERM)
		sig := <-ch
		logInfo("received %s, shutting down (30s grace period)", sig)
		ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
		defer cancel()
		if err := srv.Shutdown(ctx); err != nil {
			logWarn("shutdown: %v", err)
			srv.Close()
		}
	}()

	logInfo("ccc listening on %s → %s (%d accounts)", *listenAddr, upstreamURL, len(entries))
	if err := srv.ListenAndServe(); err != http.ErrServerClosed {
		log.Fatal(err)
	}
	logInfo("server stopped")
}
