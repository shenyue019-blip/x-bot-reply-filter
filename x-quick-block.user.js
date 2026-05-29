// ==UserScript==
// @name         X 快捷屏蔽按钮
// @namespace    https://github.com/shenyue019-blip/x-bot-reply-filter
// @version      1.3.7
// @description  在 X/Twitter 评论区给每条回复加一个快捷屏蔽按钮，先入队再按节奏屏蔽，并在页面边缘保留可撤销队列
// @author       summeriscoming
// @license      MIT
// @match        https://x.com/*
// @match        https://*.x.com/*
// @match        https://twitter.com/*
// @match        https://*.twitter.com/*
// @grant        unsafeWindow
// @grant        GM_xmlhttpRequest
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_addValueChangeListener
// @connect      x.com
// @connect      twitter.com
// @run-at       document-start
// @downloadURL  https://raw.githubusercontent.com/shenyue019-blip/x-bot-reply-filter/main/x-quick-block.user.js
// @updateURL    https://raw.githubusercontent.com/shenyue019-blip/x-bot-reply-filter/main/x-quick-block.user.js
// ==/UserScript==

(function () {
  'use strict';

  const SCRIPT_ID = 'xqb';
  const SCRIPT_VERSION = '1.3.7';
  const QUEUE_KEY = 'xqb_block_queue_v1';
  const TIMING_KEY = 'xqb_queue_timing_v1';
  const WORKER_LOCK_KEY = 'xqb_queue_worker_lock_v1';
  const PANEL_COLLAPSED_KEY = 'xqb_panel_collapsed_v1';
  const PANEL_POS_KEY = 'xqb_panel_position_v1';
  const PANEL_SIZE_KEY = 'xqb_panel_size_v1';
  const MAX_QUEUE_ITEMS = 120;
  const FAILURE_COOLDOWN_MS = 15 * 1000;
  const RATE_LIMIT_GRACE_MS = 1000;
  const HALF_HOUR_WINDOW_MS = 30 * 60 * 1000;
  const HOUR_WINDOW_MS = 60 * 60 * 1000;
  const DAY_WINDOW_MS = 24 * 60 * 60 * 1000;
  const MIN_BLOCK_GAP_MS = HALF_HOUR_WINDOW_MS / 10;
  const AUTO_RETRY_MAX = 3;
  const AUTO_RETRY_DELAYS_MS = [MIN_BLOCK_GAP_MS, 10 * 60 * 1000, 30 * 60 * 1000];
  const RATE_LIMIT_HISTORY_MAX = 120;
  const RATE_LIMITS = [
    { label: '30 分钟窗口', limit: 10, windowMs: HALF_HOUR_WINDOW_MS },
    { label: '1 小时窗口', limit: 20, windowMs: HOUR_WINDOW_MS },
    { label: '24 小时窗口', limit: 100, windowMs: DAY_WINDOW_MS },
  ];
  const LOCK_TTL_MS = 25 * 1000;
  const STALE_RUNNING_MS = 2 * 60 * 1000;
  const BUTTON_TEXT = '禁';
  const BLOCKED_TEXT = 'OK';
  const BEARER = 'AAAAAAAAAAAAAAAAAAAAANRILgAAAAAAnNwIzUejRCOuH5E6I8xnZz4puTs%3D1Zv7ttfk8LF81IUq16cHjhLTvJu4FA33AGWWjCpTnA';
  const TAB_ID = `${Date.now().toString(36)}-${Math.random().toString(36).slice(2)}`;

  let liveBearer = null;
  let scanQueued = false;
  let workerActive = false;
  let workerWakeTimer = null;
  let lastScanStats = { candidates: 0, handles: 0, buttons: 0 };
  let collapsedPanelDraggedAt = 0;
  const busyHandles = new Set();
  const cancelRequestedHandles = new Set();
  const inFlightBlockRequests = new Map();

  function mountRoot() {
    return document.body || document.documentElement;
  }

  function normalizeHandle(value) {
    const m = String(value || '').trim().replace(/^@+/, '').match(/[A-Za-z0-9_]{1,15}/);
    return m ? m[0].toLowerCase() : '';
  }

  function displayHandle(value) {
    const m = String(value || '').trim().replace(/^@+/, '').match(/[A-Za-z0-9_]{1,15}/);
    return m ? m[0] : '';
  }

  function textOf(node) {
    if (!node) return '';
    const parts = [];
    const walk = document.createTreeWalker(node, NodeFilter.SHOW_TEXT | NodeFilter.SHOW_ELEMENT);
    let current = walk.currentNode;
    while (current) {
      if (current.nodeType === Node.TEXT_NODE) {
        parts.push(current.nodeValue || '');
      } else if (current.nodeType === Node.ELEMENT_NODE) {
        const el = current;
        const tag = String(el.tagName || '').toLowerCase();
        if (tag === 'img') {
          const alt = el.getAttribute('alt');
          if (alt) parts.push(alt);
        } else if (tag === 'br') {
          parts.push('\n');
        }
      }
      current = walk.nextNode();
    }
    return parts.join('').replace(/[ \t\f\v]+/g, ' ').replace(/\s*\n\s*/g, '\n').trim();
  }

  function getCookie(name) {
    const prefix = `${name}=`;
    return document.cookie.split(';').map(v => v.trim()).find(v => v.startsWith(prefix))?.slice(prefix.length) || '';
  }

  function toast(message, isError = false) {
    document.getElementById(`${SCRIPT_ID}-toast`)?.remove();
    const el = document.createElement('div');
    el.id = `${SCRIPT_ID}-toast`;
    el.textContent = message;
    el.style.cssText = [
      'position:fixed',
      'right:16px',
      'bottom:22px',
      'z-index:2147483647',
      `background:${isError ? '#f4212e' : '#0f1419'}`,
      'color:#fff',
      'font-size:13px',
      'line-height:1.35',
      'font-weight:700',
      'padding:8px 12px',
      'border-radius:8px',
      'box-shadow:0 8px 24px rgba(0,0,0,.18)',
      'max-width:320px',
      'pointer-events:none',
    ].join(';');
    mountRoot().appendChild(el);
    window.setTimeout(() => el.remove(), 2400);
  }

  function bootBadge() {
    document.getElementById(`${SCRIPT_ID}-boot`)?.remove();
    const el = document.createElement('div');
    el.id = `${SCRIPT_ID}-boot`;
    el.textContent = `X 快捷屏蔽 ${SCRIPT_VERSION} 已运行`;
    el.style.cssText = [
      'position:fixed',
      'left:12px',
      'bottom:12px',
      'z-index:2147483647',
      'background:#00ba7c',
      'color:#fff',
      'font-size:12px',
      'font-weight:800',
      'line-height:1.3',
      'padding:7px 10px',
      'border-radius:8px',
      'box-shadow:0 8px 24px rgba(0,0,0,.18)',
      'pointer-events:none',
    ].join(';');
    mountRoot().appendChild(el);
    window.setTimeout(() => el.remove(), 5000);
  }

  function normalizeHeaderObject(headers) {
    const out = {};
    if (!headers) return out;
    if (typeof headers.forEach === 'function') {
      headers.forEach((value, key) => { out[String(key).toLowerCase()] = value; });
      return out;
    }
    if (Array.isArray(headers)) {
      headers.forEach(([key, value]) => { out[String(key).toLowerCase()] = value; });
      return out;
    }
    Object.entries(headers).forEach(([key, value]) => {
      out[String(key).toLowerCase()] = value;
    });
    return out;
  }

  function captureApiHeaders(headers) {
    const auth = normalizeHeaderObject(headers).authorization;
    if (auth && String(auth).startsWith('Bearer ') && String(auth).length > 30) {
      liveBearer = String(auth).slice(7);
    }
  }

  function hookAuth() {
    const win = typeof unsafeWindow !== 'undefined' ? unsafeWindow : window;

    try {
      const origFetch = win.fetch;
      win.fetch = function (input, init) {
        try {
          captureApiHeaders((init && init.headers) || (input && input.headers));
        } catch (_) {}
        return origFetch.apply(this, arguments);
      };
    } catch (err) {
      console.warn('[XQB] fetch hook failed', err);
    }

    try {
      const origOpen = win.XMLHttpRequest.prototype.open;
      const origSet = win.XMLHttpRequest.prototype.setRequestHeader;
      win.XMLHttpRequest.prototype.open = function (method, url) {
        this._xqbUrl = url;
        return origOpen.apply(this, arguments);
      };
      win.XMLHttpRequest.prototype.setRequestHeader = function (name, value) {
        if (!this._xqbHeaders) this._xqbHeaders = {};
        this._xqbHeaders[name] = value;
        if (String(name).toLowerCase() === 'authorization') captureApiHeaders({ authorization: value });
        return origSet.apply(this, arguments);
      };
    } catch (err) {
      console.warn('[XQB] XHR hook failed', err);
    }
  }

  function apiPost(path, handle, opts = {}) {
    const csrf = getCookie('ct0');
    if (!csrf) return Promise.reject(new Error('未找到 ct0 登录凭证，请确认当前页面已登录 X'));
    const bearer = liveBearer || BEARER;
    return new Promise((resolve, reject) => {
      const req = GM_xmlhttpRequest({
        method: 'POST',
        url: `https://x.com${path}`,
        headers: {
          Authorization: `Bearer ${bearer}`,
          'x-csrf-token': csrf,
          'Content-Type': 'application/x-www-form-urlencoded',
          'x-twitter-active-user': 'yes',
          'x-twitter-auth-type': 'OAuth2Session',
        },
        data: `screen_name=${encodeURIComponent(handle)}`,
        anonymous: false,
        timeout: 60000,
        onload(resp) {
          if (resp.status >= 200 && resp.status < 300) {
            resolve(resp.responseText || '');
          } else {
            reject(new Error(apiErrorMessage(resp)));
          }
        },
        onerror() { reject(new Error('网络请求失败')); },
        onabort() { reject(new Error('请求已撤回')); },
        ontimeout() { reject(new Error('请求超时')); },
      });
      try { opts.onRequest?.(req); } catch (_) {}
    });
  }

  function blockUser(handle) {
    const key = normalizeHandle(handle);
    return apiPost('/i/api/1.1/blocks/create.json', handle, {
      onRequest(req) {
        if (key && req?.abort) inFlightBlockRequests.set(key, req);
      },
    }).finally(() => {
      if (key) inFlightBlockRequests.delete(key);
    });
  }

  function unblockUser(handle) {
    return apiPost('/i/api/1.1/blocks/destroy.json', handle);
  }

  function sleep(ms) {
    return new Promise(resolve => window.setTimeout(resolve, Math.max(0, Number(ms) || 0)));
  }

  function cleanErrorText(value, max = 260) {
    return String(value || '')
      .replace(/<[^>]+>/g, ' ')
      .replace(/\s+/g, ' ')
      .trim()
      .slice(0, max);
  }

  function apiErrorMessage(resp) {
    const status = Number(resp?.status || 0) || 0;
    const statusText = cleanErrorText(resp?.statusText || '', 60);
    const prefix = statusText ? `HTTP ${status} ${statusText}` : `HTTP ${status}`;
    const raw = String(resp?.responseText || '').trim();
    if (!raw) return prefix;

    try {
      const json = JSON.parse(raw);
      const error = Array.isArray(json?.errors) ? json.errors[0] : null;
      const message = cleanErrorText(error?.message || json?.error || json?.message || raw);
      const code = error?.code ? `错误码 ${error.code}` : '';
      return [prefix, code, message].filter(Boolean).join('：');
    } catch (_) {
      return `${prefix}：${cleanErrorText(raw)}`;
    }
  }

  function isAuthError(error) {
    return /ct0|HTTP 401|HTTP 403|HTTP 419|登录|auth/i.test(String(error?.message || error || ''));
  }

  function isUserNotFoundError(error) {
    return /not\s*found|notfound|does not exist|HTTP 404|错误码 50|用户不存在|不存在|找不到/i.test(String(error?.message || error || ''));
  }

  function autoRetryDelayMs(retryCount) {
    const index = Math.max(0, Math.min(AUTO_RETRY_DELAYS_MS.length - 1, Number(retryCount || 1) - 1));
    return AUTO_RETRY_DELAYS_MS[index];
  }

  function emptyQueue() {
    return { version: 1, updatedAt: Date.now(), items: [] };
  }

  function sanitizeQueue(raw) {
    const q = raw && typeof raw === 'object' ? raw : emptyQueue();
    const seen = new Set();
    const items = [];
    for (const rawItem of Array.isArray(q.items) ? q.items : []) {
      const key = normalizeHandle(rawItem?.handle || rawItem?.key);
      if (!key || seen.has(key)) continue;
      seen.add(key);
      items.push({
        key,
        handle: displayHandle(rawItem.handle || key) || key,
        displayName: String(rawItem.displayName || '').slice(0, 80),
        avatarUrl: String(rawItem.avatarUrl || '').slice(0, 500),
        comment: String(rawItem.comment || rawItem.tweetText || '').replace(/\s+/g, ' ').trim().slice(0, 280),
        status: ['queued', 'blocking', 'blocked', 'failed', 'unblocking', 'unblocked'].includes(rawItem.status) ? rawItem.status : 'queued',
        addedAt: Number(rawItem.addedAt || rawItem.blockedAt || Date.now()) || Date.now(),
        updatedAt: Number(rawItem.updatedAt || Date.now()) || Date.now(),
        error: cleanErrorText(rawItem.error || ''),
        retryCount: Math.max(0, Number(rawItem.retryCount || 0) || 0),
        nextRetryAt: Math.max(0, Number(rawItem.nextRetryAt || 0) || 0),
      });
      if (items.length >= MAX_QUEUE_ITEMS) break;
    }
    return { version: 1, updatedAt: Number(q.updatedAt || Date.now()) || Date.now(), items };
  }

  function readQueue() {
    return sanitizeQueue(GM_getValue(QUEUE_KEY, emptyQueue()));
  }

  function writeQueue(queue) {
    const q = sanitizeQueue(queue);
    q.updatedAt = Date.now();
    GM_setValue(QUEUE_KEY, q);
    renderPanel(q);
  }

  function getQueueItem(key, queue = readQueue()) {
    return queue.items.find(item => item.key === normalizeHandle(key)) || null;
  }

  function upsertQueueItem(handle, patch) {
    const key = normalizeHandle(handle);
    if (!key) return null;
    const now = Date.now();
    const queue = readQueue();
    const existing = getQueueItem(key, queue);
    const next = {
      key,
      handle: displayHandle(handle) || existing?.handle || key,
      displayName: String(patch.displayName ?? existing?.displayName ?? '').slice(0, 80),
      avatarUrl: String(patch.avatarUrl ?? existing?.avatarUrl ?? '').slice(0, 500),
      comment: String(patch.comment ?? existing?.comment ?? '').replace(/\s+/g, ' ').trim().slice(0, 280),
      status: patch.status || existing?.status || 'blocked',
      addedAt: existing?.addedAt || now,
      updatedAt: now,
      error: cleanErrorText(patch.error ?? ''),
      retryCount: Math.max(0, Number(patch.retryCount ?? existing?.retryCount ?? 0) || 0),
      nextRetryAt: Math.max(0, Number(patch.nextRetryAt ?? existing?.nextRetryAt ?? 0) || 0),
    };
    if (next.status !== 'failed') next.nextRetryAt = 0;
    if (['blocked', 'unblocked'].includes(next.status)) next.retryCount = 0;
    queue.items = [next, ...queue.items.filter(item => item.key !== key)].slice(0, MAX_QUEUE_ITEMS);
    writeQueue(queue);
    return next;
  }

  function removeQueueItem(key) {
    const norm = normalizeHandle(key);
    const queue = readQueue();
    queue.items = queue.items.filter(item => item.key !== norm);
    writeQueue(queue);
    maybeStartQueueWorker();
  }

  function emptyTiming() {
    return { version: 2, count: 0, nextRunAt: 0, reason: '', history: [] };
  }

  function normalizeBlockHistory(value, now = Date.now()) {
    const cutoff = now - DAY_WINDOW_MS;
    return (Array.isArray(value) ? value : [])
      .map(Number)
      .filter(ts => Number.isFinite(ts) && ts > cutoff && ts <= now + RATE_LIMIT_GRACE_MS)
      .sort((a, b) => a - b)
      .slice(-RATE_LIMIT_HISTORY_MAX);
  }

  function readTiming() {
    const raw = GM_getValue(TIMING_KEY, emptyTiming());
    const history = normalizeBlockHistory(raw?.history);
    return {
      version: 2,
      count: history.length,
      nextRunAt: Math.max(0, Number(raw?.nextRunAt || 0) || 0),
      reason: String(raw?.reason || '').slice(0, 120),
      history,
    };
  }

  function writeTiming(timing) {
    const history = normalizeBlockHistory(timing?.history);
    GM_setValue(TIMING_KEY, {
      version: 2,
      count: history.length,
      nextRunAt: Math.max(0, Number(timing?.nextRunAt || 0) || 0),
      reason: String(timing?.reason || '').slice(0, 120),
      history,
    });
  }

  function queueCounts(queue = readQueue()) {
    const counts = { queued: 0, blocking: 0, blocked: 0, failed: 0, unblocking: 0, unblocked: 0 };
    for (const item of queue.items) {
      if (Object.prototype.hasOwnProperty.call(counts, item.status)) counts[item.status] += 1;
    }
    return counts;
  }

  function rateLimitState(now = Date.now(), timing = readTiming()) {
    const history = normalizeBlockHistory(timing.history, now);
    let nextRunAt = 0;
    let reason = '';

    const lastBlockAt = history[history.length - 1] || 0;
    if (lastBlockAt > 0) {
      const gapUnlockAt = lastBlockAt + MIN_BLOCK_GAP_MS + RATE_LIMIT_GRACE_MS;
      if (gapUnlockAt > nextRunAt) {
        nextRunAt = gapUnlockAt;
        reason = '相邻屏蔽间隔 3 分钟';
      }
    }

    for (const rule of RATE_LIMITS) {
      const recent = history.filter(ts => ts > now - rule.windowMs);
      if (recent.length < rule.limit) continue;
      const unlockAt = recent[recent.length - rule.limit] + rule.windowMs + RATE_LIMIT_GRACE_MS;
      if (unlockAt > nextRunAt) {
        nextRunAt = unlockAt;
        reason = `${rule.label}已满 ${recent.length}/${rule.limit}`;
      }
    }

    return {
      history,
      nextRunAt,
      reason: nextRunAt > now ? reason : '可立即执行',
    };
  }

  function computeRateLimitTiming(extra = {}) {
    const now = Date.now();
    const timing = readTiming();
    const state = rateLimitState(now, timing);
    const storedNextRunAt = Number(timing.nextRunAt || 0) > now ? Math.max(0, Number(timing.nextRunAt || 0) || 0) : 0;
    const extraNextRunAt = Math.max(0, Number(extra.nextRunAt || 0) || 0);
    let nextRunAt = state.nextRunAt;
    let reason = state.reason;
    if (storedNextRunAt > nextRunAt) {
      nextRunAt = storedNextRunAt;
      reason = timing.reason || state.reason;
    }
    if (extraNextRunAt > nextRunAt) {
      nextRunAt = extraNextRunAt;
      reason = String(extra.reason || state.reason);
    }
    const next = {
      history: state.history,
      nextRunAt,
      reason: nextRunAt > now ? reason : '可立即执行',
    };
    return next;
  }

  function refreshRateLimitTiming(extra = {}) {
    const next = computeRateLimitTiming(extra);
    writeTiming(next);
    return next;
  }

  function recordSuccessfulBlock() {
    const now = Date.now();
    const timing = readTiming();
    const history = normalizeBlockHistory([...timing.history, now], now);
    const state = rateLimitState(now, { history });
    writeTiming(state);
    return state;
  }

  function formatDuration(ms) {
    const sec = Math.max(0, Math.ceil(Number(ms || 0) / 1000));
    if (sec >= 86400) {
      const days = Math.floor(sec / 86400);
      const hours = Math.floor((sec % 86400) / 3600);
      return hours ? `${days}天${hours}小时` : `${days}天`;
    }
    if (sec >= 3600) {
      const hours = Math.floor(sec / 3600);
      const min = Math.floor((sec % 3600) / 60);
      return min ? `${hours}小时${min}分钟` : `${hours}小时`;
    }
    if (sec >= 60) {
      const min = Math.floor(sec / 60);
      const rest = sec % 60;
      return rest ? `${min}分钟${rest}秒` : `${min}分钟`;
    }
    return `${sec}秒`;
  }

  function queueDelayText() {
    const timing = computeRateLimitTiming();
    const remaining = Number(timing.nextRunAt || 0) - Date.now();
    if (remaining <= 0) return '';
    return `${formatDuration(remaining)}后执行 · ${timing.reason || '队列限速'}`;
  }

  function readWorkerLock() {
    const raw = GM_getValue(WORKER_LOCK_KEY, null);
    return raw && typeof raw === 'object' ? raw : null;
  }

  function acquireWorkerLock() {
    const now = Date.now();
    const current = readWorkerLock();
    if (current?.tabId && current.tabId !== TAB_ID && Number(current.expiresAt || 0) > now) return false;
    GM_setValue(WORKER_LOCK_KEY, { tabId: TAB_ID, expiresAt: now + LOCK_TTL_MS, updatedAt: now });
    const next = readWorkerLock();
    return next?.tabId === TAB_ID;
  }

  function heartbeatWorkerLock() {
    const current = readWorkerLock();
    if (current?.tabId !== TAB_ID) return false;
    GM_setValue(WORKER_LOCK_KEY, { tabId: TAB_ID, expiresAt: Date.now() + LOCK_TTL_MS, updatedAt: Date.now() });
    return true;
  }

  function releaseWorkerLock() {
    const current = readWorkerLock();
    if (current?.tabId === TAB_ID) GM_setValue(WORKER_LOCK_KEY, { tabId: '', expiresAt: 0, updatedAt: Date.now() });
  }

  function recoverStaleRunningItems() {
    const now = Date.now();
    const queue = readQueue();
    let changed = false;
    queue.items = queue.items.map(item => {
      if (item.status !== 'blocking') return item;
      if (now - Number(item.updatedAt || 0) < STALE_RUNNING_MS) return item;
      changed = true;
      return { ...item, status: 'queued', error: '执行超时，已恢复排队', updatedAt: now };
    });
    if (changed) writeQueue(queue);
    return changed ? queue : readQueue();
  }

  function promoteDueFailedRetries(queue = readQueue()) {
    const now = Date.now();
    let changed = false;
    queue.items = queue.items.map(item => {
      if (item.status !== 'failed') return item;
      if (!item.nextRetryAt || item.nextRetryAt > now || item.retryCount > AUTO_RETRY_MAX) return item;
      changed = true;
      return {
        ...item,
        status: 'queued',
        error: '',
        nextRetryAt: 0,
        updatedAt: now,
      };
    });
    if (changed) writeQueue(queue);
    return changed ? queue : readQueue();
  }

  function nextAutoRetryDelay(queue = readQueue()) {
    const now = Date.now();
    const nextRetryAt = queue.items
      .filter(item => item.status === 'failed' && item.nextRetryAt > now && item.retryCount <= AUTO_RETRY_MAX)
      .map(item => Number(item.nextRetryAt) || 0)
      .filter(Boolean)
      .sort((a, b) => a - b)[0];
    return nextRetryAt ? Math.max(0, nextRetryAt - now) : null;
  }

  function hasQueuedOrFutureRetry(queue = readQueue()) {
    return queue.items.some(item => item.status === 'queued') || nextAutoRetryDelay(queue) !== null;
  }

  function scheduleQueueWorker(delay = 0) {
    if (workerWakeTimer) window.clearTimeout(workerWakeTimer);
    workerWakeTimer = window.setTimeout(() => {
      workerWakeTimer = null;
      maybeStartQueueWorker();
    }, Math.max(0, Number(delay) || 0));
  }

  function maybeStartQueueWorker() {
    if (workerActive) return;
    const queue = promoteDueFailedRetries(recoverStaleRunningItems());
    if (!queue.items.some(item => item.status === 'queued')) {
      const retryDelay = nextAutoRetryDelay(queue);
      if (retryDelay !== null) {
        renderPanel(queue);
        scheduleQueueWorker(Math.min(retryDelay, 60 * 1000));
      }
      return;
    }
    if (!acquireWorkerLock()) {
      scheduleQueueWorker(2000);
      return;
    }
    runQueueWorker();
  }

  async function waitForTurnOrQueueEmpty() {
    while (true) {
      if (!heartbeatWorkerLock()) return false;
      const queue = readQueue();
      if (!queue.items.some(item => item.status === 'queued')) return false;
      const remaining = Number(computeRateLimitTiming().nextRunAt || 0) - Date.now();
      if (remaining <= 0) return true;
      renderPanel(queue);
      await sleep(Math.min(5000, remaining));
    }
  }

  async function runQueueWorker() {
    workerActive = true;
    try {
      while (true) {
        if (!heartbeatWorkerLock()) break;
        const ready = await waitForTurnOrQueueEmpty();
        if (!ready) break;

        const queue = readQueue();
        const next = queue.items.find(item => item.status === 'queued');
        if (!next) break;

        busyHandles.add(next.key);
        upsertQueueItem(next.handle, { displayName: next.displayName, avatarUrl: next.avatarUrl, comment: next.comment, status: 'blocking', error: '' });
        setButtonsForHandle(next.handle, 'blocking');

        try {
          await blockUser(next.handle);
          if (cancelRequestedHandles.has(next.key) || !getQueueItem(next.key)) {
            try { await unblockUser(next.handle); } catch (_) {}
            cancelRequestedHandles.delete(next.key);
            clearQueuedHiddenArticles(next.handle);
            clearArticlesBlocked(next.handle);
            setButtonsForHandle(next.handle, 'idle');
            continue;
          }
          recordSuccessfulBlock();
          upsertQueueItem(next.handle, { displayName: next.displayName, avatarUrl: next.avatarUrl, comment: next.comment, status: 'blocked', error: '' });
          markArticlesBlocked(next.handle);
          toast(`已屏蔽 @${next.handle}`);
        } catch (err) {
          if (cancelRequestedHandles.has(next.key) || !getQueueItem(next.key)) {
            cancelRequestedHandles.delete(next.key);
            clearQueuedHiddenArticles(next.handle);
            setButtonsForHandle(next.handle, 'idle');
            continue;
          }
          const reason = cleanErrorText(err?.message || err || '未知错误');
          if (isUserNotFoundError(reason)) {
            removeQueueItem(next.key);
            clearQueuedHiddenArticles(next.handle);
            clearArticlesBlocked(next.handle);
            setButtonsForHandle(next.handle, 'idle');
            toast(`@${next.handle} 不存在，已从队列删除`);
            continue;
          }
          refreshRateLimitTiming({ nextRunAt: Date.now() + FAILURE_COOLDOWN_MS, reason: '失败后暂停 15 秒' });
          const retryCount = Number(next.retryCount || 0) + 1;
          const canAutoRetry = !isAuthError(reason) && retryCount <= AUTO_RETRY_MAX;
          const nextRetryAt = canAutoRetry ? Date.now() + autoRetryDelayMs(retryCount) : 0;
          upsertQueueItem(next.handle, {
            displayName: next.displayName,
            avatarUrl: next.avatarUrl,
            comment: next.comment,
            status: 'failed',
            error: reason,
            retryCount,
            nextRetryAt,
          });
          clearQueuedHiddenArticles(next.handle);
          setButtonsForHandle(next.handle, 'idle');
          toast(`屏蔽 @${next.handle} 失败：${reason}`, true);
          if (isAuthError(reason)) break;
        } finally {
          busyHandles.delete(next.key);
        }
      }
    } finally {
      workerActive = false;
      releaseWorkerLock();
      const queue = readQueue();
      renderPanel(queue);
      setTimeout(() => {
        if (hasQueuedOrFutureRetry(readQueue())) maybeStartQueueWorker();
      }, 1200);
    }
  }

  function statusText(status) {
    if (status === 'queued') return '排队中';
    if (status === 'blocking') return '屏蔽中';
    if (status === 'blocked') return '已屏蔽';
    if (status === 'unblocking') return '撤销中';
    if (status === 'unblocked') return '已撤销';
    if (status === 'failed') return '失败';
    return status || '';
  }

  function shortTime(ts) {
    try {
      return new Date(Number(ts || Date.now())).toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });
    } catch (_) {
      return '';
    }
  }

  function panelStoredSize() {
    const raw = GM_getValue(PANEL_SIZE_KEY, null);
    const defaultHeight = Math.max(260, Math.min(520, window.innerHeight - 72));
    const width = Math.max(260, Math.min(window.innerWidth - 16, Number(raw?.width || 286) || 286));
    const height = Math.max(260, Math.min(window.innerHeight - 24, Number(raw?.height || defaultHeight) || defaultHeight));
    return { width, height };
  }

  function panelStoredPosition(size = panelStoredSize()) {
    const raw = GM_getValue(PANEL_POS_KEY, null);
    const defaultLeft = Math.max(8, window.innerWidth - size.width - 12);
    const defaultTop = 56;
    const left = Math.max(8, Math.min(window.innerWidth - 52, Number(raw?.left ?? defaultLeft)));
    const top = Math.max(8, Math.min(window.innerHeight - 52, Number(raw?.top ?? defaultTop)));
    return { left, top };
  }

  function applyPanelGeometry(panel) {
    if (!panel) return;
    const size = panelStoredSize();
    const pos = panelStoredPosition(size);
    panel.style.left = `${pos.left}px`;
    panel.style.top = `${pos.top}px`;
    panel.style.right = 'auto';
    panel.style.width = `${size.width}px`;
    if (size.height) panel.style.height = `${size.height}px`;
    else panel.style.removeProperty('height');
  }

  function savePanelPosition(panel) {
    const rect = panel.getBoundingClientRect();
    GM_setValue(PANEL_POS_KEY, {
      left: Math.round(Math.max(8, Math.min(window.innerWidth - 52, rect.left))),
      top: Math.round(Math.max(8, Math.min(window.innerHeight - 52, rect.top))),
    });
  }

  function savePanelSize(panel) {
    const rect = panel.getBoundingClientRect();
    GM_setValue(PANEL_SIZE_KEY, {
      width: Math.round(Math.max(260, Math.min(window.innerWidth - 16, rect.width))),
      height: Math.round(Math.max(220, Math.min(window.innerHeight - 24, rect.height))),
    });
  }

  function ensureStyles() {
    if (document.getElementById(`${SCRIPT_ID}-style`)) return;
    const style = document.createElement('style');
    style.id = `${SCRIPT_ID}-style`;
    style.textContent = `
      .xqb-btn {
        display: inline-flex !important;
        align-items: center !important;
        justify-content: center !important;
        width: 18px !important;
        height: 18px !important;
        margin: 0 !important;
        padding: 0 !important;
        border: 1.5px solid #f4212e !important;
        border-radius: 999px !important;
        background: rgba(244, 33, 46, .08) !important;
        color: #f4212e !important;
        font: 800 10px/1 system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif !important;
        cursor: pointer !important;
        box-sizing: border-box !important;
        flex: 0 0 auto !important;
        z-index: 20 !important;
        transition: transform .12s ease, opacity .12s ease, background .12s ease !important;
      }
      .xqb-btn:hover { transform: scale(1.12) !important; background: rgba(244, 33, 46, .16) !important; }
      .xqb-btn[data-xqb-state="blocking"],
      .xqb-btn[data-xqb-state="unblocking"] { opacity: .45 !important; cursor: wait !important; }
      .xqb-btn[data-xqb-state="blocked"] { border-color: #536471 !important; color: #536471 !important; background: rgba(83, 100, 113, .12) !important; }
      article[data-xqb-local-hidden="1"],
      article[data-xqb-blocked="1"] { display: none !important; }
      article[data-xqb-blocked="1"] [data-testid="User-Name"] a { text-decoration: line-through !important; }
      #xqb-panel, #xqb-panel * { box-sizing: border-box; }
      #xqb-panel {
        position: fixed;
        top: 56px;
        right: 12px;
        z-index: 2147483646;
        width: 286px;
        min-width: 260px;
        min-height: 220px;
        max-width: calc(100vw - 24px);
        max-height: calc(100vh - 16px);
        color: #0f1419;
        background: rgba(255,255,255,.98);
        border: 1px solid rgba(15,20,25,.14);
        border-radius: 8px;
        box-shadow: 0 10px 34px rgba(0,0,0,.16);
        font-family: system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
        overflow: hidden;
        display: flex;
        flex-direction: column;
      }
      #xqb-panel[data-collapsed="1"] {
        width: 38px !important;
        height: 38px !important;
        min-width: 38px !important;
        min-height: 38px !important;
        border-radius: 999px;
        overflow: hidden;
      }
      #xqb-panel button {
        font: inherit;
        border-radius: 7px;
        cursor: pointer;
      }
      .xqb-head {
        display: flex;
        align-items: center;
        gap: 6px;
        padding: 8px;
        border-bottom: 1px solid rgba(15,20,25,.1);
        background: #fff;
        cursor: move;
        user-select: none;
      }
      .xqb-title {
        flex: 1;
        min-width: 0;
        font-size: 12px;
        font-weight: 900;
        white-space: nowrap;
        overflow: hidden;
        text-overflow: ellipsis;
      }
      .xqb-icon-btn {
        width: 26px;
        height: 24px;
        padding: 0;
        border: 1px solid rgba(15,20,25,.16);
        background: #fff;
        color: #536471;
        font-size: 13px;
        font-weight: 900;
        line-height: 1;
        display: inline-flex;
        align-items: center;
        justify-content: center;
        text-align: center;
      }
      .xqb-icon-btn:disabled {
        opacity: .42;
        cursor: default;
      }
      .xqb-body {
        flex: 1;
        min-height: 0;
        overflow: auto;
        padding: 6px;
      }
      .xqb-resizer {
        position: absolute;
        right: 0;
        bottom: 0;
        width: 16px;
        height: 16px;
        cursor: nwse-resize;
        background: linear-gradient(135deg, transparent 48%, rgba(83,100,113,.45) 50%, rgba(83,100,113,.45) 58%, transparent 60%);
      }
      .xqb-status-line {
        margin: 0 0 6px;
        padding: 6px 7px;
        border-radius: 7px;
        background: rgba(244,33,46,.07);
        color: #f4212e;
        font-size: 11px;
        line-height: 1.3;
        font-weight: 800;
      }
      .xqb-empty {
        padding: 14px 8px;
        color: #536471;
        text-align: center;
        font-size: 12px;
      }
      .xqb-row {
        display: grid;
        grid-template-columns: 34px minmax(0, 1fr) auto;
        gap: 6px;
        align-items: center;
        padding: 7px;
        border-radius: 8px;
        border: 1px solid rgba(15,20,25,.08);
        background: #fff;
        margin-bottom: 6px;
      }
      .xqb-section-title {
        margin: 8px 2px 5px;
        color: #536471;
        font-size: 11px;
        line-height: 1.2;
        font-weight: 900;
      }
      .xqb-avatar {
        width: 34px;
        height: 34px;
        border-radius: 999px;
        overflow: hidden;
        background: rgba(83,100,113,.14);
        color: #536471;
        display: flex;
        align-items: center;
        justify-content: center;
        font-size: 13px;
        font-weight: 900;
      }
      .xqb-avatar img {
        width: 100%;
        height: 100%;
        display: block;
        object-fit: cover;
      }
      .xqb-person { min-width: 0; }
      .xqb-name {
        font-size: 12px;
        line-height: 1.25;
        font-weight: 800;
        overflow: hidden;
        text-overflow: ellipsis;
        white-space: nowrap;
      }
      .xqb-comment {
        margin-top: 3px;
        color: #0f1419;
        font-size: 11px;
        line-height: 1.32;
        display: -webkit-box;
        -webkit-line-clamp: 2;
        -webkit-box-orient: vertical;
        overflow: hidden;
        word-break: break-word;
      }
      .xqb-error {
        margin-top: 4px;
        color: #f4212e;
        font-size: 11px;
        line-height: 1.32;
        display: -webkit-box;
        -webkit-line-clamp: 2;
        -webkit-box-orient: vertical;
        overflow: hidden;
        word-break: break-word;
      }
      .xqb-meta {
        margin-top: 2px;
        color: #536471;
        font-size: 11px;
        line-height: 1.25;
        overflow: hidden;
        text-overflow: ellipsis;
        white-space: nowrap;
      }
      .xqb-actions {
        display: flex;
        flex-direction: column;
        gap: 4px;
        align-items: stretch;
      }
      .xqb-action {
        min-width: 46px;
        border: 1px solid rgba(15,20,25,.16);
        background: #fff;
        color: #0f1419;
        padding: 4px 7px;
        font-size: 11px;
        font-weight: 800;
        white-space: nowrap;
      }
      .xqb-action[data-kind="danger"] { border-color: rgba(244,33,46,.45); color: #f4212e; }
      .xqb-action:disabled { opacity: .45; cursor: wait; }
      #xqb-panel[data-collapsed="1"] .xqb-title,
      #xqb-panel[data-collapsed="1"] .xqb-body,
      #xqb-panel[data-collapsed="1"] .xqb-clear,
      #xqb-panel[data-collapsed="1"] .xqb-retry-all,
      #xqb-panel[data-collapsed="1"] .xqb-resizer { display: none !important; }
      #xqb-panel[data-collapsed="1"] .xqb-head {
        width: 38px;
        height: 38px;
        justify-content: center;
        padding: 0;
        border-bottom: 0;
        cursor: pointer;
      }
      #xqb-panel[data-collapsed="1"] .xqb-icon-btn {
        width: 38px;
        height: 38px;
        padding: 0;
        border: 0;
        border-radius: 999px;
        background: #fff;
        color: #f4212e;
        font-size: 15px;
        line-height: 1;
        display: inline-flex;
        align-items: center;
        justify-content: center;
      }
    `;
    (document.head || document.documentElement).appendChild(style);
  }

  function ensurePanel() {
    ensureStyles();
    let panel = document.getElementById(`${SCRIPT_ID}-panel`);
    if (panel) return panel;
    panel = document.createElement('div');
    panel.id = `${SCRIPT_ID}-panel`;
    panel.addEventListener('click', onPanelClick);
    mountRoot().appendChild(panel);
    applyPanelGeometry(panel);
    return panel;
  }

  function makePanelDraggable(panel, handle) {
    handle.onpointerdown = event => {
      const collapsed = panel.dataset.collapsed === '1';
      if (event.button !== 0 || (!collapsed && event.target.closest('button'))) return;
      event.preventDefault();
      const rect = panel.getBoundingClientRect();
      const startX = event.clientX;
      const startY = event.clientY;
      const startLeft = rect.left;
      const startTop = rect.top;
      let moved = false;
      const maxLeft = () => Math.max(8, window.innerWidth - 52);
      const maxTop = () => Math.max(8, window.innerHeight - 52);
      const move = ev => {
        const dx = ev.clientX - startX;
        const dy = ev.clientY - startY;
        if (Math.abs(dx) + Math.abs(dy) > 4) moved = true;
        const left = Math.max(8, Math.min(maxLeft(), startLeft + dx));
        const top = Math.max(8, Math.min(maxTop(), startTop + dy));
        panel.style.left = `${Math.round(left)}px`;
        panel.style.top = `${Math.round(top)}px`;
        panel.style.right = 'auto';
      };
      const up = () => {
        document.removeEventListener('pointermove', move, true);
        document.removeEventListener('pointerup', up, true);
        savePanelPosition(panel);
        if (collapsed && moved) collapsedPanelDraggedAt = Date.now();
      };
      document.addEventListener('pointermove', move, true);
      document.addEventListener('pointerup', up, true);
    };
  }

  function makePanelResizable(panel, grip) {
    grip.onpointerdown = event => {
      if (event.button !== 0) return;
      event.preventDefault();
      event.stopPropagation();
      const rect = panel.getBoundingClientRect();
      const startX = event.clientX;
      const startY = event.clientY;
      const startWidth = rect.width;
      const startHeight = rect.height;
      const move = ev => {
        const width = Math.max(260, Math.min(window.innerWidth - rect.left - 8, startWidth + ev.clientX - startX));
        const height = Math.max(220, Math.min(window.innerHeight - rect.top - 8, startHeight + ev.clientY - startY));
        panel.style.width = `${Math.round(width)}px`;
        panel.style.height = `${Math.round(height)}px`;
      };
      const up = () => {
        document.removeEventListener('pointermove', move, true);
        document.removeEventListener('pointerup', up, true);
        savePanelSize(panel);
        savePanelPosition(panel);
      };
      document.addEventListener('pointermove', move, true);
      document.addEventListener('pointerup', up, true);
    };
  }

  function makeAvatarNode(item) {
    const avatar = document.createElement('div');
    avatar.className = 'xqb-avatar';
    const src = String(item.avatarUrl || '').trim();
    if (src) {
      const img = document.createElement('img');
      img.src = src;
      img.alt = '';
      img.referrerPolicy = 'no-referrer';
      avatar.appendChild(img);
    } else {
      avatar.textContent = (item.displayName || item.handle || '?').slice(0, 1).toUpperCase();
    }
    return avatar;
  }

  function queueSectionItems(queue, section) {
    if (section === 'pending') {
      return queue.items.filter(item => ['queued', 'blocking', 'failed'].includes(item.status));
    }
    if (section === 'blocked') {
      return queue.items.filter(item => ['blocked', 'unblocking'].includes(item.status));
    }
    return [];
  }

  function renderQueueItem(body, item) {
    const row = document.createElement('div');
    row.className = 'xqb-row';
    row.dataset.key = item.key;
    row.dataset.status = item.status;

    const person = document.createElement('div');
    person.className = 'xqb-person';
    const name = document.createElement('div');
    name.className = 'xqb-name';
    name.textContent = `${item.displayName || item.handle || item.key} · @${item.handle}`;
    const meta = document.createElement('div');
    meta.className = 'xqb-meta';
    const bits = [statusText(item.status), shortTime(item.updatedAt)];
    if (item.status === 'failed' && item.nextRetryAt && item.retryCount <= AUTO_RETRY_MAX) {
      const remaining = Number(item.nextRetryAt || 0) - Date.now();
      bits.push(remaining > 0 ? `自动重试 ${item.retryCount}/${AUTO_RETRY_MAX} · ${formatDuration(remaining)}后` : `自动重试 ${item.retryCount}/${AUTO_RETRY_MAX} · 即将执行`);
    } else if (item.status === 'failed' && item.retryCount > AUTO_RETRY_MAX) {
      bits.push('自动重试已停止');
    } else if (item.status === 'failed' && item.retryCount > 0) {
      bits.push('需手动重试');
    }
    meta.textContent = bits.filter(Boolean).join(' · ');
    meta.title = meta.textContent;
    const comment = document.createElement('div');
    comment.className = 'xqb-comment';
    comment.textContent = item.comment || '未抓取到评论文本';
    comment.title = item.comment || '';
    person.append(name, meta, comment);
    if (item.status === 'failed' && item.error) {
      const error = document.createElement('div');
      error.className = 'xqb-error';
      error.textContent = `失败原因：${item.error}`;
      error.title = item.error;
      person.appendChild(error);
    }

    const actions = document.createElement('div');
    actions.className = 'xqb-actions';

    if (item.status === 'queued' || item.status === 'blocking') {
      actions.appendChild(actionButton('cancel', '撤回', 'danger', item.key, false, `撤回 @${item.handle}`));
    } else if (item.status === 'blocked') {
      actions.appendChild(actionButton('undo', '撤回', 'danger', item.key, false, `取消屏蔽 @${item.handle}`));
    } else if (item.status === 'unblocking') {
      actions.appendChild(actionButton('noop', '撤回中', '', item.key, true, `正在取消屏蔽 @${item.handle}`));
    } else if (item.status === 'failed') {
      actions.appendChild(actionButton('retry', '重试', 'danger', item.key, false, `重试屏蔽 @${item.handle}`));
      actions.appendChild(actionButton('remove', '移除', '', item.key, false, `移除 @${item.handle} 的失败记录`));
    }

    row.append(makeAvatarNode(item), person, actions);
    body.appendChild(row);
  }

  function renderQueueSection(body, title, items) {
    const sectionTitle = document.createElement('div');
    sectionTitle.className = 'xqb-section-title';
    sectionTitle.textContent = `${title} ${items.length}`;
    body.appendChild(sectionTitle);
    if (!items.length) {
      const empty = document.createElement('div');
      empty.className = 'xqb-empty';
      empty.textContent = '暂无用户';
      body.appendChild(empty);
      return;
    }
    items.forEach(item => renderQueueItem(body, item));
  }

  function queueItemSignature(item) {
    return [
      item.key,
      item.handle,
      item.displayName,
      item.avatarUrl,
      item.comment,
      item.status,
      item.updatedAt,
      item.error,
      item.retryCount,
      item.nextRetryAt,
    ].map(value => String(value ?? '').replace(/[\u001e\u001f]/g, ' ')).join('\u001f');
  }

  function queueListSignature(queue) {
    const pendingItems = queueSectionItems(queue, 'pending');
    const blockedItems = queueSectionItems(queue, 'blocked');
    return [
      'pending',
      pendingItems.map(queueItemSignature).join('\u001e'),
      'blocked',
      blockedItems.map(queueItemSignature).join('\u001e'),
    ].join('\u001e');
  }

  function setPanelStatusLine(body, activeCount) {
    const text = activeCount ? queueDelayText() : '';
    let status = Array.from(body.children).find(child => child.classList?.contains('xqb-status-line'));
    if (!text) {
      if (status) status.remove();
      return;
    }
    if (!status) {
      status = document.createElement('div');
      status.className = 'xqb-status-line';
      body.insertBefore(status, body.firstChild);
    }
    status.textContent = text;
  }

  function renderPanel(queue = readQueue()) {
    if (!document.documentElement) return;
    const panel = ensurePanel();
    const collapsed = !!GM_getValue(PANEL_COLLAPSED_KEY, false);
    const counts = queueCounts(queue);
    const activeCount = counts.queued + counts.blocking;
    const wasCollapsed = panel.dataset.collapsed === '1';
    const previousBody = panel.querySelector('.xqb-body');
    const previousScrollTop = previousBody?.scrollTop || 0;
    const signature = queueListSignature(queue);
    panel.dataset.collapsed = collapsed ? '1' : '0';
    applyPanelGeometry(panel);
    if (collapsed) {
      panel.style.width = '38px';
      panel.style.height = '38px';
    }

    if (!collapsed && !wasCollapsed && previousBody && panel.dataset.queueSignature === signature) {
      const title = document.getElementById(`${SCRIPT_ID}-panel-title`);
      if (title) title.textContent = panelTitleText(counts);
      setPanelStatusLine(previousBody, activeCount);
      return;
    }

    panel.replaceChildren();
    panel.dataset.queueSignature = signature;

    const head = document.createElement('div');
    head.className = 'xqb-head';
    const title = document.createElement('div');
    title.id = `${SCRIPT_ID}-panel-title`;
    title.className = 'xqb-title';
    title.textContent = panelTitleText(counts);
    const clear = document.createElement('button');
    clear.type = 'button';
    clear.className = 'xqb-icon-btn xqb-clear';
    clear.dataset.action = 'clear';
    clear.title = '清理已撤销和失败记录';
    clear.textContent = '清';
    const retryAll = document.createElement('button');
    retryAll.type = 'button';
    retryAll.className = 'xqb-icon-btn xqb-retry-all';
    retryAll.dataset.action = 'retry-all';
    retryAll.title = counts.failed ? `一键重试 ${counts.failed} 个失败项` : '暂无失败项可重试';
    retryAll.textContent = '重';
    retryAll.disabled = !counts.failed;
    const collapse = document.createElement('button');
    collapse.type = 'button';
    collapse.className = 'xqb-icon-btn';
    collapse.dataset.action = 'collapse';
    collapse.title = collapsed ? '展开快捷屏蔽队列' : '收起快捷屏蔽队列';
    collapse.textContent = collapsed ? '禁' : '-';
    if (collapsed) head.appendChild(collapse);
    else head.append(title, retryAll, clear, collapse);
    panel.appendChild(head);
    makePanelDraggable(panel, head);

    if (collapsed) return;

    const body = document.createElement('div');
    body.className = 'xqb-body';
    body.dataset.queueSignature = signature;
    setPanelStatusLine(body, activeCount);

    const pendingItems = queueSectionItems(queue, 'pending');
    const blockedItems = queueSectionItems(queue, 'blocked');
    renderQueueSection(body, '待屏蔽 / 屏蔽中', pendingItems);
    renderQueueSection(body, '已屏蔽', blockedItems);

    panel.appendChild(body);
    body.scrollTop = Math.min(previousScrollTop, Math.max(0, body.scrollHeight - body.clientHeight));
    requestAnimationFrame(() => {
      body.scrollTop = Math.min(previousScrollTop, Math.max(0, body.scrollHeight - body.clientHeight));
    });
    const resizer = document.createElement('div');
    resizer.className = 'xqb-resizer';
    resizer.title = '拖动调整大小';
    panel.appendChild(resizer);
    makePanelResizable(panel, resizer);
  }

  function panelTitleText(counts = queueCounts()) {
    return `快捷屏蔽 排${counts.queued + counts.blocking} · 已${counts.blocked + counts.unblocking} · 文${lastScanStats.candidates}/钮${lastScanStats.buttons}`;
  }

  function updatePanelTitle() {
    const title = document.getElementById(`${SCRIPT_ID}-panel-title`);
    if (title) title.textContent = panelTitleText();
  }

  function actionButton(action, label, kind, key, disabled, title) {
    const btn = document.createElement('button');
    btn.type = 'button';
    btn.className = 'xqb-action';
    btn.dataset.action = action;
    btn.dataset.key = key;
    if (kind) btn.dataset.kind = kind;
    btn.disabled = !!disabled;
    btn.title = title || label;
    btn.textContent = label;
    return btn;
  }

  function syncRetriedHandle(handle) {
    setButtonsForHandle(handle, 'queued');
    tweetArticles().forEach(article => {
      if (articleHasHandle(article, handle)) syncArticleQueueState(article, handle);
    });
  }

  function retryFailedItem(item, resetRetry = true) {
    if (!item || item.status !== 'failed') return false;
    upsertQueueItem(item.handle, {
      displayName: item.displayName,
      avatarUrl: item.avatarUrl,
      comment: item.comment,
      status: 'queued',
      error: '',
      retryCount: resetRetry ? 0 : item.retryCount,
      nextRetryAt: 0,
    });
    syncRetriedHandle(item.handle);
    maybeStartQueueWorker();
    return true;
  }

  function retryAllFailedItems() {
    const queue = readQueue();
    const now = Date.now();
    const handles = [];
    queue.items = queue.items.map(item => {
      if (item.status !== 'failed') return item;
      handles.push(item.handle);
      return {
        ...item,
        status: 'queued',
        error: '',
        retryCount: 0,
        nextRetryAt: 0,
        updatedAt: now,
      };
    });
    if (!handles.length) {
      toast('暂无失败项可重试');
      return;
    }
    writeQueue(queue);
    handles.forEach(syncRetriedHandle);
    maybeStartQueueWorker();
    toast(`已重新加入 ${handles.length} 个失败项`);
  }

  async function onPanelClick(event) {
    const panel = event.target.closest(`#${SCRIPT_ID}-panel`);
    if (panel?.dataset.collapsed === '1') {
      if (Date.now() - collapsedPanelDraggedAt < 250) return;
      event.preventDefault();
      event.stopPropagation();
      GM_setValue(PANEL_COLLAPSED_KEY, false);
      renderPanel();
      return;
    }
    const btn = event.target.closest('button[data-action]');
    if (!btn) return;
    event.preventDefault();
    event.stopPropagation();

    const action = btn.dataset.action;
    if (action === 'collapse') {
      GM_setValue(PANEL_COLLAPSED_KEY, !GM_getValue(PANEL_COLLAPSED_KEY, false));
      renderPanel();
      return;
    }
    if (action === 'clear') {
      const queue = readQueue();
      queue.items = queue.items.filter(item => ['queued', 'blocking', 'blocked', 'unblocking'].includes(item.status));
      writeQueue(queue);
      maybeStartQueueWorker();
      return;
    }
    if (action === 'retry-all') {
      retryAllFailedItems();
      return;
    }

    const key = btn.dataset.key;
    const item = getQueueItem(key);
    if (!item) return;
    if (action === 'remove' || action === 'cancel') {
      if (action === 'cancel') {
        cancelQueueItem(item);
      } else {
        removeQueueItem(key);
      }
      return;
    }
    if (action === 'retry') {
      retryFailedItem(item, true);
      return;
    }
    if (action === 'undo') {
      await undoBlock(item);
    }
  }

  function cancelQueueItem(item) {
    const key = normalizeHandle(item?.handle || item?.key);
    if (!key) return;
    if (item.status === 'blocking') {
      cancelRequestedHandles.add(key);
      try { inFlightBlockRequests.get(key)?.abort?.(); } catch (_) {}
    }
    removeQueueItem(key);
    clearQueuedHiddenArticles(item.handle);
    clearArticlesBlocked(item.handle);
    setButtonsForHandle(item.handle, 'idle');
    toast(`已撤回 @${item.handle}`);
  }

  function setButtonState(btn, state) {
    btn.dataset.xqbState = state;
    if (state === 'queued') {
      btn.textContent = '等';
      btn.disabled = false;
      btn.title = '已加入屏蔽队列，可在页面边缘队列中取消';
    } else if (state === 'blocking') {
      btn.textContent = '...';
      btn.disabled = true;
      btn.title = '正在屏蔽';
    } else if (state === 'blocked') {
      btn.textContent = BLOCKED_TEXT;
      btn.disabled = false;
      btn.title = '已屏蔽，可在页面边缘队列中撤销';
    } else {
      btn.textContent = BUTTON_TEXT;
      btn.disabled = false;
      btn.title = btn.dataset.xqbTitle || '快捷屏蔽该用户';
    }
  }

  function setButtonsForHandle(handle, state) {
    const key = normalizeHandle(handle);
    if (!key) return;
    document.querySelectorAll('.xqb-btn[data-xqb-handle]').forEach(btn => {
      if (normalizeHandle(btn.dataset.xqbHandle) === key) setButtonState(btn, state);
    });
  }

  function handleFromHref(href) {
    try {
      const path = new URL(href, location.href).pathname.split('/').filter(Boolean);
      const first = path[0] || '';
      if (!/^[A-Za-z0-9_]{1,15}$/.test(first)) return '';
      if (['i', 'search', 'home', 'explore', 'notifications', 'messages', 'settings'].includes(first.toLowerCase())) return '';
      return displayHandle(first);
    } catch (_) {
      const m = String(href || '').match(/(?:^|https?:\/\/(?:mobile\.)?(?:x|twitter)\.com\/)([A-Za-z0-9_]{1,15})(?:$|[/?#])/);
      if (!m || ['i', 'search', 'home', 'explore', 'notifications', 'messages', 'settings'].includes(m[1].toLowerCase())) return '';
      return displayHandle(m[1]);
    }
  }

  function extractHandleFromArticle(article) {
    const nameEl = article.querySelector('[data-testid="User-Name"]');
    if (nameEl) {
      for (const span of nameEl.querySelectorAll('span')) {
        const txt = textOf(span);
        if (txt.startsWith('@') && txt.length > 1 && !txt.includes(' ')) return displayHandle(txt.slice(1));
      }
      for (const link of nameEl.querySelectorAll('a[href]')) {
        const handle = handleFromHref(link.getAttribute('href') || link.href || '');
        if (handle) return handle;
      }
    }
    for (const link of article.querySelectorAll('a[href]')) {
      const handle = handleFromHref(link.getAttribute('href') || link.href || '');
      if (handle) return handle;
    }
    return '';
  }

  function extractDisplayNameFromArticle(article, handle) {
    const nameEl = article.querySelector('[data-testid="User-Name"]');
    if (!nameEl) return '';
    for (const link of nameEl.querySelectorAll('a')) {
      const txt = textOf(link);
      if (txt && !txt.includes(`@${handle}`)) {
        const first = txt.split(`@${handle}`)[0].trim();
        if (first) return first.slice(0, 80);
      }
    }
    for (const span of nameEl.querySelectorAll('span')) {
      const txt = textOf(span);
      if (txt && !txt.startsWith('@') && txt !== handle) return txt.slice(0, 80);
    }
    return '';
  }

  function extractAvatarFromArticle(article) {
    const img = article.querySelector('[data-testid^="UserAvatar-Container"] img[src], img[src*="profile_images"]');
    return String(img?.src || '').slice(0, 500);
  }

  function cleanCommentText(value) {
    return String(value || '').replace(/\s+/g, ' ').trim();
  }

  function isUsableCommentText(value, handle = '', displayName = '') {
    const text = cleanCommentText(value);
    if (!text) return false;
    if (text.length < 2) return false;
    const lower = text.toLowerCase();
    const key = normalizeHandle(handle);
    if (key && lower === `@${key}`) return false;
    if (displayName && lower === cleanCommentText(displayName).toLowerCase()) return false;
    if (/^(reply|repost|like|view|share|回复|转帖|喜欢|查看|分享|广告)$/i.test(text)) return false;
    return true;
  }

  function bestCommentCandidate(candidates, handle = '', displayName = '') {
    const seen = new Set();
    const usable = [];
    for (const raw of candidates) {
      const text = cleanCommentText(raw);
      const norm = text.toLowerCase();
      if (!isUsableCommentText(text, handle, displayName) || seen.has(norm)) continue;
      seen.add(norm);
      usable.push(text);
    }
    usable.sort((a, b) => b.length - a.length);
    return (usable[0] || '').slice(0, 280);
  }

  function extractCommentFromArticle(article, handle = '', displayName = '') {
    const candidates = [];
    const textEl = article.querySelector('[data-testid="tweetText"]');
    if (textEl) candidates.push(textOf(textEl));

    article.querySelectorAll('[lang]').forEach(node => {
      if (node.closest('[data-testid="User-Name"], [role="button"]')) return;
      candidates.push(textOf(node));
    });

    article.querySelectorAll('div[dir="auto"], span[dir="auto"]').forEach(node => {
      if (node.closest('[data-testid="User-Name"], [role="button"]')) return;
      if (node.closest('time')) return;
      candidates.push(textOf(node));
    });

    const rawLines = String(article.innerText || article.textContent || '')
      .split(/\n+/)
      .map(cleanCommentText)
      .filter(Boolean);
    candidates.push(...rawLines);

    return bestCommentCandidate(candidates, handle, displayName) || '无文本评论或媒体回复';
  }

  function queuePatchFromArticle(article, handle, displayName = '') {
    const name = displayName || extractDisplayNameFromArticle(article, handle);
    return {
      displayName: name,
      avatarUrl: extractAvatarFromArticle(article),
      comment: extractCommentFromArticle(article, handle, name),
    };
  }

  function isStatusPage() {
    return /\/status\/\d+/.test(location.pathname);
  }

  function isLikelyMainStatusArticle(article) {
    if (!isStatusPage()) return false;
    const first = document.querySelector('main article[data-testid="tweet"], main article[role="article"]');
    return first === article;
  }

  function tweetArticles() {
    return Array.from(document.querySelectorAll('article[data-testid="tweet"], article[role="article"], [data-testid="cellInnerDiv"] article'))
      .filter((article, index, arr) => article && arr.indexOf(article) === index);
  }

  function findActionAnchor(article) {
    const node = article.querySelector('[data-testid="caret"], button[aria-label="More"], button[aria-label="更多"], div[aria-label="More"][role="button"], div[aria-label="更多"][role="button"]');
    return node?.closest?.('button,[role="button"]') || node;
  }

  function injectButtons() {
    if (!document.body) return;
    ensureStyles();

    const articles = tweetArticles();
    let handles = 0;
    articles.forEach(article => {
      if (article.querySelector('.xqb-btn')) return;
      if (isLikelyMainStatusArticle(article)) return;

      const handle = extractHandleFromArticle(article);
      if (!handle) return;
      handles += 1;
      article.dataset.xqbButtoned = '1';
      const key = normalizeHandle(handle);
      const displayName = extractDisplayNameFromArticle(article, handle);

      const btn = document.createElement('button');
      btn.type = 'button';
      btn.className = 'xqb-btn';
      btn.dataset.xqbHandle = handle;
      btn.dataset.xqbDisplayName = displayName;
      btn.dataset.xqbTitle = `快捷屏蔽 @${handle}`;
      btn.setAttribute('aria-label', `快捷屏蔽 @${handle}`);

      const item = getQueueItem(key);
      setButtonState(btn, isHiddenQueueStatus(item?.status) ? item.status : 'idle');

      btn.addEventListener('click', event => {
        event.preventDefault();
        event.stopPropagation();
        const current = getQueueItem(key);
        if (['queued', 'blocking', 'blocked'].includes(current?.status)) {
          renderPanel();
          toast(`@${handle} 已在快捷屏蔽队列中`);
          return;
        }
        enqueueBlock(handle, displayName, article);
      }, true);

      article.style.position = 'relative';
      Object.assign(btn.style, {
        position: 'absolute',
        top: '12px',
        right: '72px',
      });
      article.appendChild(btn);

      syncArticleQueueState(article, handle);
    });
    lastScanStats = {
      candidates: articles.length,
      handles,
      buttons: document.querySelectorAll('.xqb-btn[data-xqb-handle]').length,
    };
    updatePanelTitle();
  }

  function scheduleScan() {
    if (scanQueued) return;
    scanQueued = true;
    requestAnimationFrame(() => {
      scanQueued = false;
      injectButtons();
    });
  }

  function articleHasHandle(article, handle) {
    return normalizeHandle(extractHandleFromArticle(article)) === normalizeHandle(handle);
  }

  function isHiddenQueueStatus(status) {
    return ['queued', 'blocking', 'blocked'].includes(status || '');
  }

  function syncArticleQueueState(article, handle = extractHandleFromArticle(article)) {
    if (!article || !handle) return;
    const item = getQueueItem(handle);
    delete article.dataset.xqbBlocked;
    delete article.dataset.xqbLocalHidden;
    delete article.dataset.xqbQueued;
    delete article.dataset.xqbQueuedHandle;
    if (item?.status === 'blocked') {
      article.dataset.xqbBlocked = '1';
    } else if (['queued', 'blocking'].includes(item?.status)) {
      article.dataset.xqbQueued = '1';
      article.dataset.xqbQueuedHandle = normalizeHandle(handle);
      article.dataset.xqbLocalHidden = '1';
    }
    setButtonsForHandle(handle, isHiddenQueueStatus(item?.status) ? item.status : 'idle');
  }

  function hideQueuedArticle(handle, article) {
    if (!article) return;
    article.dataset.xqbQueued = '1';
    article.dataset.xqbQueuedHandle = normalizeHandle(handle);
    article.dataset.xqbLocalHidden = '1';
  }

  function clearQueuedHiddenArticles(handle) {
    const key = normalizeHandle(handle);
    tweetArticles().forEach(article => {
      if (article.dataset.xqbQueuedHandle === key || articleHasHandle(article, handle)) {
        delete article.dataset.xqbQueued;
        delete article.dataset.xqbQueuedHandle;
        delete article.dataset.xqbLocalHidden;
      }
    });
  }

  function markArticlesBlocked(handle) {
    tweetArticles().forEach(article => {
      if (!articleHasHandle(article, handle)) return;
      delete article.dataset.xqbQueued;
      delete article.dataset.xqbQueuedHandle;
      delete article.dataset.xqbLocalHidden;
      article.dataset.xqbBlocked = '1';
    });
    setButtonsForHandle(handle, 'blocked');
  }

  function clearArticlesBlocked(handle) {
    tweetArticles().forEach(article => {
      if (!articleHasHandle(article, handle)) return;
      delete article.dataset.xqbBlocked;
      delete article.dataset.xqbLocalHidden;
      delete article.dataset.xqbQueued;
      delete article.dataset.xqbQueuedHandle;
    });
    setButtonsForHandle(handle, 'idle');
  }

  function enqueueBlock(handle, displayName = '', sourceArticle = null) {
    const key = normalizeHandle(handle);
    if (!key) return;
    const existing = getQueueItem(key);
    if (['queued', 'blocking', 'blocked'].includes(existing?.status)) {
      renderPanel();
      toast(`@${handle} 已在快捷屏蔽队列中`);
      return;
    }

    refreshRateLimitTiming();
    const meta = sourceArticle ? queuePatchFromArticle(sourceArticle, handle, displayName) : { displayName };
    upsertQueueItem(handle, { ...meta, status: 'queued', error: '' });
    setButtonsForHandle(handle, 'queued');
    hideQueuedArticle(handle, sourceArticle);
    renderPanel();
    maybeStartQueueWorker();
    toast(`@${handle} 已加入屏蔽队列`);
  }

  async function undoBlock(item) {
    const key = normalizeHandle(item.handle);
    if (!key || busyHandles.has(key)) return;
    busyHandles.add(key);
    upsertQueueItem(item.handle, { displayName: item.displayName, status: 'unblocking', error: '' });
    setButtonsForHandle(item.handle, 'blocking');

    try {
      await unblockUser(item.handle);
      upsertQueueItem(item.handle, { displayName: item.displayName, status: 'unblocked', error: '' });
      clearArticlesBlocked(item.handle);
      toast(`已撤销屏蔽 @${item.handle}`);
    } catch (err) {
      upsertQueueItem(item.handle, { displayName: item.displayName, status: 'blocked', error: err?.message || String(err) });
      setButtonsForHandle(item.handle, 'blocked');
      toast(`撤销 @${item.handle} 失败：${err?.message || err}`, true);
    } finally {
      busyHandles.delete(key);
    }
  }

  function start() {
    ensureStyles();
    bootBadge();
    renderPanel();

    if (typeof GM_addValueChangeListener === 'function') {
      GM_addValueChangeListener(QUEUE_KEY, () => {
        renderPanel();
        tweetArticles().forEach(article => {
          const handle = extractHandleFromArticle(article);
          if (handle) syncArticleQueueState(article, handle);
        });
        maybeStartQueueWorker();
      });
      GM_addValueChangeListener(TIMING_KEY, () => {
        renderPanel();
      });
    }

    const observer = new MutationObserver(scheduleScan);
    observer.observe(document.documentElement, { childList: true, subtree: true });
    scheduleScan();
    window.setInterval(scheduleScan, 1500);
    maybeStartQueueWorker();
  }

  hookAuth();

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', start, { once: true });
  } else {
    start();
  }
})();
