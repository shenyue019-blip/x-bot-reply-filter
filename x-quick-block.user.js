// ==UserScript==
// @name         X 快捷屏蔽按钮
// @namespace    https://github.com/shenyue019-blip/x-bot-reply-filter
// @version      1.2.0
// @description  在 X/Twitter 评论区给每条回复加一个快捷屏蔽按钮，先入队再按节奏屏蔽，并在页面边缘保留可撤销队列
// @author       summeriscoming
// @license      MIT
// @match        https://x.com/*
// @match        https://twitter.com/*
// @match        https://mobile.x.com/*
// @match        https://mobile.twitter.com/*
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
  const QUEUE_KEY = 'xqb_block_queue_v1';
  const TIMING_KEY = 'xqb_queue_timing_v1';
  const WORKER_LOCK_KEY = 'xqb_queue_worker_lock_v1';
  const PANEL_COLLAPSED_KEY = 'xqb_panel_collapsed_v1';
  const MAX_QUEUE_ITEMS = 50;
  const BLOCK_GAP_MS = 15 * 1000;
  const TWENTY_COOLDOWN_EVERY = 20;
  const TWENTY_COOLDOWN_MS = 30 * 1000;
  const SIXTY_COOLDOWN_EVERY = 60;
  const SIXTY_COOLDOWN_MS = 5 * 60 * 1000;
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
  const busyHandles = new Set();
  const cancelRequestedHandles = new Set();
  const inFlightBlockRequests = new Map();

  function normalizeHandle(value) {
    const m = String(value || '').trim().replace(/^@+/, '').match(/[A-Za-z0-9_]{1,15}/);
    return m ? m[0].toLowerCase() : '';
  }

  function displayHandle(value) {
    const m = String(value || '').trim().replace(/^@+/, '').match(/[A-Za-z0-9_]{1,15}/);
    return m ? m[0] : '';
  }

  function textOf(node) {
    return String(node?.textContent || '').replace(/\s+/g, ' ').trim();
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
    document.documentElement.appendChild(el);
    window.setTimeout(() => el.remove(), 2400);
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
            reject(new Error(`HTTP ${resp.status}`));
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
        error: String(rawItem.error || '').slice(0, 160),
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
      error: String(patch.error ?? '').slice(0, 160),
    };
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
    return { version: 1, count: 0, nextRunAt: 0, reason: '' };
  }

  function readTiming() {
    const raw = GM_getValue(TIMING_KEY, emptyTiming());
    return {
      version: 1,
      count: Math.max(0, Number(raw?.count || 0) || 0),
      nextRunAt: Math.max(0, Number(raw?.nextRunAt || 0) || 0),
      reason: String(raw?.reason || '').slice(0, 80),
    };
  }

  function writeTiming(timing) {
    GM_setValue(TIMING_KEY, {
      version: 1,
      count: Math.max(0, Number(timing?.count || 0) || 0),
      nextRunAt: Math.max(0, Number(timing?.nextRunAt || 0) || 0),
      reason: String(timing?.reason || '').slice(0, 80),
    });
  }

  function queueCounts(queue = readQueue()) {
    const counts = { queued: 0, blocking: 0, blocked: 0, failed: 0, unblocking: 0, unblocked: 0 };
    for (const item of queue.items) {
      if (Object.prototype.hasOwnProperty.call(counts, item.status)) counts[item.status] += 1;
    }
    return counts;
  }

  function hasActiveQueue(queue = readQueue()) {
    return queue.items.some(item => item.status === 'queued' || item.status === 'blocking');
  }

  function nextDelayForCompletedCount(count) {
    if (count > 0 && count % SIXTY_COOLDOWN_EVERY === 0) {
      return { ms: SIXTY_COOLDOWN_MS, reason: '每 60 个冷却 5 分钟' };
    }
    if (count > 0 && count % TWENTY_COOLDOWN_EVERY === 0) {
      return { ms: TWENTY_COOLDOWN_MS, reason: '每 20 个冷却 30 秒' };
    }
    return { ms: BLOCK_GAP_MS, reason: '每个账号间隔 15 秒' };
  }

  function formatDuration(ms) {
    const sec = Math.max(0, Math.ceil(Number(ms || 0) / 1000));
    if (sec >= 60) {
      const min = Math.floor(sec / 60);
      const rest = sec % 60;
      return rest ? `${min}分${rest}秒` : `${min}分`;
    }
    return `${sec}秒`;
  }

  function ensureInitialQueueDelay(resetCount = false) {
    const timing = readTiming();
    const now = Date.now();
    writeTiming({
      count: resetCount ? 0 : timing.count,
      nextRunAt: Math.max(timing.nextRunAt || 0, now + BLOCK_GAP_MS),
      reason: '每个账号间隔 15 秒',
    });
  }

  function queueDelayText() {
    const timing = readTiming();
    const remaining = Number(timing.nextRunAt || 0) - Date.now();
    if (remaining <= 0) return '';
    return `${formatDuration(remaining)}后执行 · ${timing.reason || '队列间隔'}`;
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

  function scheduleQueueWorker(delay = 0) {
    if (workerWakeTimer) window.clearTimeout(workerWakeTimer);
    workerWakeTimer = window.setTimeout(() => {
      workerWakeTimer = null;
      maybeStartQueueWorker();
    }, Math.max(0, Number(delay) || 0));
  }

  function maybeStartQueueWorker() {
    if (workerActive) return;
    const queue = recoverStaleRunningItems();
    if (!queue.items.some(item => item.status === 'queued')) return;
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
      const remaining = Number(readTiming().nextRunAt || 0) - Date.now();
      if (remaining <= 0) return true;
      renderPanel(queue);
      await sleep(Math.min(1000, remaining));
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
            clearArticlesBlocked(next.handle);
            setButtonsForHandle(next.handle, 'idle');
            continue;
          }
          const timing = readTiming();
          const count = timing.count + 1;
          const delay = nextDelayForCompletedCount(count);
          writeTiming({ count, nextRunAt: Date.now() + delay.ms, reason: delay.reason });
          upsertQueueItem(next.handle, { displayName: next.displayName, avatarUrl: next.avatarUrl, comment: next.comment, status: 'blocked', error: '' });
          markArticlesBlocked(next.handle);
          toast(`已屏蔽 @${next.handle}`);
        } catch (err) {
          if (cancelRequestedHandles.has(next.key) || !getQueueItem(next.key)) {
            cancelRequestedHandles.delete(next.key);
            setButtonsForHandle(next.handle, 'idle');
            continue;
          }
          writeTiming({ ...readTiming(), nextRunAt: Date.now() + BLOCK_GAP_MS, reason: '失败后暂停 15 秒' });
          upsertQueueItem(next.handle, { displayName: next.displayName, avatarUrl: next.avatarUrl, comment: next.comment, status: 'failed', error: err?.message || String(err) });
          setButtonsForHandle(next.handle, 'idle');
          toast(`屏蔽 @${next.handle} 失败：${err?.message || err}`, true);
          if (/ct0|HTTP 401|HTTP 403|HTTP 419|登录|auth/i.test(String(err?.message || err))) break;
        } finally {
          busyHandles.delete(next.key);
        }
      }
    } finally {
      workerActive = false;
      releaseWorkerLock();
      const queue = readQueue();
      if (!hasActiveQueue(queue)) writeTiming({ ...readTiming(), nextRunAt: 0, reason: '' });
      renderPanel(queue);
      setTimeout(() => {
        if (readQueue().items.some(item => item.status === 'queued')) maybeStartQueueWorker();
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

  function ensureStyles() {
    if (document.getElementById(`${SCRIPT_ID}-style`)) return;
    const style = document.createElement('style');
    style.id = `${SCRIPT_ID}-style`;
    style.textContent = `
      .xqb-btn {
        display: inline-flex !important;
        align-items: center !important;
        justify-content: center !important;
        width: 20px !important;
        height: 20px !important;
        margin: 0 4px !important;
        padding: 0 !important;
        border: 1.5px solid #f4212e !important;
        border-radius: 999px !important;
        background: rgba(244, 33, 46, .08) !important;
        color: #f4212e !important;
        font: 800 11px/1 system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif !important;
        cursor: pointer !important;
        box-sizing: border-box !important;
        flex: 0 0 auto !important;
        z-index: 10 !important;
        transition: transform .12s ease, opacity .12s ease, background .12s ease !important;
      }
      .xqb-btn:hover { transform: scale(1.12) !important; background: rgba(244, 33, 46, .16) !important; }
      .xqb-btn[data-xqb-state="blocking"],
      .xqb-btn[data-xqb-state="unblocking"] { opacity: .45 !important; cursor: wait !important; }
      .xqb-btn[data-xqb-state="blocked"] { border-color: #536471 !important; color: #536471 !important; background: rgba(83, 100, 113, .12) !important; }
      article[data-xqb-blocked="1"] { opacity: .38 !important; transition: opacity .18s ease !important; }
      article[data-xqb-blocked="1"] [data-testid="User-Name"] a { text-decoration: line-through !important; }
      #xqb-panel, #xqb-panel * { box-sizing: border-box; }
      #xqb-panel {
        position: fixed;
        top: 96px;
        right: 12px;
        z-index: 2147483646;
        width: 286px;
        max-width: calc(100vw - 24px);
        color: #0f1419;
        background: rgba(255,255,255,.98);
        border: 1px solid rgba(15,20,25,.14);
        border-radius: 8px;
        box-shadow: 0 10px 34px rgba(0,0,0,.16);
        font-family: system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
        overflow: hidden;
      }
      #xqb-panel[data-collapsed="1"] { width: 44px; }
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
      }
      .xqb-body {
        max-height: 420px;
        overflow: auto;
        padding: 6px;
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
      #xqb-panel[data-collapsed="1"] .xqb-clear { display: none; }
      #xqb-panel[data-collapsed="1"] .xqb-head { justify-content: center; padding: 7px; border-bottom: 0; }
    `;
    document.documentElement.appendChild(style);
  }

  function ensurePanel() {
    ensureStyles();
    let panel = document.getElementById(`${SCRIPT_ID}-panel`);
    if (panel) return panel;
    panel = document.createElement('div');
    panel.id = `${SCRIPT_ID}-panel`;
    panel.addEventListener('click', onPanelClick);
    document.documentElement.appendChild(panel);
    return panel;
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
    if (item.error) bits.push(item.error);
    meta.textContent = bits.filter(Boolean).join(' · ');
    const comment = document.createElement('div');
    comment.className = 'xqb-comment';
    comment.textContent = item.comment || '未抓取到评论文本';
    comment.title = item.comment || '';
    person.append(name, meta, comment);

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

  function renderPanel(queue = readQueue()) {
    if (!document.documentElement) return;
    const panel = ensurePanel();
    const collapsed = !!GM_getValue(PANEL_COLLAPSED_KEY, false);
    const counts = queueCounts(queue);
    const activeCount = counts.queued + counts.blocking;
    panel.dataset.collapsed = collapsed ? '1' : '0';
    panel.replaceChildren();

    const head = document.createElement('div');
    head.className = 'xqb-head';
    const title = document.createElement('div');
    title.className = 'xqb-title';
    title.textContent = `快捷屏蔽 排${counts.queued + counts.blocking} · 已${counts.blocked + counts.unblocking}`;
    const clear = document.createElement('button');
    clear.type = 'button';
    clear.className = 'xqb-icon-btn xqb-clear';
    clear.dataset.action = 'clear';
    clear.title = '清理已撤销和失败记录';
    clear.textContent = '清';
    const collapse = document.createElement('button');
    collapse.type = 'button';
    collapse.className = 'xqb-icon-btn';
    collapse.dataset.action = 'collapse';
    collapse.title = collapsed ? '展开快捷屏蔽队列' : '收起快捷屏蔽队列';
    collapse.textContent = collapsed ? '禁' : '-';
    head.append(title, clear, collapse);
    panel.appendChild(head);

    if (collapsed) return;

    const body = document.createElement('div');
    body.className = 'xqb-body';
    const delay = queueDelayText();
    if (activeCount && delay) {
      const status = document.createElement('div');
      status.className = 'xqb-status-line';
      status.textContent = delay;
      body.appendChild(status);
    }

    const pendingItems = queueSectionItems(queue, 'pending');
    const blockedItems = queueSectionItems(queue, 'blocked');
    renderQueueSection(body, '待屏蔽 / 屏蔽中', pendingItems);
    renderQueueSection(body, '已屏蔽', blockedItems);

    panel.appendChild(body);
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

  async function onPanelClick(event) {
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
      enqueueBlock(item.handle, item.displayName);
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

  function extractHandleFromArticle(article) {
    const nameEl = article.querySelector('[data-testid="User-Name"]');
    if (!nameEl) return '';
    for (const span of nameEl.querySelectorAll('span')) {
      const txt = textOf(span);
      if (/^@[A-Za-z0-9_]{1,15}$/.test(txt)) return displayHandle(txt);
    }
    for (const link of nameEl.querySelectorAll('a[href]')) {
      const path = new URL(link.href, location.href).pathname.split('/').filter(Boolean);
      if (path.length === 1 && /^[A-Za-z0-9_]{1,15}$/.test(path[0])) return displayHandle(path[0]);
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

  function extractCommentFromArticle(article) {
    const textEl = article.querySelector('[data-testid="tweetText"]');
    if (textEl) return textOf(textEl).slice(0, 280);
    const langEl = article.querySelector('[lang]');
    if (langEl && !langEl.closest('[data-testid="User-Name"]')) return textOf(langEl).slice(0, 280);
    return '';
  }

  function queuePatchFromArticle(article, handle, displayName = '') {
    return {
      displayName: displayName || extractDisplayNameFromArticle(article, handle),
      avatarUrl: extractAvatarFromArticle(article),
      comment: extractCommentFromArticle(article),
    };
  }

  function isStatusPage() {
    return /\/status\/\d+/.test(location.pathname);
  }

  function isLikelyMainStatusArticle(article) {
    if (!isStatusPage()) return false;
    const first = document.querySelector('main article[data-testid="tweet"]');
    return first === article;
  }

  function injectButtons() {
    if (!document.body) return;
    ensureStyles();

    document.querySelectorAll('article[data-testid="tweet"]:not([data-xqb-seen])').forEach(article => {
      article.dataset.xqbSeen = '1';
      if (isLikelyMainStatusArticle(article)) return;

      const handle = extractHandleFromArticle(article);
      if (!handle) return;
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
      setButtonState(btn, ['queued', 'blocking', 'blocked'].includes(item?.status) ? item.status : 'idle');

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

      const caret = article.querySelector('[data-testid="caret"]');
      if (caret) {
        caret.insertAdjacentElement('beforebegin', btn);
      } else {
        article.style.position = 'relative';
        Object.assign(btn.style, {
          position: 'absolute',
          top: '10px',
          right: '44px',
        });
        article.appendChild(btn);
      }

      if (item?.status === 'blocked') markArticlesBlocked(handle);
    });
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

  function markArticlesBlocked(handle) {
    document.querySelectorAll('article[data-testid="tweet"]').forEach(article => {
      if (articleHasHandle(article, handle)) article.dataset.xqbBlocked = '1';
    });
    setButtonsForHandle(handle, 'blocked');
  }

  function clearArticlesBlocked(handle) {
    document.querySelectorAll('article[data-testid="tweet"]').forEach(article => {
      if (articleHasHandle(article, handle)) delete article.dataset.xqbBlocked;
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

    const queue = readQueue();
    ensureInitialQueueDelay(!hasActiveQueue(queue));
    const meta = sourceArticle ? queuePatchFromArticle(sourceArticle, handle, displayName) : { displayName };
    upsertQueueItem(handle, { ...meta, status: 'queued', error: '' });
    setButtonsForHandle(handle, 'queued');
    if (sourceArticle) sourceArticle.dataset.xqbQueued = '1';
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
    renderPanel();

    if (typeof GM_addValueChangeListener === 'function') {
      GM_addValueChangeListener(QUEUE_KEY, () => {
        renderPanel();
        document.querySelectorAll('article[data-testid="tweet"]').forEach(article => {
          const handle = extractHandleFromArticle(article);
          const item = handle ? getQueueItem(handle) : null;
          if (item?.status === 'blocked') article.dataset.xqbBlocked = '1';
          else delete article.dataset.xqbBlocked;
          if (handle) setButtonsForHandle(handle, ['queued', 'blocking', 'blocked'].includes(item?.status) ? item.status : 'idle');
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
