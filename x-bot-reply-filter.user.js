// ==UserScript==
// @name         垃圾推号大扫除 - 自用版
// @namespace    http://tampermonkey.net/
// @version      6.18.6
// @description  扫描推文回复中的垃圾用户批量拉黑
// @author       summeriscoming
// @license MIT
// @icon         data:image/svg+xml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCA2NCA2NCI+PGNpcmNsZSBjeD0iMzIiIGN5PSIzMiIgcj0iMzEiIGZpbGw9IiNmNDIxMmUiLz48Y2lyY2xlIGN4PSIyNyIgY3k9IjI3IiByPSIxMSIgZmlsbD0ibm9uZSIgc3Ryb2tlPSIjZmZmIiBzdHJva2Utd2lkdGg9IjQuNSIvPjxsaW5lIHgxPSIzNSIgeTE9IjM1IiB4Mj0iNDgiIHkyPSI0OCIgc3Ryb2tlPSIjZmZmIiBzdHJva2Utd2lkdGg9IjQuNSIgc3Ryb2tlLWxpbmVjYXA9InJvdW5kIi8+PGxpbmUgeDE9IjIxIiB5MT0iMjciIHgyPSIzMyIgeTI9IjI3IiBzdHJva2U9IiNmZmYiIHN0cm9rZS13aWR0aD0iMy41IiBzdHJva2UtbGluZWNhcD0icm91bmQiLz48bGluZSB4MT0iMjciIHkxPSIyMSIgeDI9IjI3IiB5Mj0iMzMiIHN0cm9rZT0iI2ZmZiIgc3Ryb2tlLXdpZHRoPSIzLjUiIHN0cm9rZS1saW5lY2FwPSJyb3VuZCIvPjwvc3ZnPg==
// @match        https://twitter.com/*
// @match        https://x.com/*
// @grant        unsafeWindow
// @grant        GM_xmlhttpRequest
// @grant        GM_getValue
// @grant        GM_setValue
// @connect      x.com
// @connect      raw.githubusercontent.com
// @connect      api.github.com
// @run-at       document-start
// @downloadURL https://raw.githubusercontent.com/shenyue019-blip/x-bot-reply-filter/main/x-bot-reply-filter.user.js
// @updateURL https://raw.githubusercontent.com/shenyue019-blip/x-bot-reply-filter/main/x-bot-reply-filter.user.js
// ==/UserScript==

(function () {
  'use strict';

  // ── Detection rules ──────────────────────────────────────────────────
  const HEART_RE   = /[\u2764\u2665\u2763\u{1F493}\u{1F494}\u{1F495}\u{1F496}\u{1F497}\u{1F498}\u{1F499}\u{1F49A}\u{1F49B}\u{1F49C}\u{1F49D}\u{1F49E}\u{1F49F}\u{1F5A4}\u{1F90D}\u{1F90E}\u{1F9E1}]/u;
  // Basic CJK block — used to distinguish Chinese-context tweets from English ones
  const CHINESE_RE = /[\u4e00-\u9fff\u3400-\u4dbf]/;
  const FACE_EMOJI_SRC = '[\\u{1F600}-\\u{1F64F}]|[\\u{1F910}-\\u{1F917}]|[\\u{1F920}-\\u{1F92F}]|[\\u{1F970}-\\u{1F97A}]|\\u{1F9D0}|[\\u{1FAE0}-\\u{1FAE8}]|[\\u263A\\u2639]';
  const NON_FACE_EMOJI_SRC = `(?!(?:${FACE_EMOJI_SRC}))\\p{Extended_Pictographic}[\\uFE0F\\u{1F3FB}-\\u{1F3FF}]?`;
  // Strange characters for decorative spam: Unicode symbols only. Punctuation, including CJK/fullwidth punctuation, is intentionally excluded.
  const DECOR_SYMBOL_SRC = `(?!(?:${NON_FACE_EMOJI_SRC}))\\p{S}`;
  const DECOR_SYMBOL_RUN_SRC = `(?:${DECOR_SYMBOL_SRC})+`;
  const { content: DEFAULT_SUSPECT_KWS, name: DEFAULT_SUSPECT_NAME_KWS, regex: DEFAULT_SUSPECT_RE_KWS } = buildDefaultSuspectPresets();
  const DEFAULT_HIDE_ONLY_RE_KWS = [];
  const DEFAULT_REFERRAL_PROFILE_RE_KWS = [];
  const REMOTE_RULES_URL = 'https://raw.githubusercontent.com/stigfire/x_fraud_block/main/rules/keywords.json';
  const REMOTE_RULES_API_URL = 'https://api.github.com/repos/stigfire/x_fraud_block/contents/rules/keywords.json?ref=main';
  const GREASYFORK_URL = 'https://greasyfork.org/en/scripts/573991-x-fraud-scanner-%E5%9E%83%E5%9C%BE%E6%8E%A8%E5%8F%B7%E4%B8%80%E6%89%AB%E7%A9%BA';
  const REMOTE_RULES_FETCH_INTERVAL = 60 * 60 * 1000;
  const REMOTE_RULES_MAX_BYTES = 100 * 1024;
  const REMOTE_RULE_LIMITS = {
    content: 300,
    name: 300,
    regex: 80,
    hideOnlyRegex: 80,
    referralProfileRegex: 80,
    keywordLen: 120,
    regexLen: 500,
  };
  let remoteRulesActive = !!GM_getValue('remote_rules_active', false);
  let remoteRulesCache = null;
  let remoteRulesFetching = false;
  let remoteRulesLastError = GM_getValue('remote_rules_last_error', '');
  let remoteRulesLastChange = GM_getValue('remote_rules_last_change', '');
  // Keyword storage: only user additions/deletions are persisted.
  // Defaults are always merged in at startup, so new script-level presets
  // appear automatically even when the user has existing stored data.
  function _normKw(k) {
    return String(k).trim().toLowerCase();
  }
  function _cleanKwList(list) {
    const seen = new Set();
    const out = [];
    for (const raw of Array.isArray(list) ? list : []) {
      const v = String(raw).trim();
      const norm = _normKw(v);
      if (!v || seen.has(norm)) continue;
      seen.add(norm);
      out.push(v);
    }
    return out;
  }
  function _regexPatternParts(raw) {
    const value = String(raw).trim();
    const m = value.match(/^(content|body|name|profile):(.*)$/is);
    if (!m) return { raw: value, scope: 'both', pat: value };
    const scope = m[1].toLowerCase();
    return { raw: value, scope: scope === 'name' ? 'name' : (scope === 'profile' ? 'profile' : 'body'), pat: m[2].trim() };
  }
  function _limitRemoteList(list, limit, maxLen, isRegex = false) {
    const out = [];
    for (const item of _cleanKwList(list)) {
      if (item.length > maxLen) continue;
      if (isRegex) {
        const parsed = _regexPatternParts(item);
        if (!parsed.pat) continue;
        try { new RegExp(parsed.pat, 'mu'); } catch (_) { continue; }
      }
      out.push(item);
      if (out.length >= limit) break;
    }
    return out;
  }
  function _remoteArray(obj, key) {
    if (Array.isArray(obj?.[key])) return obj[key];
    if (Array.isArray(obj?.rules?.[key])) return obj.rules[key];
    return [];
  }
  function sanitizeRemoteRulesPayload(payload, fetchedAt = 0) {
    const obj = payload && typeof payload === 'object' ? payload : {};
    const rules = {
      contentKeywords: _limitRemoteList(_remoteArray(obj, 'contentKeywords'), REMOTE_RULE_LIMITS.content, REMOTE_RULE_LIMITS.keywordLen),
      nameKeywords: _limitRemoteList(_remoteArray(obj, 'nameKeywords'), REMOTE_RULE_LIMITS.name, REMOTE_RULE_LIMITS.keywordLen),
      regexKeywords: _limitRemoteList(_remoteArray(obj, 'regexKeywords'), REMOTE_RULE_LIMITS.regex, REMOTE_RULE_LIMITS.regexLen, true),
      hideOnlyRegexKeywords: _limitRemoteList(_remoteArray(obj, 'hideOnlyRegexKeywords'), REMOTE_RULE_LIMITS.hideOnlyRegex, REMOTE_RULE_LIMITS.regexLen, true),
      referralProfileRegexKeywords: _limitRemoteList(_remoteArray(obj, 'referralProfileRegexKeywords'), REMOTE_RULE_LIMITS.referralProfileRegex, REMOTE_RULE_LIMITS.regexLen, true),
    };
    return {
      schemaVersion: Number(obj.schemaVersion) || 1,
      rulesVersion: String(obj.rulesVersion || obj.version || '').slice(0, 48),
      updatedAt: String(obj.updatedAt || '').slice(0, 48),
      fetchedAt: Number(fetchedAt || obj.fetchedAt || 0) || 0,
      rules,
    };
  }
  function loadRemoteRulesCache() {
    try {
      const cached = sanitizeRemoteRulesPayload(GM_getValue('remote_rules_cache', null));
      const total = cached.rules.contentKeywords.length + cached.rules.nameKeywords.length + cached.rules.regexKeywords.length + cached.rules.hideOnlyRegexKeywords.length + cached.rules.referralProfileRegexKeywords.length;
      remoteRulesCache = total > 0 || cached.rulesVersion ? cached : null;
    } catch (_) {
      remoteRulesCache = null;
    }
  }
  loadRemoteRulesCache();
  function remoteDefaultsForKey(key) {
    if (!remoteRulesActive || !remoteRulesCache?.rules) return [];
    if (key === 'suspect_kws') return remoteRulesCache.rules.contentKeywords || [];
    if (key === 'suspect_name_kws') return remoteRulesCache.rules.nameKeywords || [];
    if (key === 'suspect_re_kws') return remoteRulesCache.rules.regexKeywords || [];
    if (key === 'hide_only_re_kws') return remoteRulesCache.rules.hideOnlyRegexKeywords || [];
    if (key === 'referral_profile_re_kws') return remoteRulesCache.rules.referralProfileRegexKeywords || [];
    return [];
  }
  function _combinedDefaults(defaults, key) {
    return _cleanKwList([...defaults, ...remoteDefaultsForKey(key)]);
  }
  function _sameList(a, b) {
    return a.length === b.length && a.every((v, i) => v === b[i]);
  }
  function _loadKws(defaults, key) {
    const activeDefaults = _combinedDefaults(defaults, key);
    const rawAdds = GM_getValue(key + '_add', []);
    const rawAddList = Array.isArray(rawAdds) ? rawAdds : [];
    const defNorms = new Set(activeDefaults.map(_normKw));
    const adds = _cleanKwList(rawAddList).filter(k => !defNorms.has(_normKw(k)));
    if (!_sameList(rawAddList, adds)) GM_setValue(key + '_add', adds);
    const delNorms = new Set((GM_getValue(key + '_del', []) || []).map(_normKw));
    return _cleanKwList([...activeDefaults, ...adds]).filter(k => !delNorms.has(_normKw(k)));
  }
  function _saveKwSet(live, defaults, key) {
    const activeDefaults = _combinedDefaults(defaults, key);
    const cleanLive = _cleanKwList(live);
    const defNorms = new Set(activeDefaults.map(_normKw));
    const liveNorms = new Set(cleanLive.map(_normKw));
    const activeDefaultNorms = new Set(activeDefaults.map(_normKw));
    const preservedDels = _cleanKwList(GM_getValue(key + '_del', []))
      .filter(k => !activeDefaultNorms.has(_normKw(k)) && !liveNorms.has(_normKw(k)));
    GM_setValue(key + '_add', cleanLive.filter(k => !defNorms.has(_normKw(k))));
    GM_setValue(key + '_del', _cleanKwList([...preservedDels, ...activeDefaults.filter(k => !liveNorms.has(_normKw(k)))]));
  }
  let SUSPECT_KWS      = _loadKws(DEFAULT_SUSPECT_KWS,      'suspect_kws');
  let SUSPECT_NAME_KWS = _loadKws(DEFAULT_SUSPECT_NAME_KWS, 'suspect_name_kws');
  let SUSPECT_RE_KWS   = _loadKws(DEFAULT_SUSPECT_RE_KWS,   'suspect_re_kws');
  let HIDE_ONLY_RE_KWS = _loadKws(DEFAULT_HIDE_ONLY_RE_KWS, 'hide_only_re_kws');
  let REFERRAL_PROFILE_RE_KWS = _loadKws(DEFAULT_REFERRAL_PROFILE_RE_KWS, 'referral_profile_re_kws');
  function reloadKws() {
    SUSPECT_KWS      = _loadKws(DEFAULT_SUSPECT_KWS,      'suspect_kws');
    SUSPECT_NAME_KWS = _loadKws(DEFAULT_SUSPECT_NAME_KWS, 'suspect_name_kws');
    SUSPECT_RE_KWS   = _loadKws(DEFAULT_SUSPECT_RE_KWS,   'suspect_re_kws');
    HIDE_ONLY_RE_KWS = _loadKws(DEFAULT_HIDE_ONLY_RE_KWS, 'hide_only_re_kws');
    REFERRAL_PROFILE_RE_KWS = _loadKws(DEFAULT_REFERRAL_PROFILE_RE_KWS, 'referral_profile_re_kws');
  }
  function saveKws() {
    _saveKwSet(SUSPECT_KWS,      DEFAULT_SUSPECT_KWS,      'suspect_kws');
    _saveKwSet(SUSPECT_NAME_KWS, DEFAULT_SUSPECT_NAME_KWS, 'suspect_name_kws');
    _saveKwSet(SUSPECT_RE_KWS,   DEFAULT_SUSPECT_RE_KWS,   'suspect_re_kws');
    _saveKwSet(HIDE_ONLY_RE_KWS, DEFAULT_HIDE_ONLY_RE_KWS, 'hide_only_re_kws');
    _saveKwSet(REFERRAL_PROFILE_RE_KWS, DEFAULT_REFERRAL_PROFILE_RE_KWS, 'referral_profile_re_kws');
  }
  function kwSetConfig(type) {
    if (type === 'content') return { key: 'suspect_kws', defaults: DEFAULT_SUSPECT_KWS, live: () => SUSPECT_KWS };
    if (type === 'name') return { key: 'suspect_name_kws', defaults: DEFAULT_SUSPECT_NAME_KWS, live: () => SUSPECT_NAME_KWS };
    if (type === 'regex') return { key: 'suspect_re_kws', defaults: DEFAULT_SUSPECT_RE_KWS, live: () => SUSPECT_RE_KWS };
    if (type === 'hide_only_regex') return { key: 'hide_only_re_kws', defaults: DEFAULT_HIDE_ONLY_RE_KWS, live: () => HIDE_ONLY_RE_KWS };
    if (type === 'referral_profile_regex') return { key: 'referral_profile_re_kws', defaults: DEFAULT_REFERRAL_PROFILE_RE_KWS, live: () => REFERRAL_PROFILE_RE_KWS };
    return null;
  }
  function addManualKeyword(type, value) {
    const cfg = kwSetConfig(type);
    const cleanValue = String(value || '').trim();
    if (!cfg || !cleanValue) return false;
    const norm = _normKw(cleanValue);
    if (cfg.live().some(item => _normKw(item) === norm)) return false;
    const defaults = _combinedDefaults(cfg.defaults, cfg.key);
    const addKey = cfg.key + '_add';
    const delKey = cfg.key + '_del';
    const adds = _cleanKwList(GM_getValue(addKey, []));
    const nextAdds = defaults.some(item => _normKw(item) === norm) || adds.some(item => _normKw(item) === norm)
      ? adds
      : [...adds, cleanValue];
    const nextDels = _cleanKwList(GM_getValue(delKey, [])).filter(item => _normKw(item) !== norm);
    GM_setValue(addKey, nextAdds);
    GM_setValue(delKey, nextDels);
    reloadKws();
    refreshKeywordPanelIfOpen();
    refreshVisibleKeywordMatches();
    return true;
  }
  function removeManualKeyword(type, value) {
    const cfg = kwSetConfig(type);
    const cleanValue = String(value || '').trim();
    if (!cfg || !cleanValue) return false;
    const norm = _normKw(cleanValue);
    const defaults = _combinedDefaults(cfg.defaults, cfg.key);
    const addKey = cfg.key + '_add';
    const delKey = cfg.key + '_del';
    const nextAdds = _cleanKwList(GM_getValue(addKey, [])).filter(item => _normKw(item) !== norm);
    const curDels = _cleanKwList(GM_getValue(delKey, []));
    const nextDels = defaults.some(item => _normKw(item) === norm)
      ? (curDels.some(item => _normKw(item) === norm) ? curDels : [...curDels, cleanValue])
      : curDels.filter(item => _normKw(item) !== norm);
    GM_setValue(addKey, nextAdds);
    GM_setValue(delKey, nextDels);
    reloadKws();
    refreshKeywordPanelIfOpen();
    refreshVisibleKeywordMatches();
    return true;
  }
  function refreshVisibleKeywordMatches() {
    document.querySelectorAll('article[data-testid="tweet"]').forEach(art => {
      art.querySelectorAll?.('button[data-xfs-handle]').forEach(btn => btn.remove());
      delete art.dataset.xfsIbtn;
    });
    reapplyContentRulesForVisible();
    injectInlineButtons();
    applyHideAll();
  }
  function commitKeywordChanges() {
    saveKws();
    reloadKws();
    refreshKeywordPanelIfOpen();
    refreshVisibleKeywordMatches();
  }
  let regexCacheKey = '';
  let regexCache = [];
  function compiledRegexes(patterns) {
    const key = patterns.join('\n');
    if (key === regexCacheKey) return regexCache;
    regexCacheKey = key;
    regexCache = patterns.map(pat => {
      const parsed = _regexPatternParts(pat);
      try { return { pat, scope: parsed.scope, re: new RegExp(parsed.pat, 'mu') }; }
      catch (_) { return null; }
    }).filter(Boolean);
    return regexCache;
  }
  function _kwAdditions(live, defaults) {
    const defNorms = new Set(defaults.map(_normKw));
    return _cleanKwList(live).filter(k => !defNorms.has(_normKw(k)));
  }
  async function copyText(text) {
    try {
      await navigator.clipboard.writeText(text);
      return true;
    } catch (_) {
      const ta = document.createElement('textarea');
      ta.value = text;
      ta.style.cssText = 'position:fixed;left:-9999px;top:0;';
      document.body.appendChild(ta);
      ta.focus();
      ta.select();
      let ok = false;
      try { ok = document.execCommand('copy'); } catch (_) {}
      ta.remove();
      return ok;
    }
  }
  async function exportKws() {
    const payload = {
      source: 'X Fraud Scanner custom keyword export',
      version: typeof GM_info !== 'undefined' && GM_info.script ? GM_info.script.version : '',
      exportedAt: new Date().toISOString(),
      note: 'Only manually added keywords are exported. Built-in preset keywords are not included.',
      contentKeywordAdditions: _kwAdditions(SUSPECT_KWS, DEFAULT_SUSPECT_KWS),
      nameKeywordAdditions: _kwAdditions(SUSPECT_NAME_KWS, DEFAULT_SUSPECT_NAME_KWS),
      regexKeywordAdditions: _kwAdditions(SUSPECT_RE_KWS, DEFAULT_SUSPECT_RE_KWS),
      hideOnlyRegexKeywordAdditions: _kwAdditions(HIDE_ONLY_RE_KWS, DEFAULT_HIDE_ONLY_RE_KWS),
      referralProfileRegexKeywordAdditions: _kwAdditions(REFERRAL_PROFILE_RE_KWS, DEFAULT_REFERRAL_PROFILE_RE_KWS),
    };
    const text = JSON.stringify(payload, null, 2);
    const ok = await copyText(text);
    console.log('[XFS] custom keyword export:', payload);
    showToast(ok ? '自定义关键词 JSON 已复制' : '复制失败，已输出到 Console', !ok);
  }
  function _arrFromImport(obj, key, legacyKey, nestedKey) {
    if (Array.isArray(obj && obj[key])) return obj[key];
    if (obj && obj.customKeywords && Array.isArray(obj.customKeywords[nestedKey])) return obj.customKeywords[nestedKey];
    const part = obj && obj[legacyKey];
    if (Array.isArray(part)) return part;
    if (part && Array.isArray(part.additions)) return part.additions;
    if (part && Array.isArray(part.active)) return part.active;
    return [];
  }
  function _cleanImportList(list) {
    return [...new Set(list.map(v => String(v).trim()).filter(Boolean))];
  }
  function parseKwImport(raw) {
    const obj = JSON.parse(raw);
    return {
      content: _cleanImportList(_arrFromImport(obj, 'contentKeywordAdditions', 'contentKeywords', 'content')),
      name: _cleanImportList(_arrFromImport(obj, 'nameKeywordAdditions', 'nameKeywords', 'name')),
      regex: _cleanImportList(_arrFromImport(obj, 'regexKeywordAdditions', 'regexKeywords', 'regex')),
      hideOnlyRegex: _cleanImportList(_arrFromImport(obj, 'hideOnlyRegexKeywordAdditions', 'hideOnlyRegexKeywords', 'hideOnlyRegex')),
      referralProfileRegex: _cleanImportList(_arrFromImport(obj, 'referralProfileRegexKeywordAdditions', 'referralProfileRegexKeywords', 'referralProfileRegex')),
    };
  }
  function _mergeKws(live, incoming) {
    return [...new Set([...live, ...incoming])];
  }
  function _replaceCustomKws(live, defaults, incoming) {
    const defSet = new Set(defaults);
    return [...new Set([...live.filter(k => defSet.has(k)), ...incoming])];
  }
  function importKws(mode) {
    const raw = window.prompt('粘贴自定义关键词 JSON');
    if (!raw) return;
    let parsed;
    try {
      parsed = parseKwImport(raw);
    } catch (e) {
      console.warn('[XFS] keyword import parse failed:', e);
      showToast('自定义关键词 JSON 解析失败', true);
      return;
    }
    const total = parsed.content.length + parsed.name.length + parsed.regex.length + parsed.hideOnlyRegex.length + parsed.referralProfileRegex.length;
    if (total === 0) {
      showToast('未发现可导入的自定义关键词', true);
      return;
    }
    if (mode === 'replace' && !window.confirm('覆盖当前自定义关键词？系统预设关键词不会被导入文件覆盖。')) return;

    if (mode === 'replace') {
      SUSPECT_KWS = _replaceCustomKws(SUSPECT_KWS, DEFAULT_SUSPECT_KWS, parsed.content);
      SUSPECT_NAME_KWS = _replaceCustomKws(SUSPECT_NAME_KWS, DEFAULT_SUSPECT_NAME_KWS, parsed.name);
      SUSPECT_RE_KWS = _replaceCustomKws(SUSPECT_RE_KWS, DEFAULT_SUSPECT_RE_KWS, parsed.regex);
      HIDE_ONLY_RE_KWS = _replaceCustomKws(HIDE_ONLY_RE_KWS, DEFAULT_HIDE_ONLY_RE_KWS, parsed.hideOnlyRegex);
      REFERRAL_PROFILE_RE_KWS = _replaceCustomKws(REFERRAL_PROFILE_RE_KWS, DEFAULT_REFERRAL_PROFILE_RE_KWS, parsed.referralProfileRegex);
    } else {
      SUSPECT_KWS = _mergeKws(SUSPECT_KWS, parsed.content);
      SUSPECT_NAME_KWS = _mergeKws(SUSPECT_NAME_KWS, parsed.name);
      SUSPECT_RE_KWS = _mergeKws(SUSPECT_RE_KWS, parsed.regex);
      HIDE_ONLY_RE_KWS = _mergeKws(HIDE_ONLY_RE_KWS, parsed.hideOnlyRegex);
      REFERRAL_PROFILE_RE_KWS = _mergeKws(REFERRAL_PROFILE_RE_KWS, parsed.referralProfileRegex);
    }
    commitKeywordChanges();
    showToast(`已导入 ${total} 个自定义关键词`);
  }

  function remoteRulesSummary() {
    if (!remoteRulesCache?.rules) return '尚未拉取';
    const c = remoteRulesCache.rules.contentKeywords.length;
    const n = remoteRulesCache.rules.nameKeywords.length;
    const r = remoteRulesCache.rules.regexKeywords.length;
    const hr = remoteRulesCache.rules.hideOnlyRegexKeywords.length;
    const pr = remoteRulesCache.rules.referralProfileRegexKeywords.length;
    const ver = remoteRulesCache.rulesVersion ? ` · ${remoteRulesCache.rulesVersion}` : '';
    return `内容 ${c} / 用户名 ${n} / 正则 ${r} / 只隐藏正则 ${hr} / 主页正则 ${pr}${ver}`;
  }

  function remoteRulesTotal(cache) {
    const rules = cache?.rules;
    if (!rules) return 0;
    return rules.contentKeywords.length + rules.nameKeywords.length + rules.regexKeywords.length + rules.hideOnlyRegexKeywords.length + rules.referralProfileRegexKeywords.length;
  }

  function diffRemoteRuleList(prevList, nextList) {
    const prev = Array.isArray(prevList) ? prevList : [];
    const next = Array.isArray(nextList) ? nextList : [];
    let start = 0;
    while (start < prev.length && start < next.length && prev[start] === next[start]) start++;
    let prevEnd = prev.length - 1;
    let nextEnd = next.length - 1;
    while (prevEnd >= start && nextEnd >= start && prev[prevEnd] === next[nextEnd]) {
      prevEnd--;
      nextEnd--;
    }
    const prevMid = Math.max(0, prevEnd - start + 1);
    const nextMid = Math.max(0, nextEnd - start + 1);
    return {
      added: Math.max(0, nextMid - prevMid),
      changed: Math.min(prevMid, nextMid),
      removed: Math.max(0, prevMid - nextMid),
    };
  }

  function remoteRulesChange(prevCache, nextCache) {
    if (!prevCache?.rules) {
      return { firstFetch: true, added: remoteRulesTotal(nextCache), changed: 0, removed: 0 };
    }
    const out = { firstFetch: false, added: 0, changed: 0, removed: 0 };
    [
      ['contentKeywords'],
      ['nameKeywords'],
      ['regexKeywords'],
      ['hideOnlyRegexKeywords'],
      ['referralProfileRegexKeywords'],
    ].forEach(([key]) => {
      const diff = diffRemoteRuleList(prevCache.rules[key], nextCache.rules[key]);
      out.added += diff.added;
      out.changed += diff.changed;
      out.removed += diff.removed;
    });
    return out;
  }

  function remoteRulesChangeText(change) {
    if (change.firstFetch) return `首次拉取 ${change.added} 条`;
    const total = change.added + change.changed + change.removed;
    if (!total) return '本次无变化';
    const parts = [];
    if (change.added) parts.push(`新增 ${change.added}`);
    if (change.changed) parts.push(`修改 ${change.changed}`);
    if (change.removed) parts.push(`删除 ${change.removed}`);
    return `本次变化 ${total} 条（${parts.join(' / ')}）`;
  }

  function remoteRulesFetchedText() {
    const ts = Number(remoteRulesCache?.fetchedAt || 0);
    if (!ts) return '从未更新';
    try { return new Date(ts).toLocaleString(); }
    catch (_) { return '已更新'; }
  }

  function refreshKeywordPanelIfOpen() {
    const panel = document.getElementById('xfs-panel');
    const kwBar = document.getElementById('xfs-kw-bar');
    if (!panel || !kwBar) return;
    if (panel.dataset.xfsGlobalQueueView === '1') return;
    if (panelDockedActive || panel.style.display === 'none' || document.getElementById('xfs-panel-dock')) return;
    showPanel(scanPage(), { keywordsOpen: kwBar.style.display !== 'none' });
  }

  function decodeBase64Utf8(base64) {
    const clean = String(base64 || '').replace(/\s+/g, '');
    const binary = atob(clean);
    const bytes = new Uint8Array(binary.length);
    for (let i = 0; i < binary.length; i++) bytes[i] = binary.charCodeAt(i);
    return new TextDecoder().decode(bytes);
  }

  function requestRemoteRulesText(url, headers = {}) {
    return new Promise((resolve, reject) => {
      GM_xmlhttpRequest({
        method: 'GET',
        url,
        headers,
        timeout: 15000,
        onload(resp) {
          if (resp.status < 200 || resp.status >= 300) {
            reject(new Error(`HTTP ${resp.status}`));
            return;
          }
          resolve(String(resp.responseText || ''));
        },
        onerror() { reject(new Error('network error')); },
        ontimeout() { reject(new Error('timeout')); },
      });
    });
  }

  async function requestRemoteRulesPayload() {
    try {
      const apiText = await requestRemoteRulesText(`${REMOTE_RULES_API_URL}&t=${Date.now()}`, {
        accept: 'application/vnd.github+json',
      });
      const apiPayload = JSON.parse(apiText);
      const decoded = decodeBase64Utf8(apiPayload?.content || '');
      if (decoded.length > REMOTE_RULES_MAX_BYTES) throw new Error('remote rules file too large');
      return JSON.parse(decoded);
    } catch (apiError) {
      console.warn('[XFS] remote rules API fetch failed, falling back to raw:', apiError);
    }

    const text = await requestRemoteRulesText(`${REMOTE_RULES_URL}?t=${Date.now()}`, {
      accept: 'application/json',
    });
    if (text.length > REMOTE_RULES_MAX_BYTES) throw new Error('remote rules file too large');
    return JSON.parse(text);
  }

  async function refreshRemoteRules(opts = {}) {
    const force = !!opts.force;
    const silent = !!opts.silent;
    if (!remoteRulesActive || remoteRulesFetching) return false;
    const last = Number(remoteRulesCache?.fetchedAt || 0);
    if (!force && last && Date.now() - last < REMOTE_RULES_FETCH_INTERVAL) return false;
    remoteRulesFetching = true;
    try {
      const payload = await requestRemoteRulesPayload();
      const prevCache = remoteRulesCache;
      const nextCache = sanitizeRemoteRulesPayload(payload, Date.now());
      remoteRulesLastChange = remoteRulesChangeText(remoteRulesChange(prevCache, nextCache));
      remoteRulesCache = nextCache;
      remoteRulesLastError = '';
      GM_setValue('remote_rules_cache', remoteRulesCache);
      GM_setValue('remote_rules_last_error', '');
      GM_setValue('remote_rules_last_change', remoteRulesLastChange);
      reloadKws();
      refreshKeywordPanelIfOpen();
      reapplyContentRulesForVisible();
      if (!silent) showToast(`远程规则已更新：${remoteRulesLastChange}；当前 ${remoteRulesSummary()}`, false);
      return true;
    } catch (e) {
      remoteRulesLastError = e?.message || String(e);
      GM_setValue('remote_rules_last_error', remoteRulesLastError);
      console.warn('[XFS] remote rules refresh failed:', e);
      if (!silent) showToast(`远程规则更新失败：${remoteRulesLastError}`, true);
      return false;
    } finally {
      remoteRulesFetching = false;
    }
  }

  function scheduleRemoteRulesRefresh() {
    setTimeout(() => refreshRemoteRules({ silent: true }), 5000);
    setInterval(() => refreshRemoteRules({ silent: true }), REMOTE_RULES_FETCH_INTERVAL);
  }

  // ── Config ───────────────────────────────────────────────────────────
  const CTX_LEN    = 20;
  const MAX_BLOCK  = 100;
  const BLOCK_DELAY  = 3000; // base inter-block gap (ms)
  const BLOCK_JITTER = 2000; // random extra added to base, making effective range 3-5s
  const EXPERIMENT_BLOCK_DELAY = 15000;
  const EXPERIMENT_BLOCK_JITTER = 5000;
  const EXPERIMENT_BROWSE_BLOCK_KEY = 'experimental_browse_block_v1';
  const EXPERIMENT_BROWSE_BLOCK_TIMING_KEY = 'experimental_browse_block_timing_v1';
  const EXPERIMENT_BROWSE_BLOCK_HEARTBEAT_STALE = 5 * 60 * 1000;
  const EXPERIMENT_BROWSE_BLOCK_MAX_AGE = 24 * 60 * 60 * 1000;
  const GLOBAL_BLOCK_QUEUE_KEY = 'global_block_queue_v1';
  const GLOBAL_BLOCK_HISTORY_KEY = 'global_block_history_v1';
  const GLOBAL_BLOCK_QUEUE_LOCK_KEY = 'global_block_queue_worker_lock_v1';
  const GLOBAL_BLOCK_QUEUE_PAUSED_KEY = 'global_block_queue_paused_v1';
  const GLOBAL_BLOCK_QUEUE_PAUSE_REASON_KEY = 'global_block_queue_pause_reason_v1';
  const GLOBAL_BLOCK_QUEUE_MINIMIZED_KEY = 'global_block_queue_minimized_v1';
  const GLOBAL_BLOCK_QUEUE_POS_KEY = 'global_block_queue_position_v1';
  const GLOBAL_BLOCK_QUEUE_SHOW_DONE_KEY = 'global_block_queue_show_done_v1';
  const GLOBAL_BLOCK_QUEUE_ROUND_KEY = 'global_block_queue_round_v1';
  const GLOBAL_BLOCK_QUEUE_LOCK_TTL = 15000;
  const GLOBAL_BLOCK_QUEUE_DONE_MAX = 300;
  const GLOBAL_BLOCK_QUEUE_FAILED_RETRY_MS = 8000;
  const GLOBAL_BLOCK_HISTORY_MAX = 5000;
  const GLOBAL_BLOCK_QUEUE_SHORT_COOLDOWN_EVERY = 20;
  const GLOBAL_BLOCK_QUEUE_SHORT_COOLDOWN = 30000;
  const GLOBAL_BLOCK_QUEUE_SHORT_COOLDOWN_JITTER = 15000;
  const GLOBAL_BLOCK_QUEUE_LONG_COOLDOWN_EVERY = 60;
  const GLOBAL_BLOCK_QUEUE_LONG_COOLDOWN = 5 * 60 * 1000;
  const GLOBAL_BLOCK_QUEUE_LONG_COOLDOWN_JITTER = 60 * 1000;
  const GLOBAL_BLOCK_QUEUE_PANEL_W = 136;
  const GLOBAL_BLOCK_QUEUE_SIZE_KEY = 'global_block_queue_size_v1';
  const RESULT_PANEL_POS_KEY = 'xfs_result_panel_position_v1';
  const RESULT_PANEL_SIZE_KEY = 'xfs_result_panel_size_v1';
  const RESULT_PANEL_DOCK_POS_KEY = 'xfs_result_panel_dock_position_v1';
  // Low-follower hiding is intentionally disabled for now. It produced more
  // false positives than profile-link based referral detection, but the old
  // threshold constant is kept here as a note for possible future scoring.
  // const DEFAULT_LOW_FOLLOWER_THRESHOLD = 5;
  const REFERRAL_CACHE_KEY = 'xfs-referral-account-cache-v10';
  const REFERRAL_CACHE_TTL = 48 * 60 * 60 * 1000;
  const REFERRAL_MIN_GAP = 2500;
  const REFERRAL_JITTER = 2500;
  const REFERRAL_RATE_LIMIT_COOLDOWN = 10 * 60 * 1000;
  const REFERRAL_FAILURE_TTL = 30 * 60 * 1000;
  const REFERRAL_MAX_CACHE = 1200;
  const AI_REVIEW_ENABLED_KEY = 'xfs-ai-review-enabled-v1';
  const AI_REVIEW_MODEL_KEY = 'xfs-ai-review-model-v1';
  const AI_REVIEW_API_KEY_KEY = 'xfs-ai-review-api-key-v1';
  const AI_REVIEW_CACHE_KEY = 'xfs-ai-review-cache-v1';
  const AI_REVIEW_CACHE_TTL = 7 * 24 * 60 * 60 * 1000;
  const AI_REVIEW_CACHE_MAX = 800;
  const AI_HIDDEN_HANDLES_KEY = 'xfs-ai-hidden-handles-v1';
  const AI_HIDDEN_HANDLES_TTL = 30 * 24 * 60 * 60 * 1000;
  const AI_HIDDEN_HANDLES_MAX = 1200;
  const AI_EXEMPT_HANDLES_KEY = 'xfs-ai-exempt-handles-v1';
  const AI_EXEMPT_HANDLES_MAX = 2000;
  const AI_LEARNING_EXAMPLES_KEY = 'xfs-ai-learning-examples-v1';
  const AI_LEARNING_LAST_KEY = 'xfs-ai-learning-last-v1';
  const AI_LEARNING_EXAMPLES_MAX = 300;
  const AI_AUTO_RULES_KEY = 'xfs-ai-auto-rules-v1';
  const AI_REVIEW_DEFAULT_MODEL = 'gpt-5.5';
  const DAY_MS = 24 * 60 * 60 * 1000;
  const EXPERIMENT_TIMING_DEFAULTS = Object.freeze({
    slowBlockingMode: false,
    slowBlockDelayMs: EXPERIMENT_BLOCK_DELAY,
    shortCooldownMs: GLOBAL_BLOCK_QUEUE_SHORT_COOLDOWN,
    longCooldownMs: GLOBAL_BLOCK_QUEUE_LONG_COOLDOWN,
  });
  const EXPERIMENT_TIMING_LIMITS = Object.freeze({
    slowBlockDelayMs: { min: EXPERIMENT_BLOCK_DELAY, max: 10 * 60 * 1000 },
    shortCooldownMs: { min: GLOBAL_BLOCK_QUEUE_SHORT_COOLDOWN, max: 30 * 60 * 1000 },
    longCooldownMs: { min: GLOBAL_BLOCK_QUEUE_LONG_COOLDOWN, max: 2 * 60 * 60 * 1000 },
  });
  const YOUNG_ACCOUNT_DAY_OPTIONS = [7, 14, 30, 60, 90];
  const REFERRAL_X_LINK_RE = /\b(?:https?:\/\/)?(?:www\.)?(?:x\.com|twitter\.com)\/(?!home\b|i\b|intent\b|share\b|search\b|settings\b|privacy\b|tos\b|explore\b|notifications\b|messages\b|compose\b)[A-Za-z0-9_]{1,15}\b/i;
  const REFERRAL_X_LINK_GLOBAL_RE = /\b(?:https?:\/\/)?(?:www\.)?(?:x\.com|twitter\.com)\/(?!home\b|i\b|intent\b|share\b|search\b|settings\b|privacy\b|tos\b|explore\b|notifications\b|messages\b|compose\b)[A-Za-z0-9_]{1,15}\b/ig;
  const REFERRAL_ANY_LINK_RE = /\b(?:(?:https?:\/\/|www\.)[^\s<>"'，。、《》【】（）()]+|(?:[A-Za-z0-9](?:[A-Za-z0-9-]{0,61}[A-Za-z0-9])?\.)+(?:com\.cn|net\.cn|org\.cn|com|net|org|io|me|app|dev|xyz|cc|co|tv|link|site|top|shop|info|biz|vip|icu|cn|ly|to|be|gg|club|online|store|live|fun|quest|pw|ru|jp|us|uk|de|ai|one|pro|ink|wiki|work|world|today|space|click|cloud|mobi|red|kim|wang|xin)(?::\d{2,5})?(?:\/[^\s<>"'，。、《》【】（）()]*)?)(?![A-Za-z0-9.-])/ig;
  const DEFAULT_USER_LOOKUP_QUERY_ID = 'IGgvgiOx4QZndDHuD3x9TQ';
  const USER_LOOKUP_QUERY_ID_FALLBACKS = [
    DEFAULT_USER_LOOKUP_QUERY_ID,
    '-oaLodhGbbnzJBACb1kk2Q',
    '1VOOyvKkiI3FMmkeDNxM9A',
  ];
  const blockedHandles = new Set(); // tracks handles blocked this session
  let sweepHasRun = false;          // true after first sweep on current URL
  let hideMatchedActive = GM_getValue('hide_matched', true); // toggle: hide matched users' replies
  let hideReferralActive = GM_getValue('hide_referral_accounts', true); // toggle: hide replies from profile-link referral accounts
  let autoReferralDetectActive = GM_getValue('auto_referral_detect', true); // low-rate background referral lookup for visible replies
  let hideOnlyRulesActive = GM_getValue('hide_only_rules_active', true); // toggle: allow hide-only regex rules to affect hiding without enqueueing blocks
  let skipVerifiedAccountsActive = GM_getValue('skip_verified_accounts', true); // global safety: verified accounts are skipped by automatic hide/block flows
  let youngAccountFilterActive = GM_getValue('young_account_filter_active', false); // optional profile-created-at filter; default off due to lookup cost and false positives
  let youngAccountCutoffMode = normalizeYoungAccountCutoffMode(GM_getValue('young_account_cutoff_mode', 'days'));
  let youngAccountMaxAgeDays = normalizeYoungAccountDays(GM_getValue('young_account_max_age_days', 30));
  let youngAccountCutoffDate = normalizeDateInputValue(GM_getValue('young_account_cutoff_date', defaultYoungAccountCutoffDate()));
  let aiReviewActive = GM_getValue(AI_REVIEW_ENABLED_KEY, false); // optional AI review for non-name suspicious accounts
  let aiAutoRulesActive = GM_getValue(AI_AUTO_RULES_KEY, false); // optional: auto-apply AI rule suggestions
  let panelDockedActive = GM_getValue('panel_docked', false); // remember whether the result panel should open docked
  let buttonsCollapsed = GM_getValue('buttons_collapsed', false); // collapse the right-side floating tool stack
  let toolbarRight = GM_getValue('toolbar_right', 18);
  let toolbarBaseBottom = GM_getValue('toolbar_base_bottom', 160);
  let activeScanMode = '';
  let persistentBlockedCount = Math.max(0, parseInt(GM_getValue('persistent_blocked_count', 0), 10) || 0);
  let userLookupQueryId = GM_getValue('user_lookup_query_id', DEFAULT_USER_LOOKUP_QUERY_ID);
  let capturedApiHeaders = null;
  const globalQueueTabId = `${Date.now().toString(36)}-${Math.random().toString(36).slice(2, 9)}`;
  let globalQueueWorkerActive = false;
  let globalQueueUiTimer = null;
  let globalQueuePanelDragging = false;
  let globalQueuePanelSuppressed = false;
  let refreshAiReviewControlsFn = null;
  let refreshAiLearningControlsFn = null;
  let experimentalBrowseBlockHeartbeatTimer = null;
  const matchedHandlesInView = new Set(); // accumulates matched handles this scroll session; reset on nav
  const matchedUsersCache = new Map();   // handle → full user object; survives DOM unload by React virtual list
  const referralIntentHints = new Map(); // handle -> visible profile/display-name text containing referral intent
  const referralHintRefreshDone = new Set();
  const BEARER = 'AAAAAAAAAAAAAAAAAAAAANRILgAAAAAAnNwIzUejRCOuH5E6I8xnZz4puTs%3D1Zv7ttfk8LF81IUq16cHjhLTvJu4FA33AGWWjCpTnA';

  function clampNumber(value, min, max, fallback) {
    const n = Number(value);
    if (!Number.isFinite(n)) return fallback;
    return Math.min(max, Math.max(min, Math.round(n)));
  }

  function normalizeExperimentTimingConfig(raw) {
    const src = raw && typeof raw === 'object' ? raw : {};
    const next = {
      slowBlockingMode: false,
      slowBlockDelayMs: clampNumber(
        src.slowBlockDelayMs,
        EXPERIMENT_TIMING_LIMITS.slowBlockDelayMs.min,
        EXPERIMENT_TIMING_LIMITS.slowBlockDelayMs.max,
        EXPERIMENT_TIMING_DEFAULTS.slowBlockDelayMs
      ),
      shortCooldownMs: clampNumber(
        src.shortCooldownMs,
        EXPERIMENT_TIMING_LIMITS.shortCooldownMs.min,
        EXPERIMENT_TIMING_LIMITS.shortCooldownMs.max,
        EXPERIMENT_TIMING_DEFAULTS.shortCooldownMs
      ),
      longCooldownMs: clampNumber(
        src.longCooldownMs,
        EXPERIMENT_TIMING_LIMITS.longCooldownMs.min,
        EXPERIMENT_TIMING_LIMITS.longCooldownMs.max,
        EXPERIMENT_TIMING_DEFAULTS.longCooldownMs
      ),
    };
    return next;
  }

  let experimentTimingConfig = normalizeExperimentTimingConfig(GM_getValue(EXPERIMENT_BROWSE_BLOCK_TIMING_KEY, null));

  function saveExperimentTimingConfig(next) {
    experimentTimingConfig = normalizeExperimentTimingConfig(next);
    GM_setValue(EXPERIMENT_BROWSE_BLOCK_TIMING_KEY, experimentTimingConfig);
    syncCurrentExperimentalCooldownTiming();
    refreshGlobalBlockQueueDetailPanel();
    updateGlobalBlockQueuePanel();
    return experimentTimingConfig;
  }

  function effectiveExperimentTimingConfig() {
    return experimentTimingConfig;
  }

  function experimentSlowBlockGapText() {
    const timing = effectiveExperimentTimingConfig();
    return `${formatGlobalQueueCooldown(timing.slowBlockDelayMs)}-${formatGlobalQueueCooldown(timing.slowBlockDelayMs + EXPERIMENT_BLOCK_JITTER)}`;
  }

  function experimentCooldownSummaryText() {
    const timing = effectiveExperimentTimingConfig();
    return `每 ${GLOBAL_BLOCK_QUEUE_SHORT_COOLDOWN_EVERY} 个暂停 ${formatGlobalQueueCooldown(timing.shortCooldownMs)}；每 ${GLOBAL_BLOCK_QUEUE_LONG_COOLDOWN_EVERY} 个暂停 ${formatGlobalQueueCooldown(timing.longCooldownMs)}`;
  }

  function humanizedBoundedDelay(max, opts = {}) {
    const cap = Math.max(0, Math.floor(Number(max) || 0));
    if (!cap) return 0;
    const mode = Math.min(0.95, Math.max(0.05, Number(opts.mode ?? 0.5)));
    const hesitationChance = Math.min(0.9, Math.max(0, Number(opts.hesitationChance ?? 0.12)));
    const tailStart = Math.min(0.98, Math.max(mode, Number(opts.tailStart ?? 0.72)));
    const u = Math.random();
    let ratio = 0;
    if (u < mode) ratio = Math.sqrt(u * mode);
    else ratio = 1 - Math.sqrt((1 - u) * (1 - mode));
    if (Math.random() < hesitationChance) {
      ratio = Math.max(ratio, tailStart + Math.random() * (1 - tailStart));
    }
    return Math.min(cap, Math.round(cap * ratio));
  }

  function syncCurrentExperimentalCooldownTiming() {
    if (!experimentalBrowseBlockActive()) return;
    const round = readGlobalQueueRound();
    if (Number(round.cooldownUntil || 0) <= Date.now()) return;
    if (!Number(round.cooldownStartedAt || 0)) return;
    const nextCooldown = globalQueueCooldownForCount(round.count);
    if (!nextCooldown) return;
    writeGlobalQueueRound({
      ...round,
      reason: nextCooldown.reason,
      cooldownUntil: Number(round.cooldownStartedAt || 0) + nextCooldown.ms,
    });
  }

  function maybeCaptureUserLookupQueryId(url) {
    const m = String(url || '').match(/\/i\/api\/graphql\/([^/?]+)\/UserByScreenName\b/);
    if (!m || !m[1] || m[1] === userLookupQueryId) return;
    userLookupQueryId = m[1];
    GM_setValue('user_lookup_query_id', userLookupQueryId);
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
    const h = normalizeHeaderObject(headers);
    const auth = h.authorization;
    if (!auth || !String(auth).startsWith('Bearer ')) return;
    liveBearer = String(auth).slice(7);
    capturedApiHeaders = h;
  }

  // ── Auth capture — intercept X.com's own requests for the live bearer token ──
  let liveBearer = null;
  let stopBackgroundLoad = false;
  const _navCallbacks = []; // fired by pushState/replaceState/popstate hooks

  (function hookAuth() {
    const win = typeof unsafeWindow !== 'undefined' ? unsafeWindow : window;

    // Hook fetch
    try {
      const origFetch = win.fetch;
      win.fetch = function (input, init) {
        const url = typeof input === 'string' ? input : (input && input.url) || '';
        try {
          const h = (init && init.headers) || (input && input.headers) || {};
          captureApiHeaders(h);
          const get = k => typeof h.get === 'function' ? h.get(k) : (h[k] || h[k.toLowerCase()]);
          const auth = get('Authorization') || get('authorization');
          if (auth && auth.startsWith('Bearer ') && auth.length > 30) {
            liveBearer = auth.slice(7);
          }
        } catch (_) {}
        const p = origFetch.apply(this, arguments);
        if (String(url).includes('/i/api/graphql/')) {
          maybeCaptureUserLookupQueryId(url);
          return p.then(resp => {
            captureReferralAccountsFromResponse(resp);
            return resp;
          });
        }
        return p;
      };
    } catch (e) { console.warn('[XFS] fetch hook failed', e); }

    // Hook XHR (X.com uses both)
    try {
      const origOpen = win.XMLHttpRequest.prototype.open;
      const origSet = win.XMLHttpRequest.prototype.setRequestHeader;
      const origSend = win.XMLHttpRequest.prototype.send;
      win.XMLHttpRequest.prototype.open = function (method, url) {
        this._xfsUrl = url;
        return origOpen.apply(this, arguments);
      };
      win.XMLHttpRequest.prototype.setRequestHeader = function (name, value) {
        if (!this._xfsHeaders) this._xfsHeaders = {};
        this._xfsHeaders[name] = value;
        if (name.toLowerCase() === 'authorization' && String(value).startsWith('Bearer ') && value.length > 30) {
          liveBearer = value.slice(7);
        }
        return origSet.apply(this, arguments);
      };
      win.XMLHttpRequest.prototype.send = function () {
        if (String(this._xfsUrl || '').includes('/i/api/graphql/')) {
          maybeCaptureUserLookupQueryId(this._xfsUrl);
          captureApiHeaders(this._xfsHeaders);
          this.addEventListener('load', function () {
            try { captureReferralAccountsFromText(this.responseText); } catch (_) {}
          });
        }
        return origSend.apply(this, arguments);
      };
    } catch (e) { console.warn('[XFS] XHR hook failed', e); }

    // Hook pushState / replaceState / popstate so startUI gets immediate
    // notification of SPA navigation without waiting for DOM mutations.
    // Same cross-realm pattern as the liveBearer hooks above.
    try {
      const fire = () => _navCallbacks.forEach(fn => { try { fn(); } catch (_) {} });
      ['pushState', 'replaceState'].forEach(method => {
        const orig = win.history[method];
        win.history[method] = function (...args) { orig.apply(this, args); fire(); };
      });
      win.addEventListener('popstate', fire);
    } catch (e) { console.warn('[XFS] nav hook failed', e); }
  })();

  // ── Utilities ────────────────────────────────────────────────────────
  const sleep = ms => new Promise(r => setTimeout(r, ms));

  function showToast(msg, isError) {
    const t = document.createElement('div');
    t.textContent = msg;
    t.style.cssText = `position:fixed;bottom:148px;right:16px;background:${isError ? C.blockRed : C.mute};color:#fff;padding:5px 11px;border-radius:12px;font-size:12px;font-weight:600;z-index:2147483647;pointer-events:none;box-shadow:0 2px 8px rgba(0,0,0,0.2);`;
    document.body.appendChild(t);
    setTimeout(() => { t.style.transition = 'opacity 0.4s'; t.style.opacity = '0'; setTimeout(() => t.remove(), 420); }, 2200);
  }

  function showProgressToast(msg, color = C.mute) {
    const old = document.getElementById('xfs-progress-toast');
    old?.remove();
    const t = document.createElement('div');
    t.id = 'xfs-progress-toast';
    t.textContent = msg;
    t.style.cssText = [
      'position:fixed', 'bottom:148px', 'right:16px',
      `background:${color}`, 'color:#fff',
      'padding:6px 12px', 'border-radius:13px',
      'font-size:12px', 'font-weight:700',
      'z-index:2147483647', 'pointer-events:none',
      'box-shadow:0 3px 12px rgba(0,0,0,0.22)',
      'max-width:260px', 'white-space:nowrap',
    ].join(';');
    document.body.appendChild(t);
    return {
      update(next) { t.textContent = next; },
      close(delay = 0) {
        setTimeout(() => {
          t.style.transition = 'opacity 0.35s, transform 0.35s';
          t.style.opacity = '0';
          t.style.transform = 'translateY(4px)';
          setTimeout(() => t.remove(), 380);
        }, delay);
      },
    };
  }

  function esc(s) {
    return String(s)
      .replace(/&/g, '&amp;').replace(/</g, '&lt;')
      .replace(/>/g, '&gt;').replace(/"/g, '&quot;');
  }

  // X.com renders emoji as <img alt="♥"> (twemoji). textContent skips img elements,
  // so we must walk child nodes and include img.alt to capture emoji in display names.
  // Some Twemoji images have empty alt — fallback: reconstruct the character from the
  // src URL, whose filename is the Unicode code point in hex (e.g. "2665.svg" → ♥).
  function getTextWithEmoji(el) {
    let text = '';
    for (const node of el.childNodes) {
      if (node.nodeType === Node.TEXT_NODE) {
        text += node.textContent;
      } else if (node.nodeName === 'IMG') {
        if (node.alt) {
          text += node.alt;
        } else {
          const m = (node.src || '').match(/\/([0-9a-f]{4,6})(?:\.|-)/ );
          if (m) { try { text += String.fromCodePoint(parseInt(m[1], 16)); } catch (_) {} }
        }
      } else {
        text += getTextWithEmoji(node);
      }
    }
    return text;
  }

  function getCsrf() {
    const m = document.cookie.match(/(?:^|;\s*)ct0=([^;]+)/);
    return m ? m[1] : null;
  }

  function normalizeHandle(handle) {
    return String(handle || '').replace(/^@/, '').trim().toLowerCase();
  }

  function extractHandleFromArticle(art) {
    const nameEl = art.querySelector('[data-testid="User-Name"]');
    if (!nameEl) return null;
    for (const sp of nameEl.querySelectorAll('span')) {
      const t = sp.textContent.trim();
      if (t.startsWith('@') && t.length > 1 && !t.includes(' ')) return t.slice(1);
    }
    for (const a of nameEl.querySelectorAll('a[href]')) {
      const href = a.getAttribute('href') || '';
      const m = href.match(/^\/([A-Za-z0-9_]{1,15})(?:$|[/?#])/);
      if (m && m[1].toLowerCase() !== 'i' && m[1].toLowerCase() !== 'search') return m[1];
    }
    return null;
  }

  function extractDisplayNameFromArticle(art, handle = extractHandleFromArticle(art)) {
    const nameEl = art.querySelector('[data-testid="User-Name"]');
    if (!nameEl || !handle) return handle || '';
    const rawNameText = getTextWithEmoji(nameEl);
    const atIdx = rawNameText.indexOf('@' + handle);
    if (atIdx > 0) return rawNameText.slice(0, atIdx).trim() || handle;
    const nameLink = [...nameEl.querySelectorAll('a')].find(a => {
      const t = getTextWithEmoji(a).trim();
      return t && !t.startsWith('@');
    });
    return nameLink ? getTextWithEmoji(nameLink).trim() || handle : handle;
  }

  function nodeHasVerifiedBadge(node) {
    return !!node?.querySelector?.('[data-testid="icon-verified"],svg[aria-label="Verified account"]');
  }

  function articleHasVerifiedBadge(art) {
    const nameEl = art?.querySelector?.('[data-testid="User-Name"]');
    return nodeHasVerifiedBadge(nameEl);
  }

  function isProtectedVerifiedArticle(art) {
    return !!(skipVerifiedAccountsActive && articleHasVerifiedBadge(art));
  }

  function isProtectedVerifiedHandle(handle) {
    if (!skipVerifiedAccountsActive) return false;
    const key = normalizeHandle(handle);
    if (!key) return false;
    return [...document.querySelectorAll('article[data-testid="tweet"]')].some(art => {
      const artHandle = normalizeHandle(art.dataset.xfsReferralHandle || extractHandleFromArticle(art));
      return artHandle === key && articleHasVerifiedBadge(art);
    });
  }

  function loadReferralCache() {
    const raw = GM_getValue(REFERRAL_CACHE_KEY, {});
    const now = Date.now();
    const cache = new Map();
    if (!raw || typeof raw !== 'object' || Array.isArray(raw)) return cache;
    Object.entries(raw).forEach(([handle, item]) => {
      const ts = Number(item && item.ts);
      if (Number.isFinite(ts) && now - ts < REFERRAL_CACHE_TTL) {
        cache.set(handle, {
          isReferral: !!(item && item.isReferral),
          isLinkReferral: !!(item && item.isLinkReferral),
          isYoungAccount: !!(item && item.isYoungAccount),
          urls: Array.isArray(item && item.urls) ? item.urls : [],
          createdAt: String((item && item.createdAt) || ''),
          accountAgeDays: Number.isFinite(Number(item && item.accountAgeDays)) ? Number(item.accountAgeDays) : null,
          ts,
        });
      }
    });
    return cache;
  }

  const referralCache = loadReferralCache();
  const referralPending = new Map();
  const referralQueue = [];
  const referralFailureCache = new Map();
  let referralQueueActive = false;
  let referralQueueTimer = null;
  let referralWarned = false;

  function saveReferralCache() {
    const entries = [...referralCache.entries()].sort((a, b) => b[1].ts - a[1].ts).slice(0, REFERRAL_MAX_CACHE);
    referralCache.clear();
    const out = {};
    entries.forEach(([handle, item]) => {
      referralCache.set(handle, item);
      out[handle] = item;
    });
    GM_setValue(REFERRAL_CACHE_KEY, out);
  }

  let referralSaveTimer = null;

  function stableStringHash(input) {
    const str = String(input || '');
    let hash = 0x811c9dc5;
    for (let i = 0; i < str.length; i += 1) {
      hash ^= str.charCodeAt(i);
      hash = Math.imul(hash, 0x01000193);
    }
    return (hash >>> 0).toString(36);
  }

  function normalizeAiReviewModel(value) {
    const raw = String(value || '').trim();
    return raw || AI_REVIEW_DEFAULT_MODEL;
  }

  function aiReviewApiKey() {
    return String(GM_getValue(AI_REVIEW_API_KEY_KEY, '') || '').trim();
  }

  function aiReviewModel() {
    return normalizeAiReviewModel(GM_getValue(AI_REVIEW_MODEL_KEY, AI_REVIEW_DEFAULT_MODEL));
  }

  function aiReviewConfigured() {
    return !!(aiReviewActive && aiReviewApiKey());
  }

  function loadAiReviewCache() {
    const raw = GM_getValue(AI_REVIEW_CACHE_KEY, {});
    const now = Date.now();
    const cache = new Map();
    if (!raw || typeof raw !== 'object' || Array.isArray(raw)) return cache;
    Object.entries(raw).forEach(([key, item]) => {
      const ts = Number(item && item.ts);
      if (!Number.isFinite(ts) || now - ts > AI_REVIEW_CACHE_TTL) return;
      cache.set(key, {
        action: String(item?.action || ''),
        confidence: Math.max(0, Math.min(1, Number(item?.confidence) || 0)),
        reason: String(item?.reason || ''),
        ruleSuggestion: item?.ruleSuggestion && typeof item.ruleSuggestion === 'object' ? {
          scope: String(item.ruleSuggestion.scope || ''),
          value: String(item.ruleSuggestion.value || ''),
          note: String(item.ruleSuggestion.note || ''),
          confidence: Math.max(0, Math.min(1, Number(item.ruleSuggestion.confidence) || 0)),
        } : null,
        handle: normalizeHandle(item?.handle || ''),
        displayName: String(item?.displayName || ''),
        source: String(item?.source || ''),
        ts,
      });
    });
    return cache;
  }

  function saveAiReviewCache(cache = aiReviewCache) {
    const entries = [...cache.entries()]
      .sort((a, b) => Number(b[1]?.ts || 0) - Number(a[1]?.ts || 0))
      .slice(0, AI_REVIEW_CACHE_MAX);
    cache.clear();
    const out = {};
    entries.forEach(([key, item]) => {
      cache.set(key, item);
      out[key] = item;
    });
    GM_setValue(AI_REVIEW_CACHE_KEY, out);
  }

  function aiReviewFingerprint(user) {
    const handle = normalizeHandle(user?.handle || '');
    const displayName = String(user?.displayName || '');
    const tweetSnippet = String(user?.tweetSnippet || '');
    const cats = normalizeQueuePreviewCats(user?.cats).join(',');
    const heartHits = Array.isArray(user?.heartHits) ? user.heartHits.join('|') : '';
    const nameKwHits = Array.isArray(user?.nameKwHits) ? user.nameKwHits.join('|') : '';
    const kwHits = Array.isArray(user?.kwHits) ? user.kwHits.map(hit => `${hit?.kw || ''}:${hit?.snippet || ''}`).join('|') : '';
    const reHits = Array.isArray(user?.reHits) ? user.reHits.map(hit => `${hit?.pat || ''}:${hit?.snippet || ''}`).join('|') : '';
    return stableStringHash([handle, displayName, tweetSnippet, cats, heartHits, nameKwHits, kwHits, reHits].join('\u001f'));
  }

  function loadAiHiddenHandles() {
    const raw = GM_getValue(AI_HIDDEN_HANDLES_KEY, {});
    const now = Date.now();
    const cache = new Map();
    if (!raw || typeof raw !== 'object' || Array.isArray(raw)) return cache;
    Object.entries(raw).forEach(([key, item]) => {
      const ts = Number(item && item.ts);
      if (!Number.isFinite(ts) || now - ts > AI_HIDDEN_HANDLES_TTL) return;
      const handle = normalizeHandle(item?.handle || key);
      if (!handle) return;
      cache.set(handle, {
        handle,
        reason: String(item?.reason || ''),
        confidence: Math.max(0, Math.min(1, Number(item?.confidence) || 0)),
        source: String(item?.source || ''),
        ts,
      });
    });
    return cache;
  }

  function saveAiHiddenHandles(cache = aiHiddenHandles) {
    const entries = [...cache.entries()]
      .sort((a, b) => Number(b[1]?.ts || 0) - Number(a[1]?.ts || 0))
      .slice(0, AI_HIDDEN_HANDLES_MAX);
    cache.clear();
    const out = {};
    entries.forEach(([key, item]) => {
      cache.set(key, item);
      out[key] = item;
    });
    GM_setValue(AI_HIDDEN_HANDLES_KEY, out);
  }

  function loadAiExemptHandles() {
    const raw = GM_getValue(AI_EXEMPT_HANDLES_KEY, {});
    const cache = new Map();
    if (!raw || typeof raw !== 'object' || Array.isArray(raw)) return cache;
    Object.entries(raw).forEach(([key, item]) => {
      const handle = normalizeHandle(item?.handle || key);
      if (!handle) return;
      cache.set(handle, {
        handle,
        reason: String(item?.reason || ''),
        source: String(item?.source || ''),
        ts: Number(item?.ts || 0) || Date.now(),
      });
    });
    return cache;
  }

  function saveAiExemptHandles(cache = aiExemptHandles) {
    const entries = [...cache.entries()]
      .sort((a, b) => Number(b[1]?.ts || 0) - Number(a[1]?.ts || 0))
      .slice(0, AI_EXEMPT_HANDLES_MAX);
    cache.clear();
    const out = {};
    entries.forEach(([key, item]) => {
      cache.set(key, item);
      out[key] = item;
    });
    GM_setValue(AI_EXEMPT_HANDLES_KEY, out);
  }

  function rememberAiExemptHandle(user, meta = {}) {
    const handle = normalizeHandle(user?.handle || user);
    if (!handle) return;
    aiExemptHandles.set(handle, {
      handle,
      reason: String(meta.reason || ''),
      source: String(meta.source || 'manual'),
      ts: Date.now(),
    });
    saveAiExemptHandles();
    clearQueuedAiReviewForHandle(handle);
    removeQueuedGlobalBlockForHandle(handle);
  }

  function forgetAiExemptHandle(user) {
    const handle = normalizeHandle(user?.handle || user);
    if (!handle) return;
    if (aiExemptHandles.delete(handle)) saveAiExemptHandles();
  }

  function isAiExemptHandle(handle) {
    const key = normalizeHandle(handle);
    if (!key) return false;
    return aiExemptHandles.has(key);
  }

  function purgeAiMemoryForHandle(handle) {
    const key = normalizeHandle(handle);
    if (!key) return;
    let changed = false;
    for (const [fingerprint, item] of aiReviewCache.entries()) {
      if (normalizeHandle(item?.handle || '') !== key) continue;
      aiReviewCache.delete(fingerprint);
      changed = true;
    }
    if (changed) saveAiReviewCache();
    if (aiHiddenHandles.delete(key)) saveAiHiddenHandles();
  }

  function clearQueuedAiReviewForHandle(handle) {
    const key = normalizeHandle(handle);
    if (!key) return;
    aiReviewPending.delete(key);
    if (!aiReviewQueue.length) return;
    for (let i = aiReviewQueue.length - 1; i >= 0; i -= 1) {
      if (normalizeHandle(aiReviewQueue[i]?.handle || '') !== key) continue;
      aiReviewQueue.splice(i, 1);
    }
  }

  function removeQueuedGlobalBlockForHandle(handle) {
    const key = normalizeHandle(handle);
    if (!key) return false;
    const q = readGlobalBlockQueue();
    const item = q.items[key];
    if (!item || (item.status || 'queued') === 'running') return false;
    delete q.items[key];
    writeGlobalBlockQueue(q);
    updateGlobalBlockQueuePanel();
    refreshGlobalBlockQueueDetailPanel(q);
    refreshGlobalQueueInlineButtons();
    return true;
  }

  function loadAiLearningExamples() {
    const raw = GM_getValue(AI_LEARNING_EXAMPLES_KEY, []);
    if (!Array.isArray(raw)) return [];
    return raw
      .map(item => ({
        label: ['block', 'hide', 'ignore'].includes(item?.label) ? item.label : 'ignore',
        handle: normalizeHandle(item?.handle || ''),
        displayName: String(item?.displayName || ''),
        source: String(item?.source || ''),
        reason: String(item?.reason || ''),
        fingerprint: String(item?.fingerprint || ''),
        ts: Number(item?.ts || 0) || Date.now(),
      }))
      .filter(item => item.handle || item.displayName || item.reason);
  }

  function loadAiLearningLast() {
    const raw = GM_getValue(AI_LEARNING_LAST_KEY, null);
    if (!raw || typeof raw !== 'object' || Array.isArray(raw)) return null;
    return {
      label: ['block', 'hide', 'ignore'].includes(raw?.label) ? raw.label : 'ignore',
      handle: normalizeHandle(raw?.handle || ''),
      displayName: String(raw?.displayName || ''),
      source: String(raw?.source || ''),
      reason: String(raw?.reason || ''),
      fingerprint: String(raw?.fingerprint || ''),
      ts: Number(raw?.ts || 0) || 0,
    };
  }

  function saveAiLearningExamples(list = aiLearningExamples) {
    const items = (Array.isArray(list) ? list : [])
      .sort((a, b) => Number(b.ts || 0) - Number(a.ts || 0))
      .slice(0, AI_LEARNING_EXAMPLES_MAX);
    aiLearningExamples = items;
    GM_setValue(AI_LEARNING_EXAMPLES_KEY, items);
  }

  function saveAiLearningLast(entry) {
    if (!entry) return;
    GM_setValue(AI_LEARNING_LAST_KEY, {
      label: String(entry.label || 'ignore'),
      handle: normalizeHandle(entry.handle || ''),
      displayName: String(entry.displayName || ''),
      source: String(entry.source || ''),
      reason: String(entry.reason || ''),
      fingerprint: String(entry.fingerprint || ''),
      ts: Number(entry.ts || Date.now()) || Date.now(),
    });
  }

  function recordAiLearningExample(user, label, meta = {}) {
    const handle = normalizeHandle(user?.handle || '');
    const entry = {
      label: ['block', 'hide', 'ignore'].includes(label) ? label : 'ignore',
      handle,
      displayName: String(user?.displayName || ''),
      source: String(meta.source || user?.source || ''),
      reason: String(meta.reason || ''),
      fingerprint: String(meta.fingerprint || aiReviewFingerprint(user || {})),
      ts: Date.now(),
    };
    aiLearningExamples = aiLearningExamples.filter(item => item.fingerprint !== entry.fingerprint || item.label !== entry.label);
    aiLearningExamples.unshift(entry);
    saveAiLearningExamples();
    saveAiLearningLast(entry);
    if (typeof refreshAiReviewControlsFn === 'function') refreshAiReviewControlsFn();
    if (typeof refreshAiLearningControlsFn === 'function') refreshAiLearningControlsFn();
  }

  function aiLearningExampleText(limit = 6) {
    return aiLearningExamples
      .slice(0, limit)
      .map(item => `- ${item.label}: @${item.handle || '-'} ${item.displayName ? `(${String(item.displayName).slice(0, 40)}) ` : ''}${item.reason ? `=> ${String(item.reason).slice(0, 120)}` : ''}`)
      .join('\n');
  }

  function maybeApplyAiRuleSuggestion(suggestion, meta = {}) {
    if (!aiAutoRulesActive || !suggestion || !suggestion.scope || !suggestion.value) return false;
    if (Number(suggestion.confidence || 0) < 0.85) return false;
    const raw = String(suggestion.value || '').trim();
    if (!raw) return false;
    let type = '';
    let value = raw;
    if (suggestion.scope === 'name_keyword') type = 'name';
    else if (suggestion.scope === 'content_keyword') type = 'content';
    else if (suggestion.scope === 'name_regex') { type = 'regex'; value = `name:${raw}`; }
    else if (suggestion.scope === 'content_regex') { type = 'regex'; value = `content:${raw}`; }
    else if (suggestion.scope === 'hide_only_regex') { type = 'hide_only_regex'; value = `content:${raw}`; }
    if (!type) return false;
    try {
      const added = addManualKeyword(type, value);
      if (added) {
        showToast(`AI 已建议并更新规则：${suggestion.scope}`, false);
        recordAiLearningExample({
          handle: String(meta.handle || ''),
          displayName: String(meta.displayName || ''),
          source: String(meta.source || 'ai_rule'),
        }, 'ignore', {
          reason: `auto_rule:${suggestion.scope}:${raw}`,
        });
      }
      return added;
    } catch (e) {
      console.warn('[XFS] AI rule suggestion apply failed:', e);
      return false;
    }
  }

  function rememberAiHiddenHandle(user, meta = {}) {
    const handle = normalizeHandle(user?.handle || user);
    if (!handle) return;
    aiHiddenHandles.set(handle, {
      handle,
      reason: String(meta.reason || ''),
      confidence: Math.max(0, Math.min(1, Number(meta.confidence) || 0)),
      source: String(meta.source || 'ai'),
      ts: Date.now(),
    });
    saveAiHiddenHandles();
  }

  function isAiHiddenHandle(handle) {
    const key = normalizeHandle(handle);
    if (!key) return false;
    return aiHiddenHandles.has(key);
  }

  function aiReviewCacheLookup(user) {
    const key = aiReviewFingerprint(user);
    const item = aiReviewCache.get(key);
    if (!item) return null;
    return { key, ...item };
  }

  function aiReviewCacheStore(user, result) {
    const key = aiReviewFingerprint(user);
    aiReviewCache.set(key, {
      action: String(result?.action || 'ignore'),
      confidence: Math.max(0, Math.min(1, Number(result?.confidence) || 0)),
      reason: String(result?.reason || ''),
      ruleSuggestion: result?.ruleSuggestion && typeof result.ruleSuggestion === 'object' ? {
        scope: String(result.ruleSuggestion.scope || ''),
        value: String(result.ruleSuggestion.value || ''),
        note: String(result.ruleSuggestion.note || ''),
        confidence: Math.max(0, Math.min(1, Number(result.ruleSuggestion.confidence) || 0)),
      } : null,
      handle: normalizeHandle(user?.handle || ''),
      displayName: String(user?.displayName || ''),
      source: String(user?.source || ''),
      ts: Date.now(),
    });
    saveAiReviewCache();
  }

  const aiReviewCache = loadAiReviewCache();
  const aiHiddenHandles = loadAiHiddenHandles();
  const aiExemptHandles = loadAiExemptHandles();
  let aiLearningExamples = loadAiLearningExamples();
  const aiReviewPending = new Map();
  const aiReviewQueue = [];
  let aiReviewQueueActive = false;
  let aiReviewQueueTimer = null;

  function aiReviewCandidateText(user, source = '') {
    const cats = normalizeQueuePreviewCats(user?.cats);
    const parts = [
      `handle: @${normalizeHandle(user?.handle || '')}`,
      `display_name: ${String(user?.displayName || '')}`,
      `source: ${String(source || user?.source || '')}`,
      `cats: ${cats.join(', ') || 'none'}`,
      `tweet_snippet: ${String(user?.tweetSnippet || '')}`,
      `name_hits: ${Array.isArray(user?.nameKwHits) ? user.nameKwHits.join(' | ') : ''}`,
      `heart_hits: ${Array.isArray(user?.heartHits) ? user.heartHits.join(' | ') : ''}`,
      `keyword_hits: ${Array.isArray(user?.kwHits) ? user.kwHits.map(hit => `${hit?.kw || ''} => ${hit?.snippet || ''}`).join(' || ') : ''}`,
      `regex_hits: ${Array.isArray(user?.reHits) ? user.reHits.map(hit => `${hit?.pat || ''} => ${hit?.snippet || ''}`).join(' || ') : ''}`,
      `hide_only_hits: ${Array.isArray(user?.hideOnlyReHits) ? user.hideOnlyReHits.map(hit => `${hit?.pat || ''} => ${hit?.snippet || ''}`).join(' || ') : ''}`,
    ];
    const learned = aiLearningExampleText(6);
    if (learned) parts.push(`learned_examples:\n${learned}`);
    return parts.join('\n');
  }

  function isNameIssueMatch(user) {
    if (!user) return false;
    const heartHits = Array.isArray(user.heartHits) ? user.heartHits.length : 0;
    const nameKwHits = Array.isArray(user.nameKwHits) ? user.nameKwHits.length : 0;
    const nameRegexHits = Array.isArray(user.reHits)
      ? user.reHits.filter(hit => String(hit?.snippet || '').startsWith('昵称:')).length
      : 0;
    return heartHits > 0 || nameKwHits > 0 || nameRegexHits > 0;
  }

  function aiReviewActionLabel(action) {
    if (action === 'block') return '拉黑';
    if (action === 'hide') return '隐藏';
    return '放行';
  }

  function hasAiReviewCandidates(users) {
    return (users || []).some(user => !isNameIssueMatch(user));
  }

  function queueAiReviewUsers(users, opts = {}) {
    (users || []).forEach(user => {
      const handle = normalizeHandle(user?.handle || '');
      if (!handle || aiReviewPending.has(handle) || blockedHandles.has(handle) || globalBlockQueueItemForHandle(handle) || isAiHiddenHandle(handle) || isAiExemptHandle(handle)) return;
      aiReviewQueue.push({
        ...user,
        handle,
        source: String(opts.queueSource || user?.source || 'auto'),
      });
      aiReviewPending.set(handle, true);
    });
    processAiReviewQueue();
  }

  async function requestAiReviewDecision(user, opts = {}) {
    const key = normalizeHandle(user?.handle || '');
    if (!key) throw new Error('missing handle');
    const cached = aiReviewCacheLookup(user);
    if (cached) return { ...cached, cached: true };

    const body = {
      model: aiReviewModel(),
      temperature: 0,
      max_tokens: 160,
      response_format: {
        type: 'json_schema',
        json_schema: {
          name: 'xfs_ai_review',
          schema: {
            type: 'object',
            additionalProperties: false,
            properties: {
              action: { type: 'string', enum: ['block', 'hide', 'ignore'] },
              confidence: { type: 'number', minimum: 0, maximum: 1 },
              reason: { type: 'string' },
              rule_suggestion: {
                type: 'object',
                additionalProperties: false,
                properties: {
                  scope: { type: 'string', enum: ['name_keyword', 'content_keyword', 'name_regex', 'content_regex', 'hide_only_regex'] },
                  value: { type: 'string' },
                  note: { type: 'string' },
                  confidence: { type: 'number', minimum: 0, maximum: 1 },
                },
                required: ['scope', 'value', 'note', 'confidence'],
              },
            },
            required: ['action', 'confidence', 'reason'],
          },
          strict: true,
        },
      },
      messages: [
        {
          role: 'system',
          content: '你是中文 X/Twitter 回复垃圾账号审查器。只根据用户提供的信息分类，不要推测额外事实。输出 block、hide、ignore 三选一。用户名、昵称、主页式营销、联系方式、明显引流，优先 block；正文可疑但账号不够确定，优先 hide；看起来正常或不确定，ignore。若能提炼出稳定、可复用的规则，补充一个 rule_suggestion。只输出 JSON。',
        },
        {
          role: 'user',
          content: aiReviewCandidateText(user, opts.queueSource || ''),
        },
      ],
      store: false,
      safety_identifier: stableStringHash(key),
    };
    const apiKey = aiReviewApiKey();
    if (!apiKey) throw new Error('missing OpenAI API key');
    return new Promise((resolve, reject) => {
      GM_xmlhttpRequest({
        method: 'POST',
        url: 'https://api.openai.com/v1/chat/completions',
        headers: {
          'content-type': 'application/json',
          authorization: `Bearer ${apiKey}`,
        },
        data: JSON.stringify(body),
        onload(resp) {
          if (resp.status < 200 || resp.status >= 300) {
            reject(new Error(`HTTP ${resp.status}`));
            return;
          }
          try {
            const data = JSON.parse(resp.responseText || '{}');
            const content = String(data?.choices?.[0]?.message?.content || '').trim();
            const jsonText = content.match(/\{[\s\S]*\}/)?.[0] || content;
            const parsed = JSON.parse(jsonText);
            const action = ['block', 'hide', 'ignore'].includes(parsed?.action) ? parsed.action : 'ignore';
            const confidence = Math.max(0, Math.min(1, Number(parsed?.confidence) || 0));
            const reason = String(parsed?.reason || '').trim().slice(0, 300) || 'AI 未返回理由';
            const ruleSuggestion = parsed?.rule_suggestion && typeof parsed.rule_suggestion === 'object' ? {
              scope: ['name_keyword', 'content_keyword', 'name_regex', 'content_regex', 'hide_only_regex'].includes(parsed.rule_suggestion.scope) ? parsed.rule_suggestion.scope : '',
              value: String(parsed.rule_suggestion.value || '').trim().slice(0, 120),
              note: String(parsed.rule_suggestion.note || '').trim().slice(0, 220),
              confidence: Math.max(0, Math.min(1, Number(parsed.rule_suggestion.confidence) || 0)),
            } : null;
            resolve({
              action,
              confidence,
              reason,
              ruleSuggestion,
              model: data?.model || aiReviewModel(),
            });
          } catch (e) {
            reject(e);
          }
        },
        onerror() {
          reject(new Error('Network error'));
        },
      });
    });
  }

  async function processAiReviewQueue() {
    if (aiReviewQueueActive || !aiReviewQueue.length) return;
    aiReviewQueueActive = true;
    try {
      while (aiReviewQueue.length) {
        const item = aiReviewQueue.shift();
        const handle = normalizeHandle(item?.handle || '');
        if (!handle) continue;
        if (isAiExemptHandle(handle)) {
          aiReviewPending.delete(handle);
          continue;
        }
        try {
          const decision = await requestAiReviewDecision(item, { queueSource: item.source });
          aiReviewCacheStore(item, decision);
          recordAiLearningExample(item, decision.action, {
            source: item.source,
            reason: decision.reason,
          });
          maybeApplyAiRuleSuggestion(decision.ruleSuggestion, {
            handle,
            displayName: item.displayName,
            source: item.source,
          });
          if (decision.action === 'block') {
            enqueueGlobalBlockUsers([{
              ...item,
              handle,
              source: 'ai_review',
              reason: `AI复核：${decision.reason}`,
              aiDecision: 'block',
              aiReason: decision.reason,
              aiConfidence: decision.confidence,
            }], 'ai_review');
            showToast(`AI复核：@${handle} 已加入拉黑排队`, false);
          } else if (decision.action === 'hide') {
            rememberAiHiddenHandle(item, {
              reason: decision.reason,
              confidence: decision.confidence,
              source: item.source || 'ai_review',
            });
            matchedHandlesInView.delete(handle);
            matchedUsersCache.delete(handle);
            matchedUsersCache.delete(normalizeHandle(handle));
            updateHideBadge();
            document.querySelectorAll(`article[data-testid="tweet"]`).forEach(art => {
              const artHandle = normalizeHandle(art.dataset.xfsReferralHandle || extractHandleFromArticle(art));
              if (artHandle !== handle) return;
              art.dataset.xfsAiHidden = '1';
            });
            applyHideAll();
            showToast(`AI复核：@${handle} 已隐藏`, false);
          }
        } catch (e) {
          console.warn(`[XFS] AI review failed @${handle}:`, e);
        } finally {
          aiReviewPending.delete(handle);
        }
        await sleep(250);
      }
    } finally {
      aiReviewQueueActive = false;
    }
  }

  function normalizeYoungAccountDays(value) {
    const n = parseInt(value, 10);
    return YOUNG_ACCOUNT_DAY_OPTIONS.includes(n) ? n : 30;
  }

  function normalizeYoungAccountCutoffMode(value) {
    return value === 'date' ? 'date' : 'days';
  }

  function toDateInputValue(date) {
    const y = date.getFullYear();
    const m = String(date.getMonth() + 1).padStart(2, '0');
    const d = String(date.getDate()).padStart(2, '0');
    return `${y}-${m}-${d}`;
  }

  function defaultYoungAccountCutoffDate() {
    const d = new Date();
    d.setMonth(d.getMonth() - 1);
    return toDateInputValue(d);
  }

  function normalizeDateInputValue(value) {
    const raw = String(value || '').trim();
    if (/^\d{4}-\d{2}-\d{2}$/.test(raw) && Number.isFinite(Date.parse(`${raw}T00:00:00`))) return raw;
    return defaultYoungAccountCutoffDate();
  }

  function youngAccountCutoffMs() {
    if (youngAccountCutoffMode === 'date') {
      return Date.parse(`${youngAccountCutoffDate}T00:00:00`);
    }
    return Date.now() - youngAccountMaxAgeDays * DAY_MS;
  }

  function isYoungAccountByAge(age) {
    const cutoff = youngAccountCutoffMs();
    return !!(youngAccountFilterActive && age && Number.isFinite(cutoff) && Date.parse(age.createdAtIso) >= cutoff);
  }

  function youngAccountRuleLabel() {
    return youngAccountCutoffMode === 'date'
      ? `注册日期晚于 ${youngAccountCutoffDate}`
      : `注册少于 ${youngAccountMaxAgeDays} 天`;
  }

  function accountAgeInfo(createdAt) {
    const raw = String(createdAt || '').trim();
    if (!raw) return null;
    const ms = Date.parse(raw);
    if (!Number.isFinite(ms)) return null;
    const ageMs = Date.now() - ms;
    const ageDays = Math.floor(ageMs / DAY_MS);
    if (!Number.isFinite(ageDays) || ageDays < 0) return null;
    return {
      createdAt: raw,
      createdAtIso: new Date(ms).toISOString(),
      ageMs,
      ageDays,
    };
  }

  function createdAtFromProfile(legacy, userObj = null) {
    return legacy?.created_at
      || legacy?.createdAt
      || userObj?.legacy?.created_at
      || userObj?.legacy?.createdAt
      || userObj?.created_at
      || userObj?.createdAt
      || '';
  }

  function materializeReferralItem(item) {
    if (!item) return null;
    const age = accountAgeInfo(item.createdAt);
    const isYoungAccount = isYoungAccountByAge(age);
    const isLinkReferral = item.isLinkReferral != null
      ? !!item.isLinkReferral
      : !!(Array.isArray(item.urls) && item.urls.length > 0 && !item.isYoungAccount);
    return {
      ...item,
      isLinkReferral,
      isYoungAccount,
      accountAgeDays: age ? age.ageDays : item.accountAgeDays,
      youngAccountMaxAgeDays,
      youngAccountCutoffMode,
      youngAccountCutoffDate,
      isReferral: isLinkReferral || isYoungAccount,
    };
  }

  function referralItemDescription(item) {
    if (!item) return '主页导流链接';
    if (item.isLinkReferral && item.urls?.length) return item.urls[0];
    if (item.isYoungAccount) return `注册 ${item.accountAgeDays} 天，${youngAccountRuleLabel()}`;
    return item.urls?.[0] || '主页导流链接';
  }

  function rememberReferralAccount(handle, urls, opts = {}) {
    const key = normalizeHandle(handle);
    if (!key) return;
    const cleanUrls = [...new Set((Array.isArray(urls) ? urls : []).map(u => String(u || '').trim()).filter(Boolean))];
    if (cleanUrls.length === 0 && opts.allowNegative !== true) return;
    const existing = referralCache.get(key);
    const existingEffective = materializeReferralItem(existing);
    if (cleanUrls.length === 0 && !opts.createdAt && existingEffective?.isReferral) return;
    const mergedUrls = cleanUrls.length > 0
      ? [...new Set([...(existing?.urls || []), ...cleanUrls])]
      : (existing?.urls || []);
    const createdAt = String(opts.createdAt || existing?.createdAt || '');
    const age = accountAgeInfo(createdAt);
    const rawItem = {
      isReferral: false,
      isLinkReferral: mergedUrls.length > 0,
      isYoungAccount: isYoungAccountByAge(age),
      urls: mergedUrls,
      createdAt,
      accountAgeDays: age ? age.ageDays : null,
      ts: Date.now(),
    };
    rawItem.isReferral = materializeReferralItem(rawItem).isReferral;
    referralCache.set(key, rawItem);
    if (!referralSaveTimer) {
      referralSaveTimer = setTimeout(() => {
        referralSaveTimer = null;
        saveReferralCache();
      }, 1000);
    }
    applyReferralAccountToArticles(key);
  }

  function captureReferralAccountsFromResponse(resp) {
    try {
      const type = resp.headers && resp.headers.get && resp.headers.get('content-type');
      if (type && !type.includes('application/json')) return;
      resp.clone().json().then(captureReferralAccountsFromData).catch(() => {});
    } catch (_) {}
  }

  function captureReferralAccountsFromText(text) {
    if (!text || text.length < 20) return;
    try { captureReferralAccountsFromData(JSON.parse(text)); } catch (_) {}
  }

  function extractReferralXLinksFromText(value) {
    const text = String(value || '').trim();
    if (!text) return [];
    REFERRAL_X_LINK_GLOBAL_RE.lastIndex = 0;
    return text.match(REFERRAL_X_LINK_GLOBAL_RE) || [];
  }

  function collectReferralXLinks(candidates) {
    const out = [];
    (Array.isArray(candidates) ? candidates : []).forEach(v => {
      out.push(...extractReferralXLinksFromText(v));
    });
    return [...new Set(out.map(v => String(v || '').trim()).filter(v => REFERRAL_X_LINK_RE.test(v)))];
  }

  function extractAnyLinksFromText(value) {
    const text = String(value || '').trim();
    if (!text) return [];
    REFERRAL_ANY_LINK_RE.lastIndex = 0;
    return text.match(REFERRAL_ANY_LINK_RE) || [];
  }

  function collectReferralAnyLinks(candidates) {
    const out = [];
    (Array.isArray(candidates) ? candidates : []).forEach(v => {
      out.push(...extractAnyLinksFromText(v));
    });
    return [...new Set(out.map(v => String(v || '').trim()).filter(Boolean))];
  }

  function profileReferralRuleText(input) {
    if (input && typeof input === 'object' && !Array.isArray(input)) {
      const texts = Array.isArray(input.texts) ? input.texts : [];
      const links = Array.isArray(input.links) ? input.links : [];
      return stripInvisible([...texts, ...links].filter(Boolean).join(' ')).replace(/\s+/g, ' ').trim();
    }
    return stripInvisible(String(input || '')).replace(/\s+/g, ' ').trim();
  }

  function profileReferralRegexHits(input) {
    return getRegexHits(profileReferralRuleText(input), REFERRAL_PROFILE_RE_KWS, 'profile');
  }

  function profileHasReferralIntent(input) {
    const text = profileReferralRuleText(input);
    return text.includes('大号') || profileReferralRegexHits(input).length > 0;
  }

  function rememberReferralIntentHint(handle, text) {
    const key = normalizeHandle(handle);
    const clean = stripInvisible(String(text || '')).trim();
    if (!key || !profileHasReferralIntent(clean)) return;
    const prev = referralIntentHints.get(key) || '';
    if (!prev.includes(clean)) referralIntentHints.set(key, [prev, clean].filter(Boolean).join(' '));
  }

  function referralLinksFromProfileFacts(facts) {
    const texts = Array.isArray(facts?.texts) ? facts.texts : [];
    const links = Array.isArray(facts?.links) ? facts.links : [];
    const candidates = [...texts, ...links];
    const out = collectReferralXLinks(candidates);
    if (profileHasReferralIntent({ texts, links })) out.push(...collectReferralAnyLinks(candidates));
    return [...new Set(out.map(v => String(v || '').trim()).filter(Boolean))];
  }

  function extractProfileReferralLinks(legacy, extraTexts = []) {
    const facts = { texts: [], links: [] };
    const pushUrl = u => {
      if (!u) return;
      facts.links.push(u.url, u.expanded_url, u.display_url);
    };
    legacy?.entities?.description?.urls?.forEach(pushUrl);
    legacy?.entities?.url?.urls?.forEach(pushUrl);
    if (legacy?.url) facts.links.push(legacy.url);
    if (legacy?.name) facts.texts.push(legacy.name);
    if (legacy?.description) facts.texts.push(legacy.description);
    if (legacy?.location) facts.texts.push(legacy.location);
    facts.texts.push(...(Array.isArray(extraTexts) ? extraTexts : [extraTexts]));
    return referralLinksFromProfileFacts(facts);
  }

  function userProfileExtraTexts(userObj, handle) {
    const key = normalizeHandle(handle);
    return [
      key ? referralIntentHints.get(key) || '' : '',
      userObj?.core?.name,
      userObj?.profile?.name,
      userObj?.display_name,
      userObj?.name,
    ].filter(Boolean);
  }

  function hasCompleteProfileLinkFields(legacy) {
    if (!legacy || typeof legacy !== 'object') return false;
    return 'description' in legacy
      || 'location' in legacy
      || 'url' in legacy
      || !!legacy.entities?.description
      || !!legacy.entities?.url;
  }

  function isReservedPathHandle(handle) {
    return /^(?:home|i|intent|share|search|settings|privacy|tos|explore|notifications|messages|compose)$/i.test(handle || '');
  }

  function captureReferralAccountsFromData(data) {
    const stack = [data];
    const seen = new Set();
    let visited = 0;
    while (stack.length && visited < 20000) {
      const cur = stack.pop();
      if (!cur || typeof cur !== 'object' || seen.has(cur)) continue;
      seen.add(cur);
      visited++;

      const legacy = cur.legacy && typeof cur.legacy === 'object' ? cur.legacy : null;
      if (legacy && legacy.screen_name != null) {
        rememberReferralAccount(legacy.screen_name, extractProfileReferralLinks(legacy, userProfileExtraTexts(cur, legacy.screen_name)), {
          allowNegative: hasCompleteProfileLinkFields(legacy) || !!createdAtFromProfile(legacy, cur),
          createdAt: createdAtFromProfile(legacy, cur),
        });
      } else if (cur.screen_name != null) {
        rememberReferralAccount(cur.screen_name, extractProfileReferralLinks(cur, userProfileExtraTexts(cur, cur.screen_name)), {
          allowNegative: hasCompleteProfileLinkFields(cur) || !!createdAtFromProfile(cur, cur),
          createdAt: createdAtFromProfile(cur, cur),
        });
      }

      if (Array.isArray(cur)) {
        cur.forEach(v => { if (v && typeof v === 'object') stack.push(v); });
      } else {
        Object.values(cur).forEach(v => { if (v && typeof v === 'object') stack.push(v); });
      }
    }
  }

  function extractHandleFromProfileDom(scope) {
    const named = scope.querySelector?.('[data-testid="UserName"][data-x-screen-name]');
    const dataHandle = named?.getAttribute('data-x-screen-name');
    if (dataHandle) return dataHandle;

    const avatar = scope.querySelector?.('[data-testid^="UserAvatar-Container-"]');
    const avatarId = avatar?.getAttribute('data-testid') || '';
    const avatarHandle = avatarId.match(/^UserAvatar-Container-([A-Za-z0-9_]{1,15})$/)?.[1];
    if (avatarHandle) return avatarHandle;

    const action = scope.querySelector?.('[aria-label*="@"]');
    const actionHandle = action?.getAttribute('aria-label')?.match(/@([A-Za-z0-9_]{1,15})\b/)?.[1];
    if (actionHandle) return actionHandle;

    const aboutLink = scope.querySelector?.('a[href^="/"][href$="/about"]');
    const aboutHandle = aboutLink?.getAttribute('href')?.match(/^\/([A-Za-z0-9_]{1,15})\/about$/)?.[1];
    if (aboutHandle) return aboutHandle;

    const profileLink = [...(scope.querySelectorAll?.('a[href^="/"]') || [])].find(a => {
      const handle = a.getAttribute('href')?.match(/^\/([A-Za-z0-9_]{1,15})(?:\/(?:about|photo|with_replies|media|highlights|likes|verified_followers|following|followers))?$/)?.[1];
      return handle && !isReservedPathHandle(handle);
    });
    const profileHandle = profileLink?.getAttribute('href')?.match(/^\/([A-Za-z0-9_]{1,15})(?:\/(?:about|photo|with_replies|media|highlights|likes|verified_followers|following|followers))?$/)?.[1];
    if (profileHandle) return profileHandle;

    const pathHandle = location.pathname.match(/^\/([A-Za-z0-9_]{1,15})(?:\/(?:with_replies|media|highlights|likes|about)?)?$/)?.[1];
    return pathHandle && !isReservedPathHandle(pathHandle) ? pathHandle : null;
  }

  function profileScopeForNode(node) {
    return node.closest?.('[role="dialog"]')
      || node.closest?.('[data-testid="primaryColumn"]')
      || node.closest?.('[data-testid="cellInnerDiv"]')
      || node;
  }

  function pushProfileNodeFacts(node, facts) {
    if (!node || !facts) return;
    facts.texts.push(getTextWithEmoji(node) || node.textContent || '');
    node.querySelectorAll?.('a,span').forEach(el => {
      facts.texts.push(el.textContent, el.getAttribute('title'), el.getAttribute('aria-label'));
      facts.links.push(el.getAttribute('href'));
    });
  }

  const PROFILE_FACT_SELECTOR = '[data-testid="UserProfileHeader_Items"],[data-testid="UserDescription"],[data-testid="UserName"]';

  function extractProfileFactsFromDom(scope) {
    const facts = { texts: [], links: [] };
    const nodes = new Set();
    if (scope.matches?.(PROFILE_FACT_SELECTOR)) nodes.add(scope);
    scope.querySelectorAll?.(PROFILE_FACT_SELECTOR).forEach(n => nodes.add(n));
    nodes.forEach(node => pushProfileNodeFacts(node, facts));
    return facts;
  }

  function captureReferralAccountsFromProfileDom(root = document) {
    const scopes = new Set();
    const captured = new Set();
    root.querySelectorAll?.(PROFILE_FACT_SELECTOR).forEach(node => {
      scopes.add(node);
      scopes.add(profileScopeForNode(node));
    });
    if (root.matches?.(PROFILE_FACT_SELECTOR)) {
      scopes.add(root);
      scopes.add(profileScopeForNode(root));
    }

    scopes.forEach(scope => {
      const handle = extractHandleFromProfileDom(scope);
      if (!handle) return;
      const links = referralLinksFromProfileFacts(extractProfileFactsFromDom(scope));
      if (links.length) {
        rememberReferralAccount(handle, links, { allowNegative: false });
        captured.add(normalizeHandle(handle));
      }
    });
    return [...captured];
  }

  function inspectReferralProfileDom(root = document) {
    const scopes = new Set();
    root.querySelectorAll?.(PROFILE_FACT_SELECTOR).forEach(node => {
      scopes.add(node);
      scopes.add(profileScopeForNode(node));
    });
    if (root.matches?.(PROFILE_FACT_SELECTOR)) {
      scopes.add(root);
      scopes.add(profileScopeForNode(root));
    }

    return [...scopes].map((scope, index) => {
      const facts = extractProfileFactsFromDom(scope);
      const text = profileReferralRuleText(facts);
      const links = facts.links.filter(Boolean);
      const referralLinks = referralLinksFromProfileFacts(facts);
      const handle = normalizeHandle(extractHandleFromProfileDom(scope));
      return {
        index,
        handle,
        hasIntent: profileHasReferralIntent(facts),
        referralLinks,
        text,
        links,
        node: scope.matches?.(PROFILE_FACT_SELECTOR)
          ? scope.getAttribute('data-testid')
          : scope.getAttribute?.('data-testid') || scope.getAttribute?.('role') || scope.tagName,
      };
    });
  }

  function cachedReferralAccount(handle) {
    const key = normalizeHandle(handle);
    const item = referralCache.get(key);
    if (!item) return null;
    if (Date.now() - item.ts >= REFERRAL_CACHE_TTL) {
      referralCache.delete(key);
      saveReferralCache();
      return null;
    }
    return materializeReferralItem(item);
  }

  function referralLookupQueryIds() {
    return [...new Set([userLookupQueryId, ...USER_LOOKUP_QUERY_ID_FALLBACKS].filter(Boolean))];
  }

  function referralRequestHeaders(csrf) {
    return {
      ...(capturedApiHeaders || {}),
      authorization: `Bearer ${liveBearer || BEARER}`,
      'x-csrf-token': csrf,
      'content-type': 'application/json',
      'x-twitter-active-user': 'yes',
      'x-twitter-auth-type': capturedApiHeaders?.['x-twitter-auth-type'] || 'OAuth2Session',
    };
  }

  function makeReferralError(message, status = 0, retryAfterMs = 0) {
    const e = new Error(message);
    e.status = status;
    e.retryAfterMs = retryAfterMs;
    e.rateLimited = status === 429 || retryAfterMs > 0;
    return e;
  }

  function parseRetryAfterMs(headers) {
    const m = String(headers || '').match(/^retry-after:\s*([^\r\n]+)/im);
    if (!m) return 0;
    const raw = m[1].trim();
    const seconds = Number(raw);
    if (Number.isFinite(seconds)) return Math.max(0, seconds * 1000);
    const dateMs = Date.parse(raw);
    return Number.isFinite(dateMs) ? Math.max(0, dateMs - Date.now()) : 0;
  }

  function isReferralRateLimitError(e) {
    return !!(e && e.rateLimited);
  }

  function warnReferralLookupFailure(e) {
    if (referralWarned) return;
    referralWarned = true;
    if (isReferralRateLimitError(e)) {
      const ms = Math.max(referralCooldownRemaining(), e.retryAfterMs || 0, REFERRAL_RATE_LIMIT_COOLDOWN);
      showToast(`导流号查询触发限流，已暂停约 ${Math.ceil(ms / 60000)} 分钟`, true);
    } else {
      showToast('导流号查询失败：X API 暂不可用或限流', true);
    }
  }

  function requestReferralAccountWithQueryId(handle, queryId) {
    const csrf = getCsrf();
    if (!csrf) return Promise.reject(new Error('missing csrf'));
    const variables = {
      screen_name: handle,
      withGrokTranslatedBio: false,
    };
    const features = {
      hidden_profile_subscriptions_enabled: true,
      profile_label_improvements_pcf_label_in_post_enabled: true,
      responsive_web_profile_redirect_enabled: true,
      rweb_tipjar_consumption_enabled: true,
      verified_phone_label_enabled: false,
      subscriptions_verification_info_is_identity_verified_enabled: true,
      subscriptions_verification_info_verified_since_enabled: true,
      highlights_tweets_tab_ui_enabled: true,
      responsive_web_twitter_article_notes_tab_enabled: true,
      subscriptions_feature_can_gift_premium: true,
      creator_subscriptions_tweet_preview_api_enabled: true,
      responsive_web_graphql_skip_user_profile_image_extensions_enabled: false,
      responsive_web_graphql_timeline_navigation_enabled: true,
    };
    const params = new URLSearchParams({
      variables: JSON.stringify(variables),
      features: JSON.stringify(features),
      fieldToggles: JSON.stringify({ withAuxiliaryUserLabels: true, withPayments: false }),
    });
    return new Promise((resolve, reject) => {
      GM_xmlhttpRequest({
        method: 'GET',
        url: `https://x.com/i/api/graphql/${encodeURIComponent(queryId)}/UserByScreenName?${params.toString()}`,
        headers: referralRequestHeaders(csrf),
        anonymous: false,
        onload(resp) {
          if (resp.status < 200 || resp.status >= 300) {
            reject(makeReferralError(`HTTP ${resp.status}`, resp.status, parseRetryAfterMs(resp.responseHeaders)));
            return;
          }
          try {
            const data = JSON.parse(resp.responseText || '{}');
            captureReferralAccountsFromData(data);
            const userResult = data?.data?.user?.result;
            const legacy = userResult?.legacy;
            if (!legacy) throw new Error('missing user legacy');
            const urls = extractProfileReferralLinks(legacy, userProfileExtraTexts(userResult, key));
            rememberReferralAccount(handle, urls, { allowNegative: true, createdAt: createdAtFromProfile(legacy, userResult) });
            const remembered = cachedReferralAccount(handle);
            resolve({ isReferral: !!remembered?.isReferral, urls: remembered?.urls || urls });
          } catch (e) {
            reject(e);
          }
        },
        onerror() { reject(makeReferralError('Network error')); },
      });
    });
  }

  async function requestReferralAccount(handle) {
    let lastError = null;
    for (const queryId of referralLookupQueryIds()) {
      try {
        const result = await requestReferralAccountWithQueryId(handle, queryId);
        if (queryId !== userLookupQueryId) {
          userLookupQueryId = queryId;
          GM_setValue('user_lookup_query_id', userLookupQueryId);
        }
        return result;
      } catch (e) {
        lastError = e;
        if (isReferralRateLimitError(e)) throw e;
      }
    }
    throw lastError || new Error('referral lookup failed');
  }

  // ── Cross-tab coordinated referral lookup ────────────────────────────
  // Profile lookups are easy to rate-limit when many X tabs are open. Keep one
  // same-origin queue across tabs and share cooldown state through localStorage.
  const LS_LAST_REFERRAL_LOOKUP = 'xfs-last-referral-lookup';
  const LS_REFERRAL_COOLDOWN_UNTIL = 'xfs-referral-cooldown-until-v2';

  function referralCooldownRemaining() {
    const until = parseInt(localStorage.getItem(LS_REFERRAL_COOLDOWN_UNTIL) || '0', 10);
    return Math.max(0, until - Date.now());
  }

  function setReferralCooldown(ms) {
    if (!ms || ms <= 0) return;
    const next = Date.now() + ms;
    const cur = parseInt(localStorage.getItem(LS_REFERRAL_COOLDOWN_UNTIL) || '0', 10);
    if (next > cur) localStorage.setItem(LS_REFERRAL_COOLDOWN_UNTIL, String(next));
  }

  function rememberReferralFailure(key, e) {
    referralFailureCache.set(key, {
      ts: Date.now(),
      rateLimited: isReferralRateLimitError(e),
    });
  }

  function recentReferralFailure(key) {
    const item = referralFailureCache.get(key);
    if (!item) return false;
    if (Date.now() - item.ts > REFERRAL_FAILURE_TTL) {
      referralFailureCache.delete(key);
      return false;
    }
    return true;
  }

  async function referralRequestCoordinated(handle) {
    const run = async () => {
      const cooldown = referralCooldownRemaining();
      if (cooldown > 0) throw makeReferralError('referral lookup cooling down', 429, cooldown);

      const gap = REFERRAL_MIN_GAP + Math.floor(Math.random() * REFERRAL_JITTER);
      const elapsed = Date.now() - parseInt(localStorage.getItem(LS_LAST_REFERRAL_LOOKUP) || '0', 10);
      if (elapsed < gap) await sleep(gap - elapsed);
      localStorage.setItem(LS_LAST_REFERRAL_LOOKUP, String(Date.now()));

      try {
        return await requestReferralAccount(handle);
      } catch (e) {
        if (isReferralRateLimitError(e)) {
          setReferralCooldown(Math.max(e.retryAfterMs || 0, REFERRAL_RATE_LIMIT_COOLDOWN));
        }
        throw e;
      }
    };

    if (navigator.locks?.request) return navigator.locks.request('xfs-referral-lookup-lock', run);
    return run();
  }

  function fetchReferralAccount(handle, opts = {}) {
    const key = normalizeHandle(handle);
    if (!key) return Promise.reject(new Error('missing handle'));
    const cached = cachedReferralAccount(key);
    if (cached !== null && !(opts.forceRefresh && cached.isReferral === false)) return Promise.resolve(cached);
    const cooldown = referralCooldownRemaining();
    if (cooldown > 0) return Promise.reject(makeReferralError('referral lookup cooling down', 429, cooldown));
    if (!opts.forceRefresh && recentReferralFailure(key)) return Promise.reject(makeReferralError('recent referral lookup failure'));
    if (referralPending.has(key)) return referralPending.get(key);

    const promise = new Promise((resolve, reject) => {
      referralQueue.push({ handle, key, resolve, reject });
      processReferralQueue();
    });
    referralPending.set(key, promise);
    return promise;
  }

  async function processReferralQueue() {
    if (referralQueueActive || referralQueue.length === 0) return;
    const cooldown = referralCooldownRemaining();
    if (cooldown > 0) {
      clearTimeout(referralQueueTimer);
      referralQueueTimer = setTimeout(processReferralQueue, Math.min(cooldown + 250, REFERRAL_RATE_LIMIT_COOLDOWN));
      return;
    }
    referralQueueActive = true;
    const item = referralQueue.shift();
    try {
      const result = await referralRequestCoordinated(item.handle);
      item.resolve(result);
    } catch (e) {
      console.debug(`[XFS] referral lookup failed @${item.handle}:`, e);
      rememberReferralFailure(item.key, e);
      item.reject(e);
    } finally {
      referralPending.delete(item.key);
      referralQueueActive = false;
      referralQueueTimer = setTimeout(processReferralQueue, 0);
    }
  }

  function referralDebugSnapshot() {
    const firstArt = document.querySelectorAll('article[data-testid="tweet"]')[0] || null;
    const articles = [...document.querySelectorAll('article[data-testid="tweet"]')].map((art, index) => {
      const handle = normalizeHandle(art.dataset.xfsReferralHandle || extractHandleFromArticle(art));
      const cached = handle ? cachedReferralAccount(handle) : null;
      const displayName = handle ? extractDisplayNameFromArticle(art, handle) : '';
      return {
        index,
        isFirstArticle: art === firstArt,
        handle,
        displayName,
        referralIntentHint: handle ? referralIntentHints.get(handle) || '' : '',
        referralDataset: art.dataset.xfsReferralAccount || '',
        queued: art.dataset.xfsReferralQueued || '',
        cached,
        recentFailure: handle ? recentReferralFailure(handle) : false,
        text: stripInvisible((art.querySelector('[data-testid="tweetText"]')?.textContent || '').slice(0, 180)),
      };
    });
    const profileScopes = inspectReferralProfileDom(document);
    const domCapturedHandles = captureReferralAccountsFromProfileDom(document);
    const handles = [...new Set([
      ...articles.filter(a => !a.isFirstArticle).map(a => a.handle).filter(Boolean),
      ...domCapturedHandles,
    ])];
    const snapshot = {
      version: GM_info?.script?.version || '',
      href: location.href,
      path: location.pathname,
      referral: {
        cacheKey: REFERRAL_CACHE_KEY,
        cooldownMs: referralCooldownRemaining(),
        pending: [...referralPending.keys()],
        queue: referralQueue.map(item => item.key),
        queueActive: referralQueueActive,
        autoReferralDetectActive,
        hideReferralActive,
        youngAccountFilterActive,
        youngAccountCutoffMode,
        youngAccountMaxAgeDays,
        youngAccountCutoffDate,
        userLookupQueryId,
        hasCapturedApiHeaders: !!capturedApiHeaders,
      },
      handles,
      profileScopes,
      articles,
    };
    console.group('[XFS DEBUG] referral snapshot');
    console.log(snapshot);
    console.table(profileScopes.map(s => ({
      index: s.index,
      handle: s.handle,
      hasIntent: s.hasIntent,
      referralLinks: s.referralLinks.join(' | '),
      text: s.text.slice(0, 120),
    })));
    console.table(articles.map(a => ({
      index: a.index,
      first: a.isFirstArticle,
      handle: a.handle,
      name: a.displayName,
      hint: a.referralIntentHint,
      dataset: a.referralDataset,
      queued: a.queued,
      cached: a.cached ? `${a.cached.isReferral ? 'referral' : 'negative'} ${referralItemDescription(a.cached)}` : '',
      failure: a.recentFailure,
    })));
    console.groupEnd();
    copyText(JSON.stringify(snapshot, null, 2)).then(ok => {
      showToast(ok ? 'XFS debug 信息已复制' : 'XFS debug 已输出到 Console', !ok);
    });
    return snapshot;
  }

  async function referralDebugProbe(handle) {
    const key = normalizeHandle(handle);
    if (!key) {
      showToast('XFS debug: 缺少 handle', true);
      return null;
    }
    const before = cachedReferralAccount(key);
    const out = {
      handle: key,
      before,
      cooldownMs: referralCooldownRemaining(),
      recentFailure: recentReferralFailure(key),
      result: null,
      after: null,
      error: null,
    };
    try {
      out.result = await fetchReferralAccount(key, { forceRefresh: true });
    } catch (e) {
      out.error = {
        message: e?.message || String(e),
        status: e?.status || 0,
        retryAfterMs: e?.retryAfterMs || 0,
        rateLimited: !!e?.rateLimited,
      };
    }
    out.after = cachedReferralAccount(key);
    console.log('[XFS DEBUG] referral probe', out);
    copyText(JSON.stringify(out, null, 2)).then(ok => {
      showToast(ok ? `XFS debug @${key} 已复制` : `XFS debug @${key} 已输出到 Console`, !ok);
    });
    return out;
  }

  function exposeDebugTools() {
    const win = typeof unsafeWindow !== 'undefined' ? unsafeWindow : window;
    win.XFS_DEBUG = {
      referral: referralDebugSnapshot,
      probeReferral: referralDebugProbe,
      clearReferralState() {
        referralCache.clear();
        referralFailureCache.clear();
        referralPending.clear();
        referralQueue.length = 0;
        referralHintRefreshDone.clear();
        localStorage.removeItem(LS_REFERRAL_COOLDOWN_UNTIL);
        saveReferralCache();
        showToast('XFS referral cache/cooldown 已清空', false);
        return true;
      },
    };
  }

  // Strip Unicode Format-category characters (zero-width spaces, soft hyphens, etc.)
  // that bad actors insert between characters to defeat keyword matching.
  function stripInvisible(s) {
    return s
      .replace(/\r\n/g, '\n').replace(/\r/g, '\n')
      .replace(/\p{Cf}/gu, '')
      .replace(/^[ \t]+$/mg, ''); // collapse whitespace-only lines so \n+ spans them
  }

  function asciiLetterCount(s) {
    return (String(s).match(/[a-z]/gi) || []).length;
  }

  function getContextSnippets(text, keywords, len) {
    const hits = [];
    // Normalize: remove invisible format characters before matching so that
    // interleaved zero-width chars (U+200B, U+200D, U+FEFF, etc.) don't defeat indexOf.
    const clean = stripInvisible(text);
    const lower = clean.toLowerCase();
    // Pre-check: does this tweet contain any Chinese characters?
    // Short ASCII-only keywords (e.g. 'dd') only make sense as fraud signals inside
    // Chinese-language tweets. Longer ASCII phrases are explicit enough to stand alone.
    const textHasChinese = CHINESE_RE.test(clean);

    for (const kw of keywords) {
      const idx = lower.indexOf(kw.toLowerCase());
      if (idx < 0) continue;
      const isAsciiOnlyKw = !CHINESE_RE.test(kw);
      const isShortAsciiKw = isAsciiOnlyKw && asciiLetterCount(kw) <= 5;
      // Skip short ASCII-only keyword matches when no Chinese characters appear anywhere
      // in the tweet text; longer phrases like "big bro" are explicit enough.
      if (isShortAsciiKw && !textHasChinese) continue;
      // Prevent partial matches for short ASCII keywords (e.g. 'dd' inside 'daddy').
      // Require that the characters immediately surrounding the match are NOT ASCII
      // word characters — Chinese characters and spaces naturally satisfy this.
      if (isShortAsciiKw) {
        const ASCII_WORD_CHAR = /[a-z0-9_]/;
        const before = idx > 0 ? lower[idx - 1] : '';
        const after  = idx + kw.length < lower.length ? lower[idx + kw.length] : '';
        if (ASCII_WORD_CHAR.test(before) || ASCII_WORD_CHAR.test(after)) continue;
      }
      const s = Math.max(0, idx - len);
      const e = Math.min(clean.length, idx + kw.length + len);
      hits.push({ kw, snippet: (s > 0 ? '\u2026' : '') + clean.slice(s, e) + (e < clean.length ? '\u2026' : '') });
    }
    return hits;
  }

  // Compile and run a regex pattern string against text.
  // Flags: m (^ matches line start), u (Unicode). Returns hit objects like getContextSnippets.
  function getRegexHits(text, patterns, target = 'both') {
    const hits = [];
    for (const { pat, scope, re } of compiledRegexes(patterns)) {
      if (scope !== 'both' && target !== 'both' && scope !== target) continue;
      const m = re.exec(text);
      if (!m) continue;
      const idx = m.index;
      const s   = Math.max(0, idx - CTX_LEN);
      const e   = Math.min(text.length, idx + m[0].length + CTX_LEN);
      const raw = text.slice(s, e).replace(/\n/g, '↵');
      hits.push({ pat, snippet: (s > 0 ? '…' : '') + raw + (e < text.length ? '…' : '') });
    }
    return hits;
  }

  // ── Filter matcher (shared by scanPage and inline buttons) ───────────
  function matchesFilters(displayName, fullText) {
    displayName = stripInvisible(displayName);
    fullText    = stripInvisible(fullText);
    const heartHits  = [...new Set(displayName.match(HEART_RE) || [])];
    const nameKwHits = SUSPECT_NAME_KWS.filter(kw => stripInvisible(displayName).toLowerCase().includes(kw.toLowerCase()));
    const kwHits     = getContextSnippets(fullText, SUSPECT_KWS, CTX_LEN);
    const nameReHits = getRegexHits(displayName, SUSPECT_RE_KWS, 'name').map(h => ({ ...h, type: 'regex', snippet: `昵称: ${h.snippet}` }));
    const bodyReHits = getRegexHits(fullText, SUSPECT_RE_KWS, 'body').map(h => ({ ...h, type: 'regex' }));
    const reHits     = [...nameReHits, ...bodyReHits];
    const allHideOnlyReHits = getRegexHits(fullText, HIDE_ONLY_RE_KWS, 'body').map(h => ({ ...h, type: 'hide_only_regex' }));
    const hideOnlyReHits = hideOnlyRulesActive ? allHideOnlyReHits : [];
    const cats = new Set();
    const actionableCats = new Set();
    if (heartHits.length  > 0) cats.add('heart');
    if (nameKwHits.length > 0) cats.add('name_kw');
    if (kwHits.length     > 0) cats.add('suspect');
    if (reHits.length     > 0) cats.add('regex_kw');
    if (hideOnlyReHits.length > 0) cats.add('hide_only_regex');
    if (heartHits.length  > 0) actionableCats.add('heart');
    if (nameKwHits.length > 0) actionableCats.add('name_kw');
    if (kwHits.length     > 0) actionableCats.add('suspect');
    if (reHits.length     > 0) actionableCats.add('regex_kw');
    return {
      matched: cats.size > 0,
      actionableMatched: actionableCats.size > 0,
      hideOnlyMatched: hideOnlyReHits.length > 0,
      cats,
      actionableCats,
      heartHits,
      nameKwHits,
      kwHits,
      reHits,
      hideOnlyReHits,
      allHideOnlyReHits,
    };
  }

  function buildUserPreviewSnippet(...parts) {
    const clean = parts
      .map(part => stripInvisible(String(part || '')).trim())
      .find(Boolean) || '';
    if (!clean) return '';
    const words = clean.split(/\s+/).filter(Boolean);
    if (words.length > 1) {
      return words.slice(0, 18).join(' ') + (words.length > 18 ? '…' : '');
    }
    return clean.length > 90 ? `${clean.slice(0, 90)}…` : clean;
  }

  function normalizeQueuePreviewCats(cats) {
    const allowed = new Set(['heart', 'name_kw', 'suspect', 'regex_kw', 'hide_only_regex', 'referral', 'liker']);
    const list = Array.isArray(cats) ? cats : Array.from(cats || []);
    return list.map(v => String(v || '')).filter(v => allowed.has(v)).slice(0, 6);
  }

  function normalizeQueueKeywordHits(list) {
    return Array.isArray(list)
      ? list
        .map(hit => ({
          kw: String(hit?.kw || '').slice(0, 80),
          snippet: String(hit?.snippet || '').slice(0, 220),
        }))
        .filter(hit => hit.kw || hit.snippet)
        .slice(0, 4)
      : [];
  }

  function normalizeQueueRegexHits(list) {
    return Array.isArray(list)
      ? list
        .map(hit => ({
          pat: String(hit?.pat || '').slice(0, 160),
          snippet: String(hit?.snippet || '').slice(0, 220),
        }))
        .filter(hit => hit.pat || hit.snippet)
        .slice(0, 4)
      : [];
  }

  function clearRuleTestHighlights() {
    document.querySelectorAll('.xfs-rule-test-hit,.xfs-rule-test-name,.xfs-rule-test-content').forEach(el => {
      el.classList.remove('xfs-rule-test-hit', 'xfs-rule-test-name', 'xfs-rule-test-content');
    });
  }

  function ensureRuleTestStyle() {
    if (document.getElementById('xfs-rule-test-style')) return;
    const style = document.createElement('style');
    style.id = 'xfs-rule-test-style';
    style.textContent = `
      article.xfs-rule-test-hit {
        box-shadow: inset 4px 0 0 #f59e0b !important;
        background: rgba(245,158,11,0.08) !important;
      }
      .xfs-rule-test-name {
        outline: 2px solid #7b52ab !important;
        outline-offset: 2px !important;
        border-radius: 6px !important;
        background: rgba(123,82,171,0.12) !important;
      }
      .xfs-rule-test-content {
        outline: 2px solid #f4212e !important;
        outline-offset: 2px !important;
        border-radius: 6px !important;
        background: rgba(244,33,46,0.10) !important;
      }
    `;
    document.head.appendChild(style);
  }

  function compileRuleTestRegex(raw) {
    const value = String(raw || '').trim();
    if (!value) return null;
    const parsed = _regexPatternParts(value);
    const pat = parsed.pat || value;
    return new RegExp(pat, 'mu');
  }

  function articleRuleTestText(art) {
    const handle = extractHandleFromArticle(art);
    const displayName = extractDisplayNameFromArticle(art, handle) || handle || '';
    const textEl = art.querySelector('[data-testid="tweetText"]');
    const cardEl = art.querySelector('[data-testid="card.wrapper"]');
    const bodyLinkText = [
      ...(textEl ? [...textEl.querySelectorAll('a[href]')] : []),
      ...(cardEl  ? [...cardEl.querySelectorAll('a[href]')]  : []),
    ].map(a => a.textContent).join(' ');
    const fullText = [
      textEl ? getTextWithEmoji(textEl) : null,
      cardEl ? getTextWithEmoji(cardEl) : null,
      bodyLinkText,
    ].filter(Boolean).join(' ');
    return { displayName: stripInvisible(displayName), fullText: stripInvisible(fullText), textEl };
  }

  function runRuleTest(nameRaw, contentRaw) {
    let nameRe = null;
    let contentRe = null;
    try {
      nameRe = compileRuleTestRegex(nameRaw);
      contentRe = compileRuleTestRegex(contentRaw);
    } catch (e) {
      showToast(`测试正则错误：${e.message}`, true);
      return { scanned: 0, nameHits: 0, contentHits: 0, error: e.message };
    }
    clearRuleTestHighlights();
    ensureRuleTestStyle();
    let scanned = 0;
    let nameHits = 0;
    let contentHits = 0;
    let failed = 0;
    document.querySelectorAll('article[data-testid="tweet"]').forEach(art => {
      try {
        scanned += 1;
        const nameEl = art.querySelector('[data-testid="User-Name"]');
        const { displayName, fullText, textEl } = articleRuleTestText(art);
        const hitName = !!(nameRe && nameRe.test(displayName));
        const hitContent = !!(contentRe && contentRe.test(fullText));
        if (!hitName && !hitContent) return;
        art.classList.add('xfs-rule-test-hit');
        if (hitName) {
          nameHits += 1;
          nameEl?.classList.add('xfs-rule-test-name');
        }
        if (hitContent) {
          contentHits += 1;
          (textEl || art).classList.add('xfs-rule-test-content');
        }
      } catch (_) {
        failed += 1;
      }
    });
    return { scanned, nameHits, contentHits, failed, error: '' };
  }

  function runNameRuleTest(nameRaw) {
    return runRuleTest(nameRaw, '');
  }

  function runContentRuleTest(contentRaw) {
    return runRuleTest('', contentRaw);
  }

  function buildDefaultSuspectPresets() {
    return {
      content: ['线下', '真人', '主人', '附近的吗', 'dd', '搭子', '固炮', '蹲个', '在线找', '快来', 'big bro\'', 'big bro', 'big brother', 'little bro', '单男', '第一骚', '小m', '男大弟弟', 'pan.quark.cn', 'drive.uc.cn', 'pan.xunlei.com', '离得近的', '万达广场', '同城的哥哥', '⬆️', '🍓'],
      name: ['同城', '单身', '刺激', '母狗', '巨乳', '女大', '男大', '真人', '互关fo', '🅱️', '真实', '互关', '全国', '🍑', '🍆', '💯', '费破', '👠', '骚', '熟女', '单男', '少妇', '线下', '🍓', '💊', '约炮', '痒', '固炮', '免费', '无偿', '搭子', '反差', '护士', '高中生', '🌸🌸'],
      // Preset regex rules matched against display name and tweet body.
      regex: [
        '^@\\w+\\n+[⬆↑⇑]',
        '👉\\s*@\\w',
        '(?=[\\s\\S]*比[\\s\\S]{0,8}她)(?=[\\s\\S]*@[A-Za-z0-9_]{1,15}\\b)[\\s\\S]{1,280}',
        '(?=[\\s\\S]*比[\\s\\S]{0,8}她)(?=[\\s\\S]*@[A-Za-z0-9_]{1,15}\\b)(?=[\\s\\S]*(?:\\p{Extended_Pictographic}|\\p{Emoji_Presentation}))[\\s\\S]{1,280}',
        '(?=[\\s\\S]*不行了)(?=[\\s\\S]*@[A-Za-z0-9_]{1,15}\\b)[\\s\\S]{1,280}',
        '(?=[\\s\\S]*主页)(?=[\\s\\S]*@[A-Za-z0-9_]{1,15}\\b)(?=[\\s\\S]*(?:\\p{Extended_Pictographic}|\\p{Emoji_Presentation}))[\\s\\S]{1,280}',
        `(?:${NON_FACE_EMOJI_SRC}\\s*){3,}`,
        `(?:${DECOR_SYMBOL_RUN_SRC}\\s*(?:${NON_FACE_EMOJI_SRC}\\s*){2,}|(?:${NON_FACE_EMOJI_SRC}\\s*){2,}${DECOR_SYMBOL_RUN_SRC})`,
        '[\\u02B0-\\u02FF\\u1D2C-\\u1D7F\\u1D80-\\u1DBF\\u2070-\\u209F]{3,}',
      ],
    };
  }

  const HIDE_RULE_STATS_KEY = 'hide_rule_hit_stats_v1';
  const HIDE_RULE_TYPE_LABELS = {
    name: '用户名关键词',
    content: '内容关键词',
    regex: '正则',
    hide_only_regex: '只隐藏正则',
    referral_profile_regex: '导流号主页正则',
  };
  const RULE_ID_PREFIX = {
    content: 'keyword',
    name: 'name',
    regex: 'regex',
    hide_only_regex: 'hide-re',
    referral_profile_regex: 'profile-re',
  };

  function ruleId(type, idx) {
    return `${RULE_ID_PREFIX[type] || type}-${idx + 1}`;
  }

  function ruleListForType(type) {
    if (type === 'content') return SUSPECT_KWS;
    if (type === 'name') return SUSPECT_NAME_KWS;
    if (type === 'regex') return SUSPECT_RE_KWS;
    if (type === 'hide_only_regex') return HIDE_ONLY_RE_KWS;
    if (type === 'referral_profile_regex') return REFERRAL_PROFILE_RE_KWS;
    return [];
  }

  function currentRuleId(type, key) {
    const idx = ruleListForType(type).findIndex(item => String(item).trim() === String(key || '').trim());
    return idx >= 0 ? ruleId(type, idx) : '';
  }

  function ruleTitle(type, idx, value) {
    return `ID: ${ruleId(type, idx)}\n${value}`;
  }

  function statsRuleLabel(type, key) {
    const id = currentRuleId(type, key);
    if (type === 'regex' || type === 'hide_only_regex') return id || regexRuleLabel(key, type);
    return id ? `${id} · ${key}` : key;
  }

  function statsRuleTitle(type, key) {
    const id = currentRuleId(type, key);
    return id ? `ID: ${id}\n${key}` : key;
  }

  function hideRuleStatItems(matchInfo) {
    const seen = new Set();
    const out = [];
    const add = (type, key) => {
      const value = String(key || '').trim();
      const id = `${type}\n${value}`;
      if (!value || seen.has(id)) return;
      seen.add(id);
      out.push({ type, key: value });
    };
    (matchInfo.nameKwHits || []).forEach(kw => add('name', kw));
    (matchInfo.kwHits || []).forEach(hit => add('content', hit.kw));
    (matchInfo.reHits || []).forEach(hit => add('regex', hit.pat));
    (matchInfo.hideOnlyReHits || []).forEach(hit => add('hide_only_regex', hit.pat));
    return out;
  }

  function setArticleHideRuleStats(art, matchInfo) {
    const items = hideRuleStatItems(matchInfo);
    if (items.length) art.dataset.xfsHideRuleStats = JSON.stringify(items);
    else delete art.dataset.xfsHideRuleStats;
  }

  function isMainTweetArticle(art) {
    if (!art || !/\/status\/\d/.test(location.pathname) || isListPage()) return false;
    return art === document.querySelector('article[data-testid="tweet"]');
  }

  function clearMainTweetXfsState(art) {
    if (!art) return;
    art.dataset.xfsHideMatched = '0';
    art.dataset.xfsReferralAccount = '0';
    delete art.dataset.xfsBlocked;
    delete art.dataset.xfsHideRuleStats;
    delete art.dataset.xfsHideStatsRecorded;
    clearBlockedArticleStyle(art);
    art.querySelectorAll?.('[data-testid="User-Name"] a').forEach(a => a.style.removeProperty('text-decoration'));
    if (art.dataset.xfsHidden === '1') {
      art.dataset.xfsHidden = '';
      ['max-height','min-height','overflow','padding','margin-top','margin-bottom','pointer-events','border-bottom']
        .forEach(p => art.style.removeProperty(p));
    }
  }

  function clearProtectedVerifiedArticleState(art) {
    if (!art) return;
    const handle = normalizeHandle(art.dataset.xfsReferralHandle || extractHandleFromArticle(art));
    const isBlocked = handle && blockedHandles.has(handle);
    art.dataset.xfsHideMatched = '0';
    art.dataset.xfsReferralAccount = '0';
    art.dataset.xfsReferralQueued = '0';
    if (isBlocked) art.dataset.xfsBlocked = '1';
    else delete art.dataset.xfsBlocked;
    delete art.dataset.xfsHideRuleStats;
    delete art.dataset.xfsHideStatsRecorded;
    clearBlockedArticleStyle(art);
    if (isBlocked) applyBlockedArticleStyle(art);
    if (art.dataset.xfsHidden === '1') {
      art.dataset.xfsHidden = '';
      ['max-height','min-height','overflow','padding','margin-top','margin-bottom','pointer-events','border-bottom']
        .forEach(p => art.style.removeProperty(p));
    }
    if (handle) {
      matchedHandlesInView.delete(handle);
      matchedUsersCache.delete(handle);
    }
    art.querySelectorAll?.('button[data-xfs-handle]').forEach(btn => {
      btn.dataset.xfsMatched = '0';
      btn.dataset.xfsHideOnlyMatched = '0';
      btn.dataset.xfsReferralAccount = '0';
      delete btn.dataset.xfsMatchTooltip;
      delete btn.dataset.xfsHideOnlyTooltip;
      delete btn.dataset.xfsReferralTooltip;
      updateInlineBlockButton(btn);
    });
  }

  function clearProtectedVerifiedArticlesInView() {
    document.querySelectorAll('article[data-testid="tweet"]').forEach(art => {
      if (isProtectedVerifiedArticle(art)) clearProtectedVerifiedArticleState(art);
    });
    updateHideBadge();
    updateReferralBadge();
  }

  function loadHideRuleStats() {
    const raw = GM_getValue(HIDE_RULE_STATS_KEY, {});
    return raw && typeof raw === 'object' && !Array.isArray(raw) ? raw : {};
  }

  function incrementHideRuleStatsFromArticle(art) {
    if (art.dataset.xfsHideStatsRecorded === '1') return;
    let items = [];
    try { items = JSON.parse(art.dataset.xfsHideRuleStats || '[]'); } catch (_) {}
    if (!Array.isArray(items) || items.length === 0) return;
    const stats = loadHideRuleStats();
    items.forEach(item => {
      const type = item?.type;
      const key = String(item?.key || '').trim();
      if (!type || !key) return;
      const id = `${type}\n${key}`;
      const prev = stats[id] && typeof stats[id] === 'object' ? stats[id] : {};
      stats[id] = { type, key, count: Math.max(0, Number(prev.count || 0)) + 1, updatedAt: Date.now() };
    });
    GM_setValue(HIDE_RULE_STATS_KEY, stats);
    art.dataset.xfsHideStatsRecorded = '1';
  }

  // ── Page scanner ─────────────────────────────────────────────────────
  function scanPage() {
    reloadKws();
    const articles = document.querySelectorAll('article[data-testid="tweet"]');
    const userMap = new Map();

    articles.forEach(art => {
      if (isMainTweetArticle(art)) return;

      const nameEl = art.querySelector('[data-testid="User-Name"]');
      if (!nameEl) return;
      if (isProtectedVerifiedArticle(art)) {
        clearProtectedVerifiedArticleState(art);
        return;
      }

      const handle = extractHandleFromArticle(art);
      if (!handle) return;
      if (blockedHandles.has(normalizeHandle(handle))) return;

      const displayName = extractDisplayNameFromArticle(art, handle) || handle;

      const textEl = art.querySelector('[data-testid="tweetText"]');
      const tweetText = textEl ? getTextWithEmoji(textEl) : '';

      // X.com strips URLs from tweet body when rendered as a card preview.
      // Quark/UC links are often shown as card previews (stripped from tweet body text).
      // Collect link text ONLY from tweetText and card — NOT the whole article,
      // which includes profile links whose handles could false-match short keywords like 'dd'.
      const cardEl  = art.querySelector('[data-testid="card.wrapper"]');
      const cardText = cardEl ? getTextWithEmoji(cardEl) : '';
      const bodyLinkText = [
        ...(textEl ? [...textEl.querySelectorAll('a[href]')] : []),
        ...(cardEl  ? [...cardEl.querySelectorAll('a[href]')]  : []),
      ].map(a => a.textContent).join(' ');
      const fullText = [tweetText, cardText, bodyLinkText].filter(Boolean).join(' ');

      const { matched, actionableMatched, actionableCats, heartHits, nameKwHits, kwHits, reHits, hideOnlyReHits } = matchesFilters(displayName, fullText);
      setArticleHideRuleStats(art, { nameKwHits, kwHits, reHits, hideOnlyReHits });
      if (!matched) return;

      // First 10 words of tweet body — shown in panel for name/heart matches
      // to help users judge borderline cases without opening the tweet.
      const tweetSnippet = buildUserPreviewSnippet(tweetText, cardText, bodyLinkText);

      if (userMap.has(handle)) {
        const ex = userMap.get(handle);
        actionableCats.forEach(c => ex.cats.add(c));
        heartHits.forEach(h  => { if (!ex.heartHits.includes(h))              ex.heartHits.push(h); });
        nameKwHits.forEach(h => { if (!ex.nameKwHits.includes(h))             ex.nameKwHits.push(h); });
        kwHits.forEach(h     => { if (!ex.kwHits.find(x => x.kw  === h.kw))  ex.kwHits.push(h); });
        reHits.forEach(h     => { if (!ex.reHits.find(x => x.pat === h.pat)) ex.reHits.push(h); });
        hideOnlyReHits.forEach(h => { if (!ex.hideOnlyReHits.find(x => x.pat === h.pat)) ex.hideOnlyReHits.push(h); });
        // keep tweetSnippet from first encounter
      } else if (actionableMatched) {
        userMap.set(handle, { handle, displayName, cats: actionableCats, heartHits, nameKwHits, kwHits, reHits, hideOnlyReHits, tweetSnippet });
      }
    });

    return Array.from(userMap.values());
  }

  // ── Block API ─────────────────────────────────────────────────────────
  // GM_xmlhttpRequest keeps the call out of X.com's own fetch pipeline,
  // preventing any SPA-triggered page refresh on block success.
  function blockAuthError(message) {
    const err = new Error(message || 'Authentication lost');
    err.xfsAuthLost = true;
    return err;
  }

  function blockRateLimitError(message) {
    const err = new Error(message || 'Rate limited');
    err.xfsRateLimited = true;
    return err;
  }

  function isBlockAuthLostError(err) {
    return !!err?.xfsAuthLost || /\bHTTP\s*(?:401|403|419)\b|auth|login|logout|csrf|ct0/i.test(String(err?.message || err || ''));
  }

  function isBlockRateLimitError(err) {
    return !!err?.xfsRateLimited || /\bHTTP\s*429\b|rate.?limit|too many/i.test(String(err?.message || err || ''));
  }

  function blockHttpError(status, body = '') {
    const msg = `HTTP ${status}`;
    const n = Number(status);
    const err = [401, 403, 419].includes(n) ? blockAuthError(msg) : (n === 429 ? blockRateLimitError(msg) : new Error(msg));
    err.status = status;
    err.responseText = body;
    return err;
  }

  function pauseGlobalQueueForAuthLoss(reason = '登录状态失效') {
    setGlobalBlockQueuePaused(true, { reason: 'auth' });
    const q = readGlobalBlockQueue();
    Object.keys(q.items || {}).forEach(key => {
      const item = q.items[key];
      if (item?.status === 'running') q.items[key] = { ...item, status: 'queued', updatedAt: Date.now(), error: reason };
    });
    writeGlobalBlockQueue(q);
    updateGlobalBlockQueuePanel();
    refreshGlobalBlockQueueDetailPanel();
    refreshGlobalQueueInlineButtons();
    showToast(`拉黑排队已暂停：${reason}。请重新登录 X/Twitter 后再继续。`, true);
  }

  function pauseGlobalQueueForRateLimit(reason = '平台限流') {
    setGlobalBlockQueuePaused(true, { reason: 'rate_limit' });
    const q = readGlobalBlockQueue();
    Object.keys(q.items || {}).forEach(key => {
      const item = q.items[key];
      if (item?.status === 'running') q.items[key] = { ...item, status: 'queued', updatedAt: Date.now(), error: reason };
    });
    writeGlobalBlockQueue(q);
    updateGlobalBlockQueuePanel();
    refreshGlobalBlockQueueDetailPanel();
    refreshGlobalQueueInlineButtons();
    showToast(`拉黑排队已暂停：${reason}。不是继续加长固定间隔，而是先停住，等账号状态恢复后手动继续。`, true);
  }

  function readGlobalQueueRound() {
    const raw = GM_getValue(GLOBAL_BLOCK_QUEUE_ROUND_KEY, null);
    return {
      count: Math.max(0, Number(raw?.count || 0) || 0),
      reason: String(raw?.reason || ''),
      pausedAt: Number(raw?.pausedAt || 0) || 0,
      cooldownStartedAt: Number(raw?.cooldownStartedAt || 0) || 0,
      cooldownUntil: Number(raw?.cooldownUntil || 0) || 0,
    };
  }

  function writeGlobalQueueRound(round) {
    GM_setValue(GLOBAL_BLOCK_QUEUE_ROUND_KEY, {
      count: Math.max(0, Number(round?.count || 0) || 0),
      reason: String(round?.reason || ''),
      pausedAt: Number(round?.pausedAt || 0) || 0,
      cooldownStartedAt: Number(round?.cooldownStartedAt || 0) || 0,
      cooldownUntil: Number(round?.cooldownUntil || 0) || 0,
    });
  }

  function resetGlobalQueueRound() {
    writeGlobalQueueRound({ count: 0, reason: '', pausedAt: 0, cooldownStartedAt: 0, cooldownUntil: 0 });
  }

  function globalQueueCooldownForCount(count) {
    const timing = effectiveExperimentTimingConfig();
    if (!count) return null;
    if (count % GLOBAL_BLOCK_QUEUE_LONG_COOLDOWN_EVERY === 0) {
      return {
        ms: timing.longCooldownMs + humanizedBoundedDelay(GLOBAL_BLOCK_QUEUE_LONG_COOLDOWN_JITTER, {
          mode: 0.68,
          hesitationChance: 0.32,
          tailStart: 0.82,
        }),
        reason: `每 ${GLOBAL_BLOCK_QUEUE_LONG_COOLDOWN_EVERY} 个暂停`,
      };
    }
    if (count % GLOBAL_BLOCK_QUEUE_SHORT_COOLDOWN_EVERY === 0) {
      return {
        ms: timing.shortCooldownMs + humanizedBoundedDelay(GLOBAL_BLOCK_QUEUE_SHORT_COOLDOWN_JITTER, {
          mode: 0.58,
          hesitationChance: 0.2,
          tailStart: 0.76,
        }),
        reason: `每 ${GLOBAL_BLOCK_QUEUE_SHORT_COOLDOWN_EVERY} 个暂停`,
      };
    }
    return null;
  }

  function formatGlobalQueueCooldown(ms) {
    const sec = Math.max(0, Math.ceil(Number(ms || 0) / 1000));
    if (sec >= 60) {
      const min = Math.floor(sec / 60);
      const rest = sec % 60;
      return rest ? `${min}分${rest}秒` : `${min}分`;
    }
    return `${sec}秒`;
  }

  function globalQueueRoundText(round = readGlobalQueueRound()) {
    const remaining = Number(round.cooldownUntil || 0) - Date.now();
    return remaining > 0 ? `本轮 ${round.count} · 冷却 ${formatGlobalQueueCooldown(remaining)}` : `本轮 ${round.count}`;
  }

  async function coolDownGlobalBlockQueue(until, reason) {
    const round = readGlobalQueueRound();
    const cooldownUntil = Math.max(Date.now(), Number(until || 0));
    const cooldownStartedAt = Number(round.cooldownStartedAt || 0) || Date.now();
    writeGlobalQueueRound({ ...round, reason, cooldownStartedAt, cooldownUntil });
    updateGlobalBlockQueuePanel();
    refreshGlobalBlockQueueDetailPanel();
    refreshGlobalQueueInlineButtons();
    showToast(`拉黑排队冷却中：${reason}，约 ${formatGlobalQueueCooldown(cooldownUntil - Date.now())} 后自动继续`, false);
    while (!globalBlockQueuePaused()) {
      const latestRound = readGlobalQueueRound();
      const remaining = Number(latestRound.cooldownUntil || 0) - Date.now();
      if (remaining <= 0) break;
      heartbeatGlobalBlockQueueLock();
      updateGlobalBlockQueuePanel();
      await sleep(Math.min(1000, remaining));
    }
    const latest = readGlobalQueueRound();
    if (Number(latest.cooldownUntil || 0) <= Date.now()) {
      writeGlobalQueueRound({ ...latest, reason: '', cooldownStartedAt: 0, cooldownUntil: 0 });
      updateGlobalBlockQueuePanel();
      refreshGlobalBlockQueueDetailPanel();
    }
  }

  function blockUser(handle, csrf) {
    const bearer = liveBearer || BEARER;
    console.log(`[XFS] blocking @${handle} | live=${!!liveBearer} | csrf=${csrf ? csrf.slice(0,8)+'…' : 'MISSING'}`);
    return new Promise((resolve, reject) => {
      GM_xmlhttpRequest({
        method: 'POST',
        url: 'https://x.com/i/api/1.1/blocks/create.json',
        headers: {
          Authorization: `Bearer ${bearer}`,
          'x-csrf-token': csrf,
          'Content-Type': 'application/x-www-form-urlencoded',
          'x-twitter-active-user': 'yes',
          'x-twitter-auth-type': 'OAuth2Session',
        },
        data: `screen_name=${encodeURIComponent(handle)}`,
        anonymous: false,
        onload(resp) {
          if (resp.status >= 200 && resp.status < 300) {
            console.log(`[XFS] OK @${handle} =>`, resp.responseText.slice(0, 120));
            resolve();
          } else {
            console.error(`[XFS] FAILED @${handle} => HTTP ${resp.status}:`, resp.responseText.slice(0, 400));
            reject(blockHttpError(resp.status, resp.responseText || ''));
          }
        },
        onerror(e) {
          console.error(`[XFS] ERROR @${handle}:`, e);
          reject(new Error('Network error'));
        },
      });
    });
  }

  // ── Cross-tab coordinated block ──────────────────────────────────────
  // Uses navigator.locks (same-origin mutex across tabs) + localStorage timestamp
  // to guarantee the global inter-block gap is always >= BLOCK_DELAY, even when
  // multiple tabs are running block operations simultaneously.
  const LS_LAST_BLOCK = 'xfs-last-block';

  async function blockUserCoordinated(handle, csrf, shouldProceed, options = {}) {
    const slow = !!options.slow;
    const run = async () => {
      if (shouldProceed && !shouldProceed()) return { skipped: true };
      // Jitter is computed inside the lock so each block gets a fresh, bounded,
      // slightly humanized gap instead of a flat random interval.
      // localStorage timestamp reflects the actual gap used, so cross-tab
      // coordination sees the same effective rate regardless of which tab ran last.
      const jitter  = slow ? EXPERIMENT_BLOCK_JITTER : BLOCK_JITTER;
      const randomExtra = humanizedBoundedDelay(jitter, slow
        ? { mode: 0.52, hesitationChance: 0.22, tailStart: 0.74 }
        : { mode: 0.38, hesitationChance: 0.1, tailStart: 0.68 });
      const lastBlockAt = parseInt(localStorage.getItem(LS_LAST_BLOCK) || '0', 10);
      while (true) {
        const baseGap = slow ? effectiveExperimentTimingConfig().slowBlockDelayMs : BLOCK_DELAY;
        const remaining = lastBlockAt + baseGap + randomExtra - Date.now();
        if (remaining <= 0) break;
        if (shouldProceed && !shouldProceed()) return { skipped: true };
        await sleep(Math.min(1000, remaining));
      }
      if (shouldProceed && !shouldProceed()) return { skipped: true };
      localStorage.setItem(LS_LAST_BLOCK, String(Date.now()));
      await blockUser(handle, csrf);
      return { skipped: false };
    };
    return navigator.locks?.request ? navigator.locks.request('xfs-block-lock', run) : run();
  }

  function emptyGlobalBlockQueue() {
    return { version: 1, updatedAt: Date.now(), items: {} };
  }

  function emptyExperimentalBrowseBlockState() {
    return { enabled: false, activatedAt: 0, expiresAt: 0, heartbeatAt: 0, prevSkipVerified: null };
  }

  function readExperimentalBrowseBlockState() {
    const raw = GM_getValue(EXPERIMENT_BROWSE_BLOCK_KEY, null);
    const state = raw && typeof raw === 'object' ? raw : emptyExperimentalBrowseBlockState();
    return {
      enabled: !!state.enabled,
      activatedAt: Number(state.activatedAt || 0),
      expiresAt: Number(state.expiresAt || 0),
      heartbeatAt: Number(state.heartbeatAt || 0),
      prevSkipVerified: typeof state.prevSkipVerified === 'boolean' ? state.prevSkipVerified : null,
    };
  }

  function writeExperimentalBrowseBlockState(state) {
    GM_setValue(EXPERIMENT_BROWSE_BLOCK_KEY, {
      enabled: !!state.enabled,
      activatedAt: Number(state.activatedAt || 0),
      expiresAt: Number(state.expiresAt || 0),
      heartbeatAt: Number(state.heartbeatAt || 0),
      prevSkipVerified: typeof state.prevSkipVerified === 'boolean' ? state.prevSkipVerified : null,
    });
  }

  function disableExperimentalBrowseBlock(reason = '', opts = {}) {
    const prev = readExperimentalBrowseBlockState().prevSkipVerified;
    writeExperimentalBrowseBlockState(emptyExperimentalBrowseBlockState());
    if (opts.restoreSettings !== false && typeof prev === 'boolean') {
      skipVerifiedAccountsActive = prev;
      GM_setValue('skip_verified_accounts', skipVerifiedAccountsActive);
    }
    if (experimentalBrowseBlockHeartbeatTimer) {
      clearInterval(experimentalBrowseBlockHeartbeatTimer);
      experimentalBrowseBlockHeartbeatTimer = null;
    }
    resetGlobalQueueRound();
    document.getElementById('xfs-experiment-panel')?.remove();
    removeExperimentKillSwitch();
    if (opts.hideQueuePanel) {
      globalQueuePanelSuppressed = true;
      document.getElementById('xfs-global-block-queue')?.remove();
    }
    reapplyContentRulesForVisible();
    injectInlineButtons();
    updateGlobalBlockQueuePanel();
    if (reason) showToast(reason, false);
  }

  function experimentalBrowseBlockActive() {
    const state = readExperimentalBrowseBlockState();
    if (!state.enabled) return false;
    const now = Date.now();
    if (state.expiresAt <= now) {
      disableExperimentalBrowseBlock('边刷边拉黑已自动关闭：超过 24 小时');
      return false;
    }
    if (state.heartbeatAt && now - state.heartbeatAt > EXPERIMENT_BROWSE_BLOCK_HEARTBEAT_STALE) {
      disableExperimentalBrowseBlock('边刷边拉黑已自动关闭：新的浏览周期');
      return false;
    }
    return true;
  }

  function enableExperimentalBrowseBlock() {
    const now = Date.now();
    clearProtectedVerifiedArticlesInView();
    globalQueuePanelSuppressed = false;
    writeExperimentalBrowseBlockState({
      enabled: true,
      activatedAt: now,
      expiresAt: now + EXPERIMENT_BROWSE_BLOCK_MAX_AGE,
      heartbeatAt: now,
      prevSkipVerified: skipVerifiedAccountsActive,
    });
    skipVerifiedAccountsActive = true;
    GM_setValue('skip_verified_accounts', true);
    resetGlobalQueueRound();
    startExperimentalBrowseBlockHeartbeat();
    updateGlobalBlockQueuePanel();
    injectExperimentKillSwitch();
    buttonsCollapsed = false;
    GM_setValue('buttons_collapsed', false);
    injectBtn();
    reapplyContentRulesForVisible();
    injectInlineButtons();
    flushMatchedUsersCacheToBrowseQueue();
    showToast(`边刷边拉黑已开启：慢速排队 ${experimentSlowBlockGapText()}，会员保护已强制开启`, false);
  }

  function startExperimentalBrowseBlockHeartbeat() {
    if (experimentalBrowseBlockHeartbeatTimer) clearInterval(experimentalBrowseBlockHeartbeatTimer);
    if (!experimentalBrowseBlockActive()) return;
    const current = readExperimentalBrowseBlockState();
    current.heartbeatAt = Date.now();
    writeExperimentalBrowseBlockState(current);
    experimentalBrowseBlockHeartbeatTimer = setInterval(() => {
      const state = readExperimentalBrowseBlockState();
      if (!state.enabled || state.expiresAt <= Date.now()) {
        disableExperimentalBrowseBlock(state.enabled ? '边刷边拉黑已自动关闭：超过 24 小时' : '');
        return;
      }
      state.heartbeatAt = Date.now();
      writeExperimentalBrowseBlockState(state);
    }, 30000);
  }

  function maybeAutoQueueBrowseMatchedUser(user, sourceArticle) {
    if (!experimentalBrowseBlockActive()) return;
    const key = normalizeHandle(user?.handle);
    if (!key || blockedHandles.has(key) || globalBlockQueueItemForHandle(key)) return;
    if (sourceArticle && isProtectedVerifiedArticle(sourceArticle)) return;
    const result = autoQueueBlockUsers([{ ...user, handle: key, source: 'browse_auto' }], { queueSource: 'browse_auto' });
    if (result.added || result.aiReview) {
      sourceArticle?.setAttribute?.('data-xfs-auto-queued', '1');
      showToast(`边刷边拉黑：@${key} 已加入拉黑排队`, false);
    }
  }

  function flushMatchedUsersCacheToBrowseQueue() {
    if (!experimentalBrowseBlockActive() || !matchedUsersCache.size) return;
    const users = Array.from(matchedUsersCache.values())
      .map(user => {
        const key = normalizeHandle(user?.handle);
        return key ? { ...user, handle: key, source: 'browse_auto' } : null;
      })
      .filter(user => user && !blockedHandles.has(user.handle) && !globalBlockQueueItemForHandle(user.handle) && !isProtectedVerifiedHandle(user.handle));
    if (!users.length) return;
    const result = autoQueueBlockUsers(users, { queueSource: 'browse_auto' });
    if (result.added) showToast(`边刷边拉黑：已补入队 ${result.added} 个已扫到账号`, false);
  }

  function readGlobalBlockQueue() {
    const raw = GM_getValue(GLOBAL_BLOCK_QUEUE_KEY, null);
    const q = raw && typeof raw === 'object' && !Array.isArray(raw) ? raw : emptyGlobalBlockQueue();
    const items = q.items && typeof q.items === 'object' && !Array.isArray(q.items) ? q.items : {};
    return { version: 1, updatedAt: Number(q.updatedAt || 0) || Date.now(), items };
  }

  function writeGlobalBlockQueue(q) {
    const items = q.items && typeof q.items === 'object' ? q.items : {};
    const done = Object.values(items)
      .filter(item => ['done', 'failed', 'skipped'].includes(item?.status))
      .sort((a, b) => Number(b.updatedAt || 0) - Number(a.updatedAt || 0));
    const keepDone = new Set(done.slice(0, GLOBAL_BLOCK_QUEUE_DONE_MAX).map(item => normalizeHandle(item.handle)));
    Object.keys(items).forEach(key => {
      const item = items[key];
      if (['done', 'failed', 'skipped'].includes(item?.status) && !keepDone.has(normalizeHandle(item.handle))) delete items[key];
    });
    GM_setValue(GLOBAL_BLOCK_QUEUE_KEY, { version: 1, updatedAt: Date.now(), items });
  }

  function readGlobalBlockHistory() {
    const raw = GM_getValue(GLOBAL_BLOCK_HISTORY_KEY, null);
    const items = raw?.items && typeof raw.items === 'object' && !Array.isArray(raw.items) ? raw.items : {};
    return { version: 1, updatedAt: Number(raw?.updatedAt || 0) || Date.now(), items };
  }

  function writeGlobalBlockHistory(history) {
    const items = history.items && typeof history.items === 'object' ? history.items : {};
    const ordered = Object.values(items)
      .filter(item => item && normalizeHandle(item.handle))
      .sort((a, b) => Number(b.blockedAt || b.updatedAt || 0) - Number(a.blockedAt || a.updatedAt || 0));
    const keep = new Set(ordered.slice(0, GLOBAL_BLOCK_HISTORY_MAX).map(item => normalizeHandle(item.handle)));
    Object.keys(items).forEach(key => {
      if (!keep.has(normalizeHandle(key))) delete items[key];
    });
    GM_setValue(GLOBAL_BLOCK_HISTORY_KEY, { version: 1, updatedAt: Date.now(), items });
  }

  function archiveGlobalBlockedItem(item) {
    const key = normalizeHandle(item?.handle);
    if (!key) return;
    const history = readGlobalBlockHistory();
    history.items[key] = {
      ...history.items[key],
      ...item,
      handle: key,
      status: 'done',
      blockedAt: Number(item.blockedAt || item.updatedAt || Date.now()),
      archivedAt: Date.now(),
      updatedAt: Number(item.updatedAt || Date.now()),
    };
    writeGlobalBlockHistory(history);
  }

  function globalBlockHistoryItems() {
    return Object.values(readGlobalBlockHistory().items || {})
      .filter(item => item && normalizeHandle(item.handle))
      .sort((a, b) => Number(b.blockedAt || b.updatedAt || 0) - Number(a.blockedAt || a.updatedAt || 0));
  }

  function globalBlockQueueItems(q = readGlobalBlockQueue()) {
    return Object.values(q.items || {}).filter(item => item && normalizeHandle(item.handle));
  }

  function globalBlockQueueItemForHandle(handle) {
    const key = normalizeHandle(handle);
    return key ? readGlobalBlockQueue().items[key] || null : null;
  }

  function globalBlockQueueSummary(q = readGlobalBlockQueue()) {
    const items = globalBlockQueueItems(q);
    const counts = { queued: 0, running: 0, done: 0, failed: 0, skipped: 0, total: items.length };
    items.forEach(item => {
      const status = item.status || 'queued';
      if (counts[status] == null) counts[status] = 0;
      counts[status] += 1;
    });
    const current = items
      .filter(item => item.status === 'running')
      .sort((a, b) => Number(b.updatedAt || 0) - Number(a.updatedAt || 0))[0] || null;
    return { counts, current };
  }

  const GLOBAL_QUEUE_STATUS_LABELS = {
    queued: '排队',
    running: '执行中',
    done: '完成',
    failed: '失败',
    skipped: '跳过',
  };

  function globalQueueStatusCat(status) {
    if (status === 'running') return 'name_kw';
    if (status === 'done') return 'liker';
    if (status === 'failed') return 'regex_kw';
    return 'suspect';
  }

  function globalQueueShowDone() {
    return !!GM_getValue(GLOBAL_BLOCK_QUEUE_SHOW_DONE_KEY, false);
  }

  function setGlobalQueueShowDone(show) {
    GM_setValue(GLOBAL_BLOCK_QUEUE_SHOW_DONE_KEY, !!show);
    refreshGlobalBlockQueueDetailPanel();
  }

  function globalQueueUsersForPanel(q = readGlobalBlockQueue()) {
    const rank = { running: 0, queued: 1, failed: 2, skipped: 3, done: 4 };
    const showDone = globalQueueShowDone();
    return globalBlockQueueItems(q)
      .filter(item => showDone || !['done', 'skipped'].includes(item.status || 'queued'))
      .sort((a, b) => (rank[a.status] ?? 9) - (rank[b.status] ?? 9) || Number(a.addedAt || 0) - Number(b.addedAt || 0))
      .map(item => {
        const status = item.status || 'queued';
        const label = GLOBAL_QUEUE_STATUS_LABELS[status] || status;
        const detail = [
          item.source ? `来源 ${item.source}` : '',
          item.aiDecision ? `AI ${item.aiDecision}${item.aiConfidence ? ` ${Math.round(Number(item.aiConfidence) * 100)}%` : ''}` : '',
          item.aiReason ? `AI理由 ${item.aiReason}` : '',
          item.attempts ? `尝试 ${item.attempts}` : '',
          item.error ? `错误 ${item.error}` : '',
        ].filter(Boolean).join(' · ');
        const ruleSummary = queueMatchSummaryText({
          cats: new Set(normalizeQueuePreviewCats(item.previewCats)),
          heartHits: Array.isArray(item.heartHits) ? item.heartHits : [],
          nameKwHits: Array.isArray(item.nameKwHits) ? item.nameKwHits : [],
          kwHits: normalizeQueueKeywordHits(item.kwHits),
          reHits: normalizeQueueRegexHits(item.reHits),
          hideOnlyReHits: normalizeQueueRegexHits(item.hideOnlyReHits),
        });
        const aiSummary = item.aiDecision
          ? `AI ${item.aiDecision}${item.aiConfidence ? ` ${Math.round(Number(item.aiConfidence) * 100)}%` : ''}${item.aiReason ? ` · ${item.aiReason}` : ''}`
          : 'AI 未参与';
        const previewCats = normalizeQueuePreviewCats(item.previewCats);
        return {
          handle: normalizeHandle(item.handle),
          displayName: item.displayName || item.handle,
          cats: new Set(previewCats),
          queueRowCat: globalQueueStatusCat(status),
          heartHits: Array.isArray(item.heartHits) ? item.heartHits.map(v => String(v || '')).filter(Boolean).slice(0, 6) : [],
          nameKwHits: Array.isArray(item.nameKwHits) ? item.nameKwHits.map(v => String(v || '')).filter(Boolean).slice(0, 6) : [],
          kwHits: normalizeQueueKeywordHits(item.kwHits),
          reHits: normalizeQueueRegexHits(item.reHits),
          hideOnlyReHits: normalizeQueueRegexHits(item.hideOnlyReHits),
          tweetSnippet: String(item.tweetSnippet || item.reason || ''),
          queueStatus: status,
          queueStatusLabel: label,
          queueStatusDetail: detail || `加入时间 ${new Date(Number(item.addedAt || Date.now())).toLocaleTimeString()}`,
          queueRuleSummary: ruleSummary,
          queueAiSummary: aiSummary,
          queueUpdatedAt: Number(item.updatedAt || 0),
        };
      })
      .concat(showDone ? globalBlockHistoryItems()
        .filter(item => !q.items?.[normalizeHandle(item.handle)])
        .map(item => ({
          handle: normalizeHandle(item.handle),
          displayName: item.displayName || item.handle,
          cats: new Set(normalizeQueuePreviewCats(item.previewCats)),
          queueRowCat: 'liker',
          heartHits: Array.isArray(item.heartHits) ? item.heartHits.map(v => String(v || '')).filter(Boolean).slice(0, 6) : [],
          nameKwHits: Array.isArray(item.nameKwHits) ? item.nameKwHits.map(v => String(v || '')).filter(Boolean).slice(0, 6) : [],
          kwHits: normalizeQueueKeywordHits(item.kwHits),
          reHits: normalizeQueueRegexHits(item.reHits),
          hideOnlyReHits: normalizeQueueRegexHits(item.hideOnlyReHits),
          tweetSnippet: String(item.tweetSnippet || item.reason || ''),
          queueStatus: 'done',
          queueStatusLabel: '历史已屏蔽',
          queueStatusDetail: `屏蔽时间 ${new Date(Number(item.blockedAt || item.updatedAt || Date.now())).toLocaleString()}`,
          queueRuleSummary: queueMatchSummaryText({
            cats: new Set(normalizeQueuePreviewCats(item.previewCats)),
            heartHits: Array.isArray(item.heartHits) ? item.heartHits : [],
            nameKwHits: Array.isArray(item.nameKwHits) ? item.nameKwHits : [],
            kwHits: normalizeQueueKeywordHits(item.kwHits),
            reHits: normalizeQueueRegexHits(item.reHits),
            hideOnlyReHits: normalizeQueueRegexHits(item.hideOnlyReHits),
          }),
          queueAiSummary: item.aiDecision
            ? `AI ${item.aiDecision}${item.aiConfidence ? ` ${Math.round(Number(item.aiConfidence) * 100)}%` : ''}${item.aiReason ? ` · ${item.aiReason}` : ''}`
            : 'AI 未参与',
          queueUpdatedAt: Number(item.blockedAt || item.updatedAt || 0),
        }))
        : []);
  }

  function showGlobalBlockQueueDetailPanel(forceOpen = true, q = null) {
    if (!forceOpen && globalBlockQueueMinimized()) {
      const panel = document.getElementById('xfs-panel');
      if (panel?.dataset.xfsGlobalQueueView === '1') panel.remove();
      updateGlobalBlockQueuePanel();
      return;
    }
    globalQueuePanelSuppressed = false;
    GM_setValue(GLOBAL_BLOCK_QUEUE_MINIMIZED_KEY, false);
    document.getElementById('xfs-global-block-queue')?.remove();
    showPanel(globalQueueUsersForPanel(q || readGlobalBlockQueue()), { globalQueueView: true, precheck: false });
  }

  function refreshGlobalBlockQueueDetailPanel(q = null) {
    const panel = document.getElementById('xfs-panel');
    if (globalBlockQueueMinimized()) {
      if (panel?.dataset.xfsGlobalQueueView === '1') panel.remove();
      updateGlobalBlockQueuePanel();
      return;
    }
    if (panel?.dataset.xfsGlobalQueueView === '1') showGlobalBlockQueueDetailPanel(false, q);
  }

  function recoverStaleGlobalBlockQueueItems(q = readGlobalBlockQueue()) {
    const now = Date.now();
    let changed = false;
    Object.keys(q.items || {}).forEach(key => {
      const item = q.items[key];
      if (item?.status === 'running' && now - Number(item.updatedAt || 0) > GLOBAL_BLOCK_QUEUE_LOCK_TTL * 2) {
        q.items[key] = { ...item, status: 'queued', updatedAt: now, error: 'worker expired' };
        changed = true;
      } else if (item?.status === 'failed' && now - Number(item.updatedAt || 0) > GLOBAL_BLOCK_QUEUE_FAILED_RETRY_MS) {
        q.items[key] = { ...item, status: 'queued', updatedAt: now, error: '' };
        changed = true;
      }
    });
    if (changed) writeGlobalBlockQueue(q);
    return q;
  }

  function enqueueGlobalBlockUsers(users, source = 'manual') {
    const now = Date.now();
    const q = readGlobalBlockQueue();
    let added = 0;
    let existing = 0;
    let skipped = 0;
    const manualish = ['manual', 'panel', 'inline'].includes(String(source || 'manual'));
    (users || []).forEach(user => {
      const key = normalizeHandle(user?.handle || user);
      if (!key || blockedHandles.has(key) || isProtectedVerifiedHandle(key) || (!manualish && isAiExemptHandle(key))) {
        skipped += 1;
        return;
      }
      if (manualish) forgetAiExemptHandle(key);
      const preview = {
        displayName: String(user?.displayName || user?.handle || key),
        reason: String(user?.reason || user?.tweetSnippet || ''),
        tweetSnippet: String(user?.tweetSnippet || user?.reason || ''),
        previewCats: normalizeQueuePreviewCats(user?.cats),
        heartHits: Array.isArray(user?.heartHits) ? user.heartHits.map(v => String(v || '')).filter(Boolean).slice(0, 6) : [],
        nameKwHits: Array.isArray(user?.nameKwHits) ? user.nameKwHits.map(v => String(v || '')).filter(Boolean).slice(0, 6) : [],
        kwHits: normalizeQueueKeywordHits(user?.kwHits),
        reHits: normalizeQueueRegexHits(user?.reHits),
        hideOnlyReHits: normalizeQueueRegexHits(user?.hideOnlyReHits),
        aiDecision: String(user?.aiDecision || ''),
        aiReason: String(user?.aiReason || ''),
        aiConfidence: Number(user?.aiConfidence || 0),
      };
      const prev = q.items[key];
      if (prev && ['queued', 'running'].includes(prev.status)) {
        existing += 1;
        q.items[key] = {
          ...prev,
          displayName: prev.displayName || preview.displayName,
          source: prev.source || source,
          reason: prev.reason || preview.reason,
          tweetSnippet: prev.tweetSnippet || preview.tweetSnippet,
          previewCats: Array.isArray(prev.previewCats) && prev.previewCats.length ? prev.previewCats : preview.previewCats,
          heartHits: Array.isArray(prev.heartHits) && prev.heartHits.length ? prev.heartHits : preview.heartHits,
          nameKwHits: Array.isArray(prev.nameKwHits) && prev.nameKwHits.length ? prev.nameKwHits : preview.nameKwHits,
          kwHits: Array.isArray(prev.kwHits) && prev.kwHits.length ? prev.kwHits : preview.kwHits,
          reHits: Array.isArray(prev.reHits) && prev.reHits.length ? prev.reHits : preview.reHits,
          hideOnlyReHits: Array.isArray(prev.hideOnlyReHits) && prev.hideOnlyReHits.length ? prev.hideOnlyReHits : preview.hideOnlyReHits,
          aiDecision: prev.aiDecision || preview.aiDecision,
          aiReason: prev.aiReason || preview.aiReason,
          aiConfidence: Number.isFinite(Number(prev.aiConfidence)) ? Number(prev.aiConfidence) : preview.aiConfidence,
          updatedAt: now,
        };
        return;
      }
      if (prev && prev.status === 'done') {
        existing += 1;
        return;
      }
      q.items[key] = {
        handle: key,
        displayName: preview.displayName,
        source,
        reason: preview.reason,
        tweetSnippet: preview.tweetSnippet,
        previewCats: preview.previewCats,
        heartHits: preview.heartHits,
        nameKwHits: preview.nameKwHits,
        kwHits: preview.kwHits,
        reHits: preview.reHits,
        hideOnlyReHits: preview.hideOnlyReHits,
        aiDecision: preview.aiDecision,
        aiReason: preview.aiReason,
        aiConfidence: preview.aiConfidence,
        status: 'queued',
        attempts: Math.max(0, Number(prev?.attempts || 0)),
        addedAt: Number(prev?.addedAt || now),
        updatedAt: now,
        error: '',
      };
      added += 1;
    });
    writeGlobalBlockQueue(q);
    if (added && globalBlockQueuePaused() && !globalBlockQueuePauseReason() && getCsrf()) {
      setGlobalBlockQueuePaused(false);
    }
    ensureGlobalBlockQueuePanel();
    updateGlobalBlockQueuePanel();
    refreshGlobalBlockQueueDetailPanel();
    maybeStartGlobalBlockQueueWorker();
    return { added, existing, skipped, total: added + existing + skipped };
  }

  function autoQueueBlockUsers(users, opts = {}) {
    const safeUsers = (users || []).filter(user => !isProtectedVerifiedHandle(user?.handle || user));
    const source = opts.queueSource || 'auto';
    const useAiReview = aiReviewConfigured() && source !== 'manual' && source !== 'panel' && source !== 'inline';
    const directUsers = [];
    const reviewUsers = [];
    safeUsers.forEach(user => {
      if (!user) return;
      if (isAiHiddenHandle(user?.handle || '') || isAiExemptHandle(user?.handle || '')) return;
      if (!useAiReview || isNameIssueMatch(user)) directUsers.push(user);
      else reviewUsers.push(user);
    });
    const result = enqueueGlobalBlockUsers(directUsers, source);
    if (reviewUsers.length) {
      queueAiReviewUsers(reviewUsers, opts);
    }
    refreshGlobalQueueInlineButtons();
    result.aiDirect = directUsers.length;
    result.aiReview = reviewUsers.length;
    const msg = useAiReview && reviewUsers.length
      ? `已加入拉黑排队 ${result.added} 个${result.existing ? `，已有 ${result.existing} 个` : ''}${reviewUsers.length ? `，AI复核 ${reviewUsers.length} 个` : ''}${result.skipped ? `，跳过 ${result.skipped} 个` : ''}`
      : `已加入拉黑排队 ${result.added} 个${result.existing ? `，已有 ${result.existing} 个` : ''}${result.skipped ? `，跳过 ${result.skipped} 个` : ''}`;
    if (result.added || result.existing || result.skipped || (useAiReview && reviewUsers.length)) showToast(msg, false);
    if (result.added || result.existing || reviewUsers.length) markCleanupButtonsComplete(opts.refreshButtonIds);
    opts.onBlockDone?.({ queued: result.added, existing: result.existing, skipped: result.skipped, aiReview: reviewUsers.length, total: safeUsers.length });
    return result;
  }

  function globalBlockQueuePaused() {
    return !!GM_getValue(GLOBAL_BLOCK_QUEUE_PAUSED_KEY, false);
  }

  function globalBlockQueuePauseReason() {
    return String(GM_getValue(GLOBAL_BLOCK_QUEUE_PAUSE_REASON_KEY, '') || '');
  }

  function globalBlockQueueMinimized() {
    return !!GM_getValue(GLOBAL_BLOCK_QUEUE_MINIMIZED_KEY, true);
  }

  function setGlobalBlockQueueMinimized(minimized) {
    GM_setValue(GLOBAL_BLOCK_QUEUE_MINIMIZED_KEY, !!minimized);
    globalQueuePanelSuppressed = false;
    if (minimized) {
      const panel = document.getElementById('xfs-panel');
      if (panel?.dataset.xfsGlobalQueueView === '1') panel.remove();
      updateGlobalBlockQueuePanel();
    } else {
      document.getElementById('xfs-global-block-queue')?.remove();
      showGlobalBlockQueueDetailPanel();
    }
  }

  function readGlobalBlockQueuePosition() {
    const raw = GM_getValue(GLOBAL_BLOCK_QUEUE_POS_KEY, null);
    if (!raw || typeof raw !== 'object') return { left: 0, top: 53 };
    return {
      left: Math.max(0, Number(raw.left) || 0),
      top: Math.max(0, Number(raw.top) || 53),
    };
  }

  function writeGlobalBlockQueuePosition(pos) {
    GM_setValue(GLOBAL_BLOCK_QUEUE_POS_KEY, {
      left: Math.max(0, Math.round(Number(pos.left) || 0)),
      top: Math.max(0, Math.round(Number(pos.top) || 53)),
    });
  }

  function setGlobalBlockQueuePaused(paused, opts = {}) {
    if (!paused && !opts.keepRound) resetGlobalQueueRound();
    GM_setValue(GLOBAL_BLOCK_QUEUE_PAUSED_KEY, !!paused);
    GM_setValue(GLOBAL_BLOCK_QUEUE_PAUSE_REASON_KEY, paused ? String(opts.reason || 'manual') : '');
    updateGlobalBlockQueuePanel();
    refreshGlobalBlockQueueDetailPanel();
    if (!paused) maybeStartGlobalBlockQueueWorker();
  }

  function clearCompletedGlobalBlockQueue() {
    const q = readGlobalBlockQueue();
    Object.keys(q.items).forEach(key => {
      if (['done', 'failed', 'skipped'].includes(q.items[key]?.status)) delete q.items[key];
    });
    writeGlobalBlockQueue(q);
    updateGlobalBlockQueuePanel();
    refreshGlobalBlockQueueDetailPanel(q);
  }

  function clearDoneGlobalBlockQueue() {
    const q = readGlobalBlockQueue();
    let removed = 0;
    Object.keys(q.items).forEach(key => {
      if (q.items[key]?.status === 'done') {
        delete q.items[key];
        removed += 1;
      }
    });
    if (!removed) return 0;
    writeGlobalBlockQueue(q);
    updateGlobalBlockQueuePanel();
    refreshGlobalBlockQueueDetailPanel(q);
    return removed;
  }

  function clearGlobalBlockQueue() {
    const q = readGlobalBlockQueue();
    let removed = 0;
    let running = 0;
    Object.keys(q.items).forEach(key => {
      const status = q.items[key]?.status || 'queued';
      if (status === 'running') {
        running += 1;
        return;
      }
      delete q.items[key];
      removed += 1;
    });
    if (removed) {
      writeGlobalBlockQueue(q);
      updateGlobalBlockQueuePanel();
      refreshGlobalBlockQueueDetailPanel();
      refreshGlobalQueueInlineButtons();
    }
    return { removed, running };
  }

  function removeGlobalBlockQueueItem(handle) {
    const key = normalizeHandle(handle);
    if (!key) return { ok: false, reason: 'invalid' };
    const q = readGlobalBlockQueue();
    const item = q.items[key];
    if (!item) return { ok: false, reason: 'missing' };
    if ((item.status || 'queued') === 'running') return { ok: false, reason: 'running' };
    delete q.items[key];
    writeGlobalBlockQueue(q);
    updateGlobalBlockQueuePanel();
    refreshGlobalBlockQueueDetailPanel();
    return { ok: true, status: item.status || 'queued' };
  }

  function retryGlobalBlockQueueItem(handle) {
    const key = normalizeHandle(handle);
    if (!key) return { ok: false, reason: 'invalid' };
    const q = readGlobalBlockQueue();
    const item = q.items[key];
    if (!item) return { ok: false, reason: 'missing' };
    if ((item.status || 'queued') === 'running') return { ok: false, reason: 'running' };
    q.items[key] = {
      ...item,
      status: 'queued',
      error: '',
      updatedAt: Date.now(),
    };
    writeGlobalBlockQueue(q);
    updateGlobalBlockQueuePanel();
    refreshGlobalBlockQueueDetailPanel(q);
    refreshGlobalQueueInlineButtons();
    maybeStartGlobalBlockQueueWorker();
    return { ok: true };
  }

  function tryAcquireGlobalBlockQueueLock() {
    const now = Date.now();
    const cur = GM_getValue(GLOBAL_BLOCK_QUEUE_LOCK_KEY, null);
    if (cur?.tabId && cur.tabId !== globalQueueTabId && Number(cur.expiresAt || 0) > now) return false;
    GM_setValue(GLOBAL_BLOCK_QUEUE_LOCK_KEY, { tabId: globalQueueTabId, heartbeatAt: now, expiresAt: now + GLOBAL_BLOCK_QUEUE_LOCK_TTL });
    const next = GM_getValue(GLOBAL_BLOCK_QUEUE_LOCK_KEY, null);
    return next?.tabId === globalQueueTabId;
  }

  function heartbeatGlobalBlockQueueLock() {
    const now = Date.now();
    const cur = GM_getValue(GLOBAL_BLOCK_QUEUE_LOCK_KEY, null);
    if (cur?.tabId !== globalQueueTabId) return false;
    GM_setValue(GLOBAL_BLOCK_QUEUE_LOCK_KEY, { tabId: globalQueueTabId, heartbeatAt: now, expiresAt: now + GLOBAL_BLOCK_QUEUE_LOCK_TTL });
    return true;
  }

  function releaseGlobalBlockQueueLock() {
    const cur = GM_getValue(GLOBAL_BLOCK_QUEUE_LOCK_KEY, null);
    if (cur?.tabId === globalQueueTabId) GM_setValue(GLOBAL_BLOCK_QUEUE_LOCK_KEY, null);
  }

  function markHandleBlockedFromQueue(handle) {
    const key = normalizeHandle(handle);
    if (!key) return;
    blockedHandles.add(handle);
    blockedHandles.add(key);
    matchedHandlesInView.delete(handle);
    matchedHandlesInView.delete(key);
    matchedUsersCache.delete(handle);
    matchedUsersCache.delete(key);
    updateHideBadge();
    dimArticlesByHandle(handle);
    updateReferralBadge();
    document.querySelectorAll('button[data-xfs-handle]').forEach(b => {
      if (normalizeHandle(b.dataset.xfsHandle) !== key) return;
      const bMatched = b.dataset.xfsMatched === '1';
      b.dataset.xfsState = 'blocked';
      b.disabled = false;
      b.textContent = IBTN_CHECK_SVG;
      b.style.border = `1.5px solid ${C.mute}`;
      b.style.color = C.mute;
      b.style.boxShadow = '';
      b.style.background = `${C.mute}18`;
      b.style.opacity = '1';
      b.title = (bMatched ? '[匹配过滤] ' : '') + `已拉黑 · 点击取消 @${handle}`;
      updateInlineBlockButton(b);
    });
  }

  function syncCompletedGlobalBlocksToThisTab() {
    globalBlockQueueItems()
      .filter(item => item.status === 'done')
      .forEach(item => {
        const key = normalizeHandle(item.handle);
        if (key && !blockedHandles.has(key)) markHandleBlockedFromQueue(item.handle);
      });
  }

  function refreshGlobalQueueInlineButtons() {
    document.querySelectorAll('button[data-xfs-handle]').forEach(btn => {
      if (btn.dataset.xfsState !== 'blocked') updateInlineBlockButton(btn);
    });
  }

  async function processGlobalBlockQueue() {
    if (globalQueueWorkerActive || globalBlockQueuePaused()) return;
    if (!tryAcquireGlobalBlockQueueLock()) return;
    globalQueueWorkerActive = true;
    try {
      while (!globalBlockQueuePaused()) {
        if (!heartbeatGlobalBlockQueueLock()) break;
        const round = readGlobalQueueRound();
        if (Number(round.cooldownUntil || 0) > Date.now()) {
          await coolDownGlobalBlockQueue(round.cooldownUntil, round.reason || '队列冷却');
          if (globalBlockQueuePaused()) break;
        }
        const q = recoverStaleGlobalBlockQueueItems();
        const next = globalBlockQueueItems(q)
          .filter(item => item.status === 'queued')
          .sort((a, b) => Number(a.addedAt || 0) - Number(b.addedAt || 0))[0];
        if (!next) break;
        const key = normalizeHandle(next.handle);
        if (isAiExemptHandle(key)) {
          delete q.items[key];
          writeGlobalBlockQueue(q);
          updateGlobalBlockQueuePanel();
          refreshGlobalBlockQueueDetailPanel(q);
          continue;
        }
        const csrf = getCsrf();
        if (!csrf) {
          pauseGlobalQueueForAuthLoss('未找到登录凭证（ct0 cookie）');
          break;
        }
        q.items[key] = { ...next, status: 'running', workerTab: globalQueueTabId, attempts: Number(next.attempts || 0) + 1, updatedAt: Date.now(), error: '' };
        writeGlobalBlockQueue(q);
        updateGlobalBlockQueuePanel();
        refreshGlobalQueueInlineButtons();
        try {
          await blockUserCoordinated(next.handle, csrf, null, {
            slow: experimentalBrowseBlockActive() || next.source === 'browse_auto',
          });
          const fresh = readGlobalBlockQueue();
          fresh.items[key] = { ...fresh.items[key], status: 'done', updatedAt: Date.now(), blockedAt: Date.now(), error: '' };
          archiveGlobalBlockedItem(fresh.items[key]);
          writeGlobalBlockQueue(fresh);
          if (['manual', 'panel', 'inline'].includes(String(next.source || ''))) {
            recordAiLearningExample({
              handle: next.handle,
              displayName: next.displayName || '',
              source: next.source || 'manual',
            }, 'block', {
              source: next.source || 'manual',
              reason: next.reason || 'manual block',
              fingerprint: aiReviewFingerprint(next),
            });
          }
          incrementPersistentBlockedCount(1);
          markHandleBlockedFromQueue(next.handle);
          const nextRoundCount = readGlobalQueueRound().count + 1;
          writeGlobalQueueRound({ count: nextRoundCount, reason: '', pausedAt: 0, cooldownUntil: 0 });
          refreshGlobalBlockQueueDetailPanel();
          const cooldown = globalQueueCooldownForCount(nextRoundCount);
          if (cooldown) {
            await coolDownGlobalBlockQueue(Date.now() + cooldown.ms, cooldown.reason);
            if (globalBlockQueuePaused()) break;
          }
        } catch (e) {
          if (isBlockAuthLostError(e)) {
            pauseGlobalQueueForAuthLoss(e?.message || '登录状态失效');
            console.warn(`[XFS] global queue paused due to auth loss @${next.handle}:`, e);
            break;
          }
          if (isBlockRateLimitError(e)) {
            pauseGlobalQueueForRateLimit(e?.message || '平台限流');
            console.warn(`[XFS] global queue paused due to rate limit @${next.handle}:`, e);
            break;
          }
          const fresh = readGlobalBlockQueue();
          fresh.items[key] = { ...fresh.items[key], status: 'failed', updatedAt: Date.now(), error: e?.message || String(e || 'failed') };
          writeGlobalBlockQueue(fresh);
          refreshGlobalBlockQueueDetailPanel();
          refreshGlobalQueueInlineButtons();
          console.warn(`[XFS] global queue block @${next.handle} failed:`, e);
        }
        updateGlobalBlockQueuePanel();
      }
    } finally {
      globalQueueWorkerActive = false;
      releaseGlobalBlockQueueLock();
      updateGlobalBlockQueuePanel();
    }
  }

  function maybeStartGlobalBlockQueueWorker() {
    if (globalQueueWorkerActive || globalBlockQueuePaused()) return;
    const q = recoverStaleGlobalBlockQueueItems();
    const hasQueued = globalBlockQueueItems(q).some(item => item.status === 'queued');
    if (hasQueued) setTimeout(processGlobalBlockQueue, 0);
  }

  // ── Unblock API ───────────────────────────────────────────────────────
  function unblockUser(handle, csrf) {
    const bearer = liveBearer || BEARER;
    return new Promise((resolve, reject) => {
      GM_xmlhttpRequest({
        method: 'POST',
        url: 'https://x.com/i/api/1.1/blocks/destroy.json',
        headers: {
          Authorization: `Bearer ${bearer}`,
          'x-csrf-token': csrf,
          'Content-Type': 'application/x-www-form-urlencoded',
          'x-twitter-active-user': 'yes',
          'x-twitter-auth-type': 'OAuth2Session',
        },
        data: `screen_name=${encodeURIComponent(handle)}`,
        anonymous: false,
        onload(resp) {
          if (resp.status >= 200 && resp.status < 300) resolve();
          else reject(new Error(`HTTP ${resp.status}`));
        },
        onerror() { reject(new Error('Network error')); },
      });
    });
  }

  function shouldHideBlockedArticles() {
    return hideMatchedActive || hideReferralActive;
  }

  function applyBlockedArticleStyle(art) {
    if (!art || shouldHideBlockedArticles()) return;
    art.style.transition = 'opacity 0.3s';
    art.style.setProperty('opacity', '0.4', 'important');
  }

  function clearBlockedArticleStyle(art) {
    if (!art) return;
    art.style.removeProperty('opacity');
    art.style.removeProperty('transition');
  }

  // ── Visual feedback: dim articles belonging to a blocked handle ──────
  function dimArticlesByHandle(handle) {
    document.querySelectorAll('article[data-testid="tweet"]').forEach(art => {
      if (isMainTweetArticle(art)) {
        clearMainTweetXfsState(art);
        return;
      }
      if (isProtectedVerifiedArticle(art)) {
        clearProtectedVerifiedArticleState(art);
        return;
      }
      const nameEl = art.querySelector('[data-testid="User-Name"]');
      if (!nameEl) return;
      let isMatch = false;
      for (const sp of nameEl.querySelectorAll('span')) {
        if (normalizeHandle(sp.textContent.trim()) === normalizeHandle(handle)) { isMatch = true; break; }
      }
      if (!isMatch) return;
      art.dataset.xfsBlocked = '1';
      art.dataset.xfsHideMatched = '0';
      art.dataset.xfsReferralAccount = '0';
      // Strikethrough on the display name anchor (not the @handle).
      // setProperty with 'important' is required — X.com sets text-decoration:none on <a> elements.
      for (const a of nameEl.querySelectorAll('a')) {
        const txt = getTextWithEmoji(a).trim();
        if (txt && !txt.startsWith('@')) {
          a.style.setProperty('text-decoration', 'line-through', 'important');
          break;
        }
      }
      clearBlockedArticleStyle(art);
      if (shouldHideBlockedArticles()) applyHideToArticle(art);
      else applyBlockedArticleStyle(art);
    });
  }

  function undimArticlesByHandle(handle) {
    document.querySelectorAll('article[data-testid="tweet"]').forEach(art => {
      const nameEl = art.querySelector('[data-testid="User-Name"]');
      if (!nameEl) return;
      let isMatch = false;
      for (const sp of nameEl.querySelectorAll('span')) {
        if (normalizeHandle(sp.textContent.trim()) === normalizeHandle(handle)) { isMatch = true; break; }
      }
      if (!isMatch) return;
      delete art.dataset.xfsBlocked;
      for (const a of nameEl.querySelectorAll('a')) {
        const txt = getTextWithEmoji(a).trim();
        if (txt && !txt.startsWith('@')) { a.style.removeProperty('text-decoration'); break; }
      }
      clearBlockedArticleStyle(art);
      applyHideToArticle(art);
    });
  }

  // ── Panel UI ─────────────────────────────────────────────────────────
  // Light theme colors
  const C = {
    bg:        '#ffffff',
    border:    '#e1e8ed',
    text:      '#0f1419',
    sub:       '#536471',
    rowHover:  '#f7f9f9',
    catBg:     '#f7f9f9',
    heart:     '#e0245e',
    nameKw:    '#7b52ab',
    mute:      '#16a085',
    suspect:   '#b07d00',
    blockRed:  '#f4212e',
    btnBorder: '#cfd9de',
    regexKw:   '#0d7a8a',
    referral:  '#5f6f89',
    referralHot: '#f59e0b',
    hideOnlyHot: '#f2c14e',
  };

  const CAT_META = {
    heart:    { label: '心形 Emoji 用户名',  color: C.heart },
    name_kw:  { label: '用户名关键词',       color: C.nameKw },
    suspect:  { label: '可疑关键词',         color: C.suspect },
    regex_kw: { label: '正则匹配',           color: C.regexKw },
    hide_only_regex: { label: '只隐藏正则', color: C.mute },
    liker:    { label: '列表用户',           color: C.mute },
    referral: { label: '导流号',             color: C.referral },
  };

  function shortRuleHash(text) {
    let h = 2166136261;
    for (const ch of String(text || '')) {
      h ^= ch.codePointAt(0) || 0;
      h = Math.imul(h, 16777619);
    }
    return (h >>> 0).toString(36).slice(0, 6).toUpperCase();
  }

  function regexRuleLabel(pattern, type = 'regex') {
    const list = type === 'hide_only_regex' ? HIDE_ONLY_RE_KWS : SUSPECT_RE_KWS;
    const label = type === 'hide_only_regex' ? '只隐藏正则' : '正则';
    const idx = list.findIndex(pat => pat === pattern);
    return idx >= 0 ? `${label} ${idx + 1}` : `${label} ${shortRuleHash(pattern)}`;
  }

  function shortTooltipText(value, max = 120) {
    const text = String(value || '').replace(/\s+/g, ' ').trim();
    return text.length > max ? `${text.slice(0, max - 1)}…` : text;
  }

  function hitTooltipFromMatchInfo(matchInfo) {
    const lines = [];
    const add = line => {
      const text = shortTooltipText(line, 180);
      if (text && !lines.includes(text)) lines.push(text);
    };
    (matchInfo.heartHits || []).forEach(hit => add(`用户名心形: ${hit}`));
    (matchInfo.nameKwHits || []).forEach(kw => add(`用户名关键词: ${kw}`));
    (matchInfo.kwHits || []).forEach(hit => add(`内容关键词: ${hit.kw}${hit.snippet ? ` / ${hit.snippet}` : ''}`));
    (matchInfo.reHits || []).forEach(hit => add(`${regexRuleLabel(hit.pat, hit.type)}${hit.snippet ? `: ${hit.snippet}` : ''}`));
    (matchInfo.hideOnlyReHits || []).forEach(hit => add(`${regexRuleLabel(hit.pat, hit.type)}${hit.snippet ? `: ${hit.snippet}` : ''}`));
    return lines.slice(0, 8).join('\n');
  }

  function hitTooltipFromUser(user) {
    const lines = [];
    if (user?.cats?.has?.('referral')) {
      const ref = user.kwHits?.find?.(hit => hit.kw === '导流号' || hit.kw === '新号') || user.kwHits?.[0];
      lines.push(`${ref?.kw || '导流号'}: ${shortTooltipText(ref?.snippet || user.tweetSnippet || '账号主页规则命中')}`);
    }
    const matchText = hitTooltipFromMatchInfo(user || {});
    if (matchText) lines.push(matchText);
    return lines.join('\n');
  }

  function queueMatchSummaryText(user) {
    const parts = [];
    if (user?.cats?.has?.('referral')) parts.push('导流号');
    if ((user?.heartHits || []).length) parts.push(`用户名心形 ${user.heartHits.length}`);
    if ((user?.nameKwHits || []).length) parts.push(`用户名关键词 ${user.nameKwHits.length}`);
    if ((user?.kwHits || []).length) parts.push(`内容关键词 ${user.kwHits.length}`);
    if ((user?.reHits || []).length) parts.push(`正则 ${user.reHits.length}`);
    if ((user?.hideOnlyReHits || []).length) parts.push(`只隐藏正则 ${user.hideOnlyReHits.length}`);
    return parts.length ? `命中规则: ${parts.join(' / ')}` : '';
  }

  function showHideRuleStatsPanel() {
    document.getElementById('xfs-rule-stats-panel')?.remove();
    const stats = Object.values(loadHideRuleStats())
      .filter(item => item && item.key && Number(item.count) > 0)
      .sort((a, b) => Number(b.count || 0) - Number(a.count || 0));
    const total = stats.reduce((sum, item) => sum + Number(item.count || 0), 0);
    const max = Math.max(1, ...stats.map(item => Number(item.count || 0)));

    const panel = document.createElement('div');
    panel.id = 'xfs-rule-stats-panel';
    panel.style.cssText = [
      'position:fixed', 'left:50%', 'top:50%', 'transform:translate(-50%,-50%)',
      'width:min(760px, calc(100vw - 32px))',
      'max-height:min(78vh, 720px)', 'overflow:hidden',
      'background:rgba(255,255,255,0.98)', `color:${C.text}`,
      `border:1px solid ${C.border}`, 'border-radius:10px',
      'box-shadow:0 18px 50px rgba(0,0,0,0.25)',
      `font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif`,
      'z-index:2147483647',
      'display:flex', 'flex-direction:column',
    ].join(';');

    const hdr = document.createElement('div');
    hdr.style.cssText = `display:flex;align-items:center;gap:8px;padding:10px 12px;border-bottom:1px solid ${C.border};`;
    const title = document.createElement('div');
    title.textContent = `关键词命中统计 · ${formatBlockedCount(total)}`;
    title.style.cssText = 'flex:1;font-size:13px;font-weight:800;';
    const note = document.createElement('div');
    note.textContent = '本地统计，重复打开同一帖子会重复计数';
    note.style.cssText = `font-size:10px;color:${C.sub};`;
    const reset = document.createElement('button');
    reset.textContent = '清零';
    reset.style.cssText = `border:1px solid ${C.btnBorder};background:#fff;color:${C.sub};border-radius:7px;padding:3px 8px;font-size:11px;cursor:pointer;`;
    reset.onclick = () => {
      if (!window.confirm('清空关键词命中统计？')) return;
      GM_setValue(HIDE_RULE_STATS_KEY, {});
      panel.remove();
      showToast('关键词命中统计已清空', false);
    };
    const close = document.createElement('button');
    close.type = 'button';
    close.textContent = '×';
    close.style.cssText = `border:none;background:transparent;color:${C.sub};font-size:18px;line-height:1;cursor:pointer;padding:0 4px;`;
    close.onclick = () => panel.remove();
    hdr.appendChild(title);
    hdr.appendChild(note);
    hdr.appendChild(reset);
    hdr.appendChild(close);

    const body = document.createElement('div');
    body.style.cssText = 'overflow:auto;padding:10px 12px;display:flex;flex-direction:column;gap:6px;';
    if (stats.length === 0) {
      const empty = document.createElement('div');
      empty.textContent = '还没有统计数据。开启隐藏后，命中的关键词和正则会在这里累计。';
      empty.style.cssText = `padding:28px;text-align:center;color:${C.sub};font-size:12px;`;
      body.appendChild(empty);
    } else {
      stats.forEach(item => {
        const type = item.type || 'content';
        const color = type === 'name' ? C.nameKw : (type === 'regex' ? C.regexKw : (type === 'hide_only_regex' ? C.mute : C.suspect));
        const count = Number(item.count || 0);
        const row = document.createElement('div');
        row.style.cssText = `display:grid;grid-template-columns:86px minmax(0,1fr) 64px;gap:8px;align-items:center;font-size:11px;`;
        const typeEl = document.createElement('div');
        typeEl.textContent = HIDE_RULE_TYPE_LABELS[type] || type;
        typeEl.style.cssText = `color:${color};font-weight:700;white-space:nowrap;`;
        const mid = document.createElement('div');
        mid.style.cssText = 'min-width:0;';
        const key = document.createElement('div');
        key.textContent = statsRuleLabel(type, item.key);
        key.title = statsRuleTitle(type, item.key);
        key.style.cssText = 'overflow:hidden;text-overflow:ellipsis;white-space:nowrap;margin-bottom:3px;';
        const barWrap = document.createElement('div');
        barWrap.style.cssText = `height:7px;background:${C.border};border-radius:999px;overflow:hidden;`;
        const bar = document.createElement('div');
        bar.style.cssText = `height:100%;width:${Math.max(3, Math.round(count / max * 100))}%;background:${color};border-radius:999px;`;
        barWrap.appendChild(bar);
        mid.appendChild(key);
        mid.appendChild(barWrap);
        const countEl = document.createElement('div');
        countEl.textContent = formatBlockedCount(count);
        countEl.style.cssText = `text-align:right;color:${C.text};font-weight:800;font-variant-numeric:tabular-nums;`;
        row.appendChild(typeEl);
        row.appendChild(mid);
        row.appendChild(countEl);
        body.appendChild(row);
      });
    }

    panel.appendChild(hdr);
    panel.appendChild(body);
    document.body.appendChild(panel);
  }

  function readFloatingPanelPosition(key, fallback) {
    const raw = GM_getValue(key, null);
    if (!raw || typeof raw !== 'object') return fallback;
    return {
      left: Math.max(0, Number(raw.left) || fallback.left),
      top: Math.max(0, Number(raw.top) || fallback.top),
    };
  }

  function writeFloatingPanelPosition(key, pos) {
    GM_setValue(key, {
      left: Math.max(0, Math.round(Number(pos.left) || 0)),
      top: Math.max(0, Math.round(Number(pos.top) || 0)),
    });
  }

  function readFloatingPanelSize(key, fallback) {
    const raw = GM_getValue(key, null);
    if (!raw || typeof raw !== 'object') return fallback;
    return {
      width: Math.max(280, Number(raw.width) || fallback.width),
      height: Math.max(220, Number(raw.height) || fallback.height),
    };
  }

  function writeFloatingPanelSize(key, size) {
    GM_setValue(key, {
      width: Math.max(280, Math.round(Number(size.width) || 0)),
      height: Math.max(220, Math.round(Number(size.height) || 0)),
    });
  }

  function clampFloatingPanelPosition(pos, width, height) {
    return {
      left: Math.min(Math.max(0, Number(pos.left) || 0), Math.max(0, window.innerWidth - width - 8)),
      top: Math.min(Math.max(0, Number(pos.top) || 0), Math.max(0, window.innerHeight - height - 8)),
    };
  }

  function makeDraggableFloatingPanel(el, handle, storageKey, opts = {}) {
    handle.style.cursor = 'move';
    handle.onpointerdown = e => {
      if (e.button != null && e.button !== 0) return;
      if (e.target.closest('button,a,input,textarea,select')) return;
      e.preventDefault();
      const startX = e.clientX;
      const startY = e.clientY;
      const startLeft = el.offsetLeft;
      const startTop = el.offsetTop;
      el.setPointerCapture?.(e.pointerId);
      const applyPos = pos => {
        const w = opts.width?.() || el.offsetWidth || 190;
        const h = opts.height?.() || el.offsetHeight || 120;
        const next = clampFloatingPanelPosition(pos, w, h);
        el.style.left = `${next.left}px`;
        el.style.top = `${next.top}px`;
        el.style.right = 'auto';
        opts.onMove?.(next);
        return next;
      };
      const onMove = ev => applyPos({
        left: startLeft + ev.clientX - startX,
        top: startTop + ev.clientY - startY,
      });
      const onUp = ev => {
        el.releasePointerCapture?.(ev.pointerId);
        window.removeEventListener('pointermove', onMove);
        window.removeEventListener('pointerup', onUp);
        const finalPos = applyPos({ left: el.offsetLeft, top: el.offsetTop });
        writeFloatingPanelPosition(storageKey, finalPos);
        opts.onEnd?.(finalPos);
      };
      window.addEventListener('pointermove', onMove);
      window.addEventListener('pointerup', onUp, { once: true });
    };
  }

  function showPanel(allUsers, opts = {}) {
    document.getElementById('xfs-panel')?.remove();
    document.getElementById('xfs-panel-dock')?.remove();

    const isGlobalQueueView = !!opts.globalQueueView;
    if (opts.forceOpen !== false) {
      panelDockedActive = false;
      GM_setValue('panel_docked', false);
      document.getElementById('xfs-panel-dock')?.remove();
    }
    const panelUsers = isGlobalQueueView
      ? (allUsers || [])
      : (allUsers || []).filter(user => !isProtectedVerifiedHandle(user.handle));
    const topUsers = panelUsers.slice(0, MAX_BLOCK);
    const overflow = panelUsers.length - topUsers.length;

    // ── Build ordered list first (needed for adaptive width) ──
    function getPrimaryCat(u) {
      if (isGlobalQueueView && u.queueRowCat) return u.queueRowCat;
      if (u.cats.has('heart'))    return 'heart';
      if (u.cats.has('name_kw')) return 'name_kw';
      if (u.cats.has('referral')) return 'referral';
      if (u.cats.has('liker'))   return 'liker';
      if (u.cats.has('regex_kw')) return 'regex_kw';
      return 'suspect';
    }
    const ordered = [
      ...topUsers.filter(u => u.cats.has('heart')),
      ...topUsers.filter(u => !u.cats.has('heart') && u.cats.has('name_kw')),
      ...topUsers.filter(u => !u.cats.has('heart') && !u.cats.has('name_kw') && u.cats.has('referral')),
      ...topUsers.filter(u => !u.cats.has('heart') && !u.cats.has('name_kw') && !u.cats.has('referral')),
    ];

    // ── Adaptive column count & panel width ──
    // Estimate how many rows fit in one column based on viewport height.
    // ROW_H: conservative height covering both simple rows and suspect rows with context.
    const ROW_H = 34;
    const estBodyH = Math.max(200, window.innerHeight - 160); // 160 = top offset + hdr + kwBar + ftr
    const rowsPerCol = Math.max(6, Math.floor(estBodyH / ROW_H));
    const colsNeeded = ordered.length === 0 ? 2
      : Math.min(3, Math.max(2, Math.ceil(ordered.length / rowsPerCol)));
    const COL_W = 260;
    const panelW = colsNeeded * COL_W;
    const panelDefaultH = Math.min(Math.max(360, window.innerHeight - 110), Math.max(260, window.innerHeight - 16));
    const freeSize = isGlobalQueueView
      ? readFloatingPanelSize(GLOBAL_BLOCK_QUEUE_SIZE_KEY, {
        width: Math.min(Math.max(520, panelW), Math.max(360, window.innerWidth - 24)),
        height: panelDefaultH,
      })
      : null;
    const initialPanelW = freeSize ? Math.min(freeSize.width, Math.max(360, window.innerWidth - 16)) : panelW;
    const initialPanelH = freeSize ? Math.min(freeSize.height, Math.max(260, window.innerHeight - 16)) : 220;
    const panelPos = clampFloatingPanelPosition(
      isGlobalQueueView
        ? readGlobalBlockQueuePosition()
        : readFloatingPanelPosition(RESULT_PANEL_POS_KEY, { left: 0, top: 53 }),
      initialPanelW,
      initialPanelH
    );
    const panelPosKey = isGlobalQueueView ? GLOBAL_BLOCK_QUEUE_POS_KEY : RESULT_PANEL_POS_KEY;

    // Panel — flush left edge, adaptive width, semi-transparent
    const panel = document.createElement('div');
    panel.id = 'xfs-panel';
    if (isGlobalQueueView) panel.dataset.xfsGlobalQueueView = '1';
    panel.style.cssText = [
      'position:fixed', `left:${panelPos.left}px`, `top:${panelPos.top}px`,
      `width:${initialPanelW}px`, isGlobalQueueView ? `height:${initialPanelH}px` : `height:calc(100vh - ${panelPos.top}px)`,
      'background:rgba(255,255,255,0.93)',
      'backdrop-filter:blur(6px)',
      '-webkit-backdrop-filter:blur(6px)',
      isGlobalQueueView ? `border:1px solid ${C.border}` : `border-right:1px solid ${C.border}`,
      isGlobalQueueView ? 'border-radius:10px' : 'border-radius:0 10px 10px 0',
      isGlobalQueueView ? 'box-shadow:0 8px 28px rgba(0,0,0,0.16)' : 'box-shadow:4px 0 24px rgba(0,0,0,0.14)',
      'display:flex', 'flex-direction:column', 'overflow:hidden',
      isGlobalQueueView ? 'resize:both' : '',
      isGlobalQueueView ? 'min-width:360px' : '',
      isGlobalQueueView ? 'min-height:260px' : '',
      isGlobalQueueView ? 'max-width:calc(100vw - 16px)' : '',
      isGlobalQueueView ? 'max-height:calc(100vh - 16px)' : '',
      `font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif`,
      `font-size:12px`, `color:${C.text}`,
      'z-index:2147483646',
    ].join(';');

    // ── Header ──
    const hdr = document.createElement('div');
    hdr.style.cssText = `padding:6px 12px;border-bottom:1px solid ${C.border};display:flex;align-items:center;gap:8px;flex-shrink:0;`;
    makeDraggableFloatingPanel(panel, hdr, panelPosKey, {
      width: () => panel.offsetWidth || initialPanelW,
      height: () => panel.offsetHeight || initialPanelH,
      onMove: pos => {
        if (!isGlobalQueueView) panel.style.height = `calc(100vh - ${pos.top}px)`;
      },
      onEnd: () => {
        if (isGlobalQueueView) writeFloatingPanelSize(GLOBAL_BLOCK_QUEUE_SIZE_KEY, {
          width: panel.offsetWidth,
          height: panel.offsetHeight,
        });
        requestAnimationFrame(updateGlobalBlockQueuePanel);
      },
    });

    const title = document.createElement('span');
    title.textContent = '拉黑排队';
    title.style.cssText = 'font-size:13px;font-weight:700;flex:1;';

    const badge = document.createElement('span');
    let badgeAlert = overflow > 0;
    if (isGlobalQueueView) {
      const { counts } = globalBlockQueueSummary();
      const round = readGlobalQueueRound();
      badge.textContent = `${experimentalBrowseBlockActive() ? '边刷边拉黑 · ' : ''}排队 ${counts.queued} / 执行 ${counts.running} / 完成 ${counts.done} / 失败 ${counts.failed} / ${globalQueueRoundText(round)}`;
      badgeAlert = counts.failed > 0 || !!round.reason;
    } else {
      badge.textContent = overflow > 0 ? `候选 ${topUsers.length}/${panelUsers.length}，还有 ${overflow} 个` : `候选 ${topUsers.length} 个`;
    }
    badge.style.cssText = `font-size:11px;color:${badgeAlert ? C.blockRed : C.sub};`;

    const countBadge = document.createElement('span');
    countBadge.className = 'xfs-persistent-blocked-count';
    countBadge.textContent = `累计 ${formatBlockedCount(persistentBlockedCount)}`;
    countBadge.title = '仅供参考：这是 XFS 脚本累计成功拉黑数，不是 X 平台全部已拉黑账号数。只从该统计功能上线后开始记录，保存在本地，不受脚本更新影响。';
    countBadge.style.cssText = `font-size:10px;color:${C.mute};background:${C.mute}12;border:1px solid ${C.mute}55;border-radius:999px;padding:1px 6px;white-space:nowrap;`;

    const authDot = document.createElement('span');
    authDot.title = liveBearer ? 'Auth token captured from page' : 'Using fallback token';
    authDot.textContent = liveBearer ? 'auth ok' : 'auth?';
    authDot.style.cssText = `font-size:10px;padding:1px 5px;border-radius:8px;background:${liveBearer ? '#d4edda' : '#fff3cd'};color:${liveBearer ? '#155724' : '#856404'};`;

    const closeBtn = document.createElement('button');
    closeBtn.textContent = '\u00d7';
    closeBtn.style.cssText = `background:none;border:none;cursor:pointer;font-size:16px;color:${C.sub};padding:0 2px;line-height:1;`;
    closeBtn.onclick = () => isGlobalQueueView ? setGlobalBlockQueueMinimized(true) : panel.remove();

    const dockBtn = document.createElement('button');
    dockBtn.textContent = '收起';
    dockBtn.title = isGlobalQueueView ? '最小化拉黑排队' : '收起到左侧进度条';
    dockBtn.style.cssText = `background:#fff;border:1px solid ${C.btnBorder};border-radius:8px;cursor:pointer;font-size:10px;color:${C.sub};padding:1px 6px;white-space:nowrap;`;

    hdr.appendChild(title);
    hdr.appendChild(badge);
    hdr.appendChild(countBadge);
    hdr.appendChild(authDot);
    hdr.appendChild(dockBtn);
    hdr.appendChild(closeBtn);

    // ── Keyword management bar ──
    const kwBar = document.createElement('div');
    kwBar.id = 'xfs-kw-bar';
    kwBar.style.cssText = [
      'position:absolute', 'top:42px', 'left:12px', 'right:12px',
      'box-sizing:border-box',
      'max-height:min(72vh, calc(100vh - 125px))',
      'overflow:auto',
      `padding:10px 12px`, `border:1px solid ${C.border}`,
      'border-radius:10px',
      'display:flex', 'flex-direction:column', 'gap:8px',
      'background:rgba(255,255,255,0.98)',
      'box-shadow:0 8px 22px rgba(0,0,0,0.16)',
      'z-index:2',
    ].join(';');

    let regexRulesOpen = false;
    function renderKwBar() {
      kwBar.innerHTML = '';
      const rowCss = 'display:flex;flex-wrap:wrap;gap:6px;align-items:center;';
      const refreshKwPanel = () => renderKwBar();
      const toolsRow = document.createElement('div');
      toolsRow.style.cssText = 'display:flex;justify-content:flex-end;align-items:center;gap:6px;min-height:28px;';
      const exportBtn = document.createElement('button');
      exportBtn.textContent = '导出自定义';
      exportBtn.title = '只复制手动添加的自定义关键词 JSON，不包含系统预设';
      exportBtn.style.cssText = `background:#fff;color:${C.text};border:1px solid ${C.btnBorder};border-radius:8px;padding:4px 10px;font-size:12px;line-height:18px;font-weight:600;cursor:pointer;`;
      exportBtn.onclick = exportKws;
      const mergeBtn = document.createElement('button');
      mergeBtn.textContent = '合并导入';
      mergeBtn.title = '导入自定义关键词 JSON，并与当前自定义规则合并';
      mergeBtn.style.cssText = exportBtn.style.cssText;
      mergeBtn.onclick = () => importKws('merge');
      const replaceBtn = document.createElement('button');
      replaceBtn.textContent = '覆盖导入';
      replaceBtn.title = '用导入 JSON 覆盖当前自定义规则，系统预设不受影响';
      replaceBtn.style.cssText = exportBtn.style.cssText;
      replaceBtn.onclick = () => importKws('replace');
      toolsRow.appendChild(exportBtn);
      toolsRow.appendChild(mergeBtn);
      toolsRow.appendChild(replaceBtn);
      kwBar.appendChild(toolsRow);

      // ── Row 1: Content keywords ──
      const textRow = document.createElement('div');
      textRow.style.cssText = rowCss;
      const textLbl = document.createElement('span');
      textLbl.textContent = '内容:';
      textLbl.style.cssText = `font-size:10px;color:${C.sub};flex-shrink:0;min-width:36px;`;
      textRow.appendChild(textLbl);
      SUSPECT_KWS.forEach((kw, i) => {
        const chip = document.createElement('span');
        chip.title = ruleTitle('content', i, kw);
        chip.style.cssText = `display:inline-flex;align-items:center;gap:2px;padding:2px 6px;background:#fff;border:1px solid ${C.btnBorder};border-radius:10px;font-size:10px;color:${C.text};`;
        chip.textContent = kw + ' ';
        const del = document.createElement('button');
        del.textContent = '×';
        del.style.cssText = `background:none;border:none;cursor:pointer;font-size:11px;color:${C.sub};padding:0;line-height:1;`;
        del.onclick = () => { removeManualKeyword('content', kw); };
        chip.appendChild(del);
        textRow.appendChild(chip);
      });
      const inp = document.createElement('input');
      inp.placeholder = '+ 内容';
      inp.style.cssText = `border:1px solid ${C.btnBorder};border-radius:10px;padding:5px 9px;font-size:10px;width:150px;min-width:150px;outline:none;`;
      const addKw = () => {
        const v = inp.value.trim();
        if (v && addManualKeyword('content', v)) inp.value = '';
        else inp.value = '';
      };
      inp.onkeydown = e => { if (e.key === 'Enter') addKw(); };
      textRow.appendChild(inp);
      const addBtn = document.createElement('button');
      addBtn.textContent = '+';
      addBtn.style.cssText = `background:${C.blockRed};color:#fff;border:none;border-radius:10px;padding:4px 10px;font-size:11px;cursor:pointer;`;
      addBtn.onclick = addKw;
      textRow.appendChild(addBtn);
      // ── Row 2: Name keywords ──
      const nameRow = document.createElement('div');
      nameRow.style.cssText = rowCss;
      const nameLbl = document.createElement('span');
      nameLbl.textContent = '用户名:';
      nameLbl.style.cssText = `font-size:10px;color:${C.nameKw};flex-shrink:0;min-width:36px;`;
      nameRow.appendChild(nameLbl);
      SUSPECT_NAME_KWS.forEach((kw, i) => {
        const chip = document.createElement('span');
        chip.title = ruleTitle('name', i, kw);
        chip.style.cssText = `display:inline-flex;align-items:center;gap:2px;padding:2px 6px;background:#fff;border:1px solid ${C.nameKw};border-radius:10px;font-size:10px;color:${C.nameKw};`;
        chip.textContent = kw + ' ';
        const del = document.createElement('button');
        del.textContent = '×';
        del.style.cssText = `background:none;border:none;cursor:pointer;font-size:11px;color:${C.nameKw};padding:0;line-height:1;`;
        del.onclick = () => { removeManualKeyword('name', kw); };
        chip.appendChild(del);
        nameRow.appendChild(chip);
      });
      const nInp = document.createElement('input');
      nInp.placeholder = '+ 用户名';
      nInp.style.cssText = `border:1px solid ${C.nameKw};border-radius:10px;padding:5px 9px;font-size:10px;width:150px;min-width:150px;outline:none;`;
      const addNKw = () => {
        const v = nInp.value.trim();
        if (v && addManualKeyword('name', v)) nInp.value = '';
        else nInp.value = '';
      };
      nInp.onkeydown = e => { if (e.key === 'Enter') addNKw(); };
      nameRow.appendChild(nInp);
      const addNBtn = document.createElement('button');
      addNBtn.textContent = '+';
      addNBtn.style.cssText = `background:${C.nameKw};color:#fff;border:none;border-radius:10px;padding:4px 10px;font-size:11px;cursor:pointer;`;
      addNBtn.onclick = addNKw;
      nameRow.appendChild(addNBtn);
      kwBar.appendChild(nameRow);
      kwBar.appendChild(textRow);

      // ── Row 3: RegEx patterns ──
      const reSection = document.createElement('div');
      reSection.style.cssText = 'display:flex;flex-direction:column;gap:6px;';
      const reHeader = document.createElement('div');
      reHeader.style.cssText = rowCss;
      const reToggle = document.createElement('button');
      reToggle.type = 'button';
      reToggle.textContent = regexRulesOpen ? '▾' : '▸';
      reToggle.title = regexRulesOpen ? '收起正则规则' : '展开正则规则';
      reToggle.style.cssText = `width:20px;height:20px;padding:0;border:1px solid ${C.regexKw};border-radius:7px;background:#fff;color:${C.regexKw};font-size:12px;font-weight:800;line-height:18px;cursor:pointer;`;
      reToggle.onclick = () => { regexRulesOpen = !regexRulesOpen; refreshKwPanel(); };
      const reLbl = document.createElement('span');
      reLbl.textContent = `正则 (${SUSPECT_RE_KWS.length})`;
      reLbl.style.cssText = `font-size:10px;color:${C.regexKw};font-weight:700;flex-shrink:0;`;
      const reTip = document.createElement('span');
      reTip.textContent = '?';
      reTip.title = '正则很有效，懂的话可以新增；不懂建议别删，删除会明显削弱匹配。';
      reTip.style.cssText = `display:inline-flex;align-items:center;justify-content:center;width:16px;height:16px;border:1px solid ${C.regexKw};border-radius:50%;font-size:10px;font-weight:700;color:${C.regexKw};cursor:help;`;
      reHeader.appendChild(reToggle);
      reHeader.appendChild(reLbl);
      reHeader.appendChild(reTip);
      reSection.appendChild(reHeader);
      if (regexRulesOpen) {
        const reRow = document.createElement('div');
        reRow.style.cssText = rowCss;
        SUSPECT_RE_KWS.forEach((pat, i) => {
          const chip = document.createElement('span');
          chip.title = ruleTitle('regex', i, pat);
          chip.style.cssText = `display:inline-flex;align-items:center;gap:2px;padding:2px 6px;background:#fff;border:1px solid ${C.regexKw};border-radius:10px;font-size:10px;color:${C.regexKw};max-width:360px;`;
          const lbl = document.createElement('span');
          lbl.style.cssText = 'overflow:hidden;text-overflow:ellipsis;white-space:nowrap;';
          lbl.textContent = pat;
          const del = document.createElement('button');
          del.textContent = '×';
          del.style.cssText = `background:none;border:none;cursor:pointer;font-size:11px;color:${C.regexKw};padding:0;line-height:1;flex-shrink:0;`;
          del.onclick = () => { removeManualKeyword('regex', pat); };
          chip.appendChild(lbl);
          chip.appendChild(del);
          reRow.appendChild(chip);
        });
        const reInp = document.createElement('input');
        reInp.placeholder = '+ 正则';
        reInp.title = '输入 JS 正则表达式（不含 / 分隔符），flags: mu 自动加入；可加 content: 或 name: 限定匹配范围';
        reInp.style.cssText = `border:1px solid ${C.regexKw};border-radius:10px;padding:5px 9px;font-size:10px;width:260px;min-width:220px;outline:none;`;
        const addRe = () => {
          const v = reInp.value.trim();
          if (!v) return;
          const parsed = _regexPatternParts(v);
          try { if (!parsed.pat) throw new Error('empty regex'); new RegExp(parsed.pat, 'mu'); } catch (_) { reInp.style.borderColor = C.blockRed; return; }
          reInp.style.borderColor = C.regexKw;
          if (addManualKeyword('regex', v)) reInp.value = '';
          else reInp.value = '';
        };
        reInp.onkeydown = e => { if (e.key === 'Enter') addRe(); };
        reInp.oninput   = () => {
          const v = reInp.value.trim();
          if (!v) { reInp.style.borderColor = C.regexKw; return; }
          const parsed = _regexPatternParts(v);
          try { if (!parsed.pat) throw new Error('empty regex'); new RegExp(parsed.pat, 'mu'); reInp.style.borderColor = C.regexKw; }
          catch (_) { reInp.style.borderColor = C.blockRed; }
        };
        reRow.appendChild(reInp);
        const addReBtn = document.createElement('button');
        addReBtn.textContent = '+';
        addReBtn.style.cssText = `background:${C.regexKw};color:#fff;border:none;border-radius:10px;padding:4px 10px;font-size:11px;cursor:pointer;`;
        addReBtn.onclick = addRe;
        reRow.appendChild(addReBtn);
        reSection.appendChild(reRow);

        const hideOnlySection = document.createElement('div');
        hideOnlySection.style.cssText = `display:flex;flex-direction:column;gap:6px;padding-top:4px;border-top:1px dashed ${C.mute};margin-top:2px;`;
        const hideOnlyHeader = document.createElement('div');
        hideOnlyHeader.style.cssText = rowCss;
        const hideOnlyLbl = document.createElement('span');
        hideOnlyLbl.textContent = `只隐藏正则 (${HIDE_ONLY_RE_KWS.length})`;
        hideOnlyLbl.style.cssText = `font-size:10px;color:${C.mute};font-weight:700;flex-shrink:0;`;
        const hideOnlyTip = document.createElement('span');
        hideOnlyTip.textContent = '?';
        hideOnlyTip.title = '这是专门给“超级有效、但误伤也偏高”的规则准备的。命中后只隐藏，不会仅因这条规则进入自动拉黑候选；如果同时命中更严格规则，仍然照常进入拉黑流。';
        hideOnlyTip.style.cssText = `display:inline-flex;align-items:center;justify-content:center;width:16px;height:16px;border:1px solid ${C.mute};border-radius:50%;font-size:10px;font-weight:700;color:${C.mute};cursor:help;`;
        hideOnlyHeader.appendChild(hideOnlyLbl);
        hideOnlyHeader.appendChild(hideOnlyTip);
        hideOnlySection.appendChild(hideOnlyHeader);

        const hideOnlyNote = document.createElement('div');
        hideOnlyNote.textContent = '这一类规则特别适合“超级有效、能大幅降噪，但误伤也明显偏高”的模式。命中后只折叠回复，不会仅因这条规则进入自动拉黑候选；如果同时命中更严格规则，仍然照常进入拉黑流。拿不准、又怕误伤时，优先先放这里，别直接放进自动拉黑规则。';
        hideOnlyNote.style.cssText = `font-size:10px;line-height:1.4;color:${C.sub};padding:6px 8px;border:1px solid ${C.mute};border-radius:8px;background:#effaf7;`;
        hideOnlySection.appendChild(hideOnlyNote);

        const hideOnlyRow = document.createElement('div');
        hideOnlyRow.style.cssText = rowCss;
        HIDE_ONLY_RE_KWS.forEach((pat, i) => {
          const chip = document.createElement('span');
          chip.title = ruleTitle('hide_only_regex', i, pat);
          chip.style.cssText = `display:inline-flex;align-items:center;gap:2px;padding:2px 6px;background:#fff;border:1px solid ${C.mute};border-radius:10px;font-size:10px;color:${C.mute};max-width:360px;`;
          const lbl = document.createElement('span');
          lbl.style.cssText = 'overflow:hidden;text-overflow:ellipsis;white-space:nowrap;';
          lbl.textContent = pat;
          const del = document.createElement('button');
          del.textContent = '×';
          del.style.cssText = `background:none;border:none;cursor:pointer;font-size:11px;color:${C.mute};padding:0;line-height:1;flex-shrink:0;`;
          del.onclick = () => { removeManualKeyword('hide_only_regex', pat); };
          chip.appendChild(lbl);
          chip.appendChild(del);
          hideOnlyRow.appendChild(chip);
        });
        const hideOnlyInp = document.createElement('input');
        hideOnlyInp.placeholder = '+ 只隐藏正则';
        hideOnlyInp.title = '输入 JS 正则表达式（不含 / 分隔符），flags: mu 自动加入；默认按 content: 内容范围处理。适合高效果但高误伤、只想先隐藏降噪的规则。';
        hideOnlyInp.style.cssText = `border:1px solid ${C.mute};border-radius:10px;padding:5px 9px;font-size:10px;width:260px;min-width:220px;outline:none;`;
        const addHideOnlyRe = () => {
          const v = hideOnlyInp.value.trim();
          if (!v) return;
          const parsed = _regexPatternParts(v);
          if (parsed.scope !== 'both' && parsed.scope !== 'body') { hideOnlyInp.style.borderColor = C.blockRed; return; }
          try { if (!parsed.pat) throw new Error('empty regex'); new RegExp(parsed.pat, 'mu'); } catch (_) { hideOnlyInp.style.borderColor = C.blockRed; return; }
          hideOnlyInp.style.borderColor = C.mute;
          const normalized = `content:${parsed.pat}`;
          if (addManualKeyword('hide_only_regex', normalized)) hideOnlyInp.value = '';
          else hideOnlyInp.value = '';
        };
        hideOnlyInp.onkeydown = e => { if (e.key === 'Enter') addHideOnlyRe(); };
        hideOnlyInp.oninput = () => {
          const v = hideOnlyInp.value.trim();
          if (!v) { hideOnlyInp.style.borderColor = C.mute; return; }
          const parsed = _regexPatternParts(v);
          if (parsed.scope !== 'both' && parsed.scope !== 'body') { hideOnlyInp.style.borderColor = C.blockRed; return; }
          try { if (!parsed.pat) throw new Error('empty regex'); new RegExp(parsed.pat, 'mu'); hideOnlyInp.style.borderColor = C.mute; }
          catch (_) { hideOnlyInp.style.borderColor = C.blockRed; }
        };
        hideOnlyRow.appendChild(hideOnlyInp);
        const addHideOnlyBtn = document.createElement('button');
        addHideOnlyBtn.textContent = '+';
        addHideOnlyBtn.style.cssText = `background:${C.mute};color:#fff;border:none;border-radius:10px;padding:4px 10px;font-size:11px;cursor:pointer;`;
        addHideOnlyBtn.onclick = addHideOnlyRe;
        hideOnlyRow.appendChild(addHideOnlyBtn);
        hideOnlySection.appendChild(hideOnlyRow);

        const referralProfileSection = document.createElement('div');
        referralProfileSection.style.cssText = `display:flex;flex-direction:column;gap:6px;padding-top:4px;border-top:1px dashed ${C.referral};margin-top:2px;`;
        const referralProfileHeader = document.createElement('div');
        referralProfileHeader.style.cssText = rowCss;
        const referralProfileLbl = document.createElement('span');
        referralProfileLbl.textContent = `导流号主页正则 (${REFERRAL_PROFILE_RE_KWS.length})`;
        referralProfileLbl.style.cssText = `font-size:10px;color:${C.referral};font-weight:700;flex-shrink:0;`;
        const referralProfileTip = document.createElement('span');
        referralProfileTip.textContent = '?';
        referralProfileTip.title = '匹配主页资料文本和主页链接文本，用于导流号识别，不参与普通内容扫描。可输入 profile: 前缀，或直接输入无前缀正则。';
        referralProfileTip.style.cssText = `display:inline-flex;align-items:center;justify-content:center;width:16px;height:16px;border:1px solid ${C.referral};border-radius:50%;font-size:10px;font-weight:700;color:${C.referral};cursor:help;`;
        referralProfileHeader.appendChild(referralProfileLbl);
        referralProfileHeader.appendChild(referralProfileTip);
        referralProfileSection.appendChild(referralProfileHeader);

        const referralProfileNote = document.createElement('div');
        referralProfileNote.textContent = '这一类规则专门用于主页导流识别，匹配对象是主页简介、名称、位置以及主页上的链接文本。命中后会放宽为“主页存在导流意图”，再结合主页链接进入导流号判断。';
        referralProfileNote.style.cssText = `font-size:10px;line-height:1.4;color:${C.sub};padding:6px 8px;border:1px solid ${C.referral};border-radius:8px;background:#fff9f2;`;
        referralProfileSection.appendChild(referralProfileNote);

        const referralProfileRow = document.createElement('div');
        referralProfileRow.style.cssText = rowCss;
        REFERRAL_PROFILE_RE_KWS.forEach((pat, i) => {
          const chip = document.createElement('span');
          chip.title = ruleTitle('referral_profile_regex', i, pat);
          chip.style.cssText = `display:inline-flex;align-items:center;gap:2px;padding:2px 6px;background:#fff;border:1px solid ${C.referral};border-radius:10px;font-size:10px;color:${C.referral};max-width:360px;`;
          const lbl = document.createElement('span');
          lbl.style.cssText = 'overflow:hidden;text-overflow:ellipsis;white-space:nowrap;';
          lbl.textContent = pat;
          const del = document.createElement('button');
          del.textContent = '×';
          del.style.cssText = `background:none;border:none;cursor:pointer;font-size:11px;color:${C.referral};padding:0;line-height:1;flex-shrink:0;`;
          del.onclick = () => { removeManualKeyword('referral_profile_regex', pat); };
          chip.appendChild(lbl);
          chip.appendChild(del);
          referralProfileRow.appendChild(chip);
        });
        const referralProfileInp = document.createElement('input');
        referralProfileInp.placeholder = '+ 导流号主页正则';
        referralProfileInp.title = '输入 JS 正则表达式（不含 / 分隔符），flags: mu 自动加入；可加 profile: 前缀，或直接输入无前缀正则。';
        referralProfileInp.style.cssText = `border:1px solid ${C.referral};border-radius:10px;padding:5px 9px;font-size:10px;width:260px;min-width:220px;outline:none;`;
        const addReferralProfileRe = () => {
          const v = referralProfileInp.value.trim();
          if (!v) return;
          const parsed = _regexPatternParts(v);
          if (parsed.scope !== 'both' && parsed.scope !== 'profile') { referralProfileInp.style.borderColor = C.blockRed; return; }
          try { if (!parsed.pat) throw new Error('empty regex'); new RegExp(parsed.pat, 'mu'); } catch (_) { referralProfileInp.style.borderColor = C.blockRed; return; }
          referralProfileInp.style.borderColor = C.referral;
          const normalized = `profile:${parsed.pat}`;
          if (addManualKeyword('referral_profile_regex', normalized)) referralProfileInp.value = '';
          else referralProfileInp.value = '';
        };
        referralProfileInp.onkeydown = e => { if (e.key === 'Enter') addReferralProfileRe(); };
        referralProfileInp.oninput = () => {
          const v = referralProfileInp.value.trim();
          if (!v) { referralProfileInp.style.borderColor = C.referral; return; }
          const parsed = _regexPatternParts(v);
          if (parsed.scope !== 'both' && parsed.scope !== 'profile') { referralProfileInp.style.borderColor = C.blockRed; return; }
          try { if (!parsed.pat) throw new Error('empty regex'); new RegExp(parsed.pat, 'mu'); referralProfileInp.style.borderColor = C.referral; }
          catch (_) { referralProfileInp.style.borderColor = C.blockRed; }
        };
        referralProfileRow.appendChild(referralProfileInp);
        const addReferralProfileBtn = document.createElement('button');
        addReferralProfileBtn.textContent = '+';
        addReferralProfileBtn.style.cssText = `background:${C.referral};color:#fff;border:none;border-radius:10px;padding:4px 10px;font-size:11px;cursor:pointer;`;
        addReferralProfileBtn.onclick = addReferralProfileRe;
        referralProfileRow.appendChild(addReferralProfileBtn);
        referralProfileSection.appendChild(referralProfileRow);
        hideOnlySection.appendChild(referralProfileSection);
        reSection.appendChild(hideOnlySection);
      }
      kwBar.appendChild(reSection);
    }
    renderKwBar();
    kwBar.style.display = opts.keywordsOpen ? 'flex' : 'none'; // popup, collapsed by default

    // Toggle button — inserted into hdr before the × close button
    const kwToggle = document.createElement('button');
    kwToggle.textContent = opts.keywordsOpen ? '关键词 ×' : '关键词';
    kwToggle.style.cssText = `background:none;border:1px solid ${C.btnBorder};border-radius:8px;cursor:pointer;font-size:10px;color:${C.sub};padding:1px 6px;white-space:nowrap;`;
    kwToggle.onclick = () => {
      const nowHidden = kwBar.style.display === 'none';
      kwBar.style.display = nowHidden ? 'flex' : 'none';
      kwToggle.textContent = nowHidden ? '关键词 ×' : '关键词';
    };
    if (isGlobalQueueView) kwToggle.style.display = 'none';
    hdr.insertBefore(kwToggle, closeBtn);

    let dockIndicator = null;
    let dockIndicatorLabel = null;
    let dockCaption = null;
    let dockRestoreBtn = null;
    let dockRefreshBtn = null;
    let dockRefreshVisible = false;
    let dockStatusText = '';
    let dockPrimaryButton = null;
    function dockText() {
      return dockPrimaryButton?.textContent || badge.textContent || 'XFS';
    }
    function compactDockText(text) {
      const s = String(text || '').trim();
      const progress = s.match(/\d+\s*\/\s*\d+(?:\s*\(\d+失败\))?/);
      if (progress) return progress[0].replace(/\s+/g, '');
      const checked = s.match(/拉黑\s*\((\d+)\)/);
      if (checked) return `拉黑${checked[1]}`;
      const done = s.match(/完成\s*(\d+)/);
      if (done) return `拉黑${done[1]}`;
      return s.length > 12 ? `${s.slice(0, 12)}...` : s;
    }
    function updateDockIndicator(text = dockText(), opts = {}) {
      dockStatusText = text;
      if ('showRefresh' in opts) dockRefreshVisible = !!opts.showRefresh;
      if (!dockIndicator) return;
      if (dockIndicatorLabel) dockIndicatorLabel.textContent = compactDockText(text);
      if (dockRefreshBtn) dockRefreshBtn.style.display = dockRefreshVisible ? 'flex' : 'none';
      dockIndicator.title = `X Fraud Scanner · ${text}`;
    }
    function openDockIndicator() {
      document.getElementById('xfs-panel-dock')?.remove();
      const dockPos = clampFloatingPanelPosition(
        readFloatingPanelPosition(RESULT_PANEL_DOCK_POS_KEY, { left: 0, top: 92 }),
        GLOBAL_BLOCK_QUEUE_PANEL_W,
        140
      );
      dockIndicator = document.createElement('div');
      dockIndicator.id = 'xfs-panel-dock';
      dockIndicator.style.cssText = [
        'position:fixed', `left:${dockPos.left}px`, `top:${dockPos.top}px`,
        `width:${GLOBAL_BLOCK_QUEUE_PANEL_W}px`, 'box-sizing:border-box',
        'max-height:calc(100vh - 128px)',
        'background:rgba(255,255,255,0.72)', `color:${C.text}`,
        'backdrop-filter:blur(6px)', '-webkit-backdrop-filter:blur(6px)',
        `border:1px solid rgba(207,217,222,0.58)`, 'border-left:none',
        'border-radius:0 10px 10px 0',
        'box-shadow:1px 0 8px rgba(0,0,0,0.10)',
        'font-size:11px', 'font-weight:700', 'line-height:1.25',
        'padding:10px',
        'display:flex', 'flex-direction:column', 'align-items:center', 'gap:8px',
        'z-index:2147483647',
        `font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif`,
        'white-space:normal', 'overflow:hidden',
      ].join(';');
      const closeDockBtn = document.createElement('button');
      closeDockBtn.type = 'button';
      closeDockBtn.textContent = '\u00d7';
      closeDockBtn.title = '关闭进度提示，后台继续执行';
      closeDockBtn.style.cssText = [
        'flex-shrink:0',
        'width:18px', 'height:18px', 'line-height:1',
        'padding:0', 'border:none', 'border-radius:8px',
        'background:rgba(15,20,25,0.06)', `color:${C.sub}`,
        'font-size:12px', 'font-weight:700',
        'cursor:pointer', 'display:flex', 'align-items:center', 'justify-content:center',
        'appearance:none', '-webkit-appearance:none',
      ].join(';');
      closeDockBtn.onclick = e => {
        e.stopPropagation();
        dockIndicator.remove();
        dockIndicator = null;
        dockIndicatorLabel = null;
        dockCaption = null;
        dockRestoreBtn = null;
        dockRefreshBtn = null;
      };
      const dockTop = document.createElement('div');
      dockTop.style.cssText = [
        'width:calc(100% + 20px)', 'box-sizing:border-box',
        'margin:-10px -10px 0', 'padding:6px 8px',
        'display:flex', 'align-items:center', 'justify-content:space-between', 'gap:6px',
        'background:rgba(15,20,25,0.035)',
        `border-bottom:1px solid rgba(207,217,222,0.48)`,
        'border-radius:0 9px 0 0',
      ].join(';');
      dockCaption = document.createElement('div');
      dockCaption.textContent = '拉黑排队';
      dockCaption.style.cssText = [
        `flex:1;color:${C.sub};opacity:0.78`,
        'font-size:10px', 'font-weight:700', 'line-height:1',
        'text-align:left', 'white-space:nowrap', 'overflow:hidden',
      ].join(';');
      dockIndicatorLabel = document.createElement('div');
      dockIndicatorLabel.style.cssText = [
        `color:${C.text}`, 'font:inherit', 'text-align:center',
        'width:100%', 'min-height:16px', 'overflow:hidden', 'overflow-wrap:anywhere',
      ].join(';');
      const dockActions = document.createElement('div');
      dockActions.style.cssText = 'display:flex;flex-direction:column;gap:6px;align-items:center;width:100%;';
      dockRestoreBtn = document.createElement('button');
      dockRestoreBtn.type = 'button';
      dockRestoreBtn.textContent = '打开排队';
      dockRestoreBtn.title = '打开拉黑排队';
      dockRestoreBtn.style.cssText = [
        'background:rgba(15,20,25,0.045)', `color:${C.sub}`,
        `border:1px solid rgba(207,217,222,0.66)`, 'border-radius:7px',
        'font-size:11px', 'font-weight:700', 'line-height:1',
        'width:100%', 'height:25px', 'padding:0', 'cursor:pointer',
        'box-sizing:border-box', 'text-align:center', 'white-space:nowrap',
        'display:flex', 'align-items:center', 'justify-content:center',
        'appearance:none', '-webkit-appearance:none',
      ].join(';');
      dockRestoreBtn.onclick = e => {
        e.stopPropagation();
        panel.style.display = 'flex';
        panelDockedActive = false;
        GM_setValue('panel_docked', false);
        dockIndicator.remove();
        dockIndicator = null;
        dockIndicatorLabel = null;
        dockCaption = null;
        dockRestoreBtn = null;
        dockRefreshBtn = null;
      };
      dockRefreshBtn = document.createElement('button');
      dockRefreshBtn.type = 'button';
      dockRefreshBtn.textContent = '刷新';
      dockRefreshBtn.title = '刷新页面';
      dockRefreshBtn.style.cssText = [
        'display:none',
        'background:rgba(15,20,25,0.045)', `color:${C.sub}`,
        `border:1px solid rgba(207,217,222,0.66)`, 'border-radius:7px',
        'font-size:11px', 'font-weight:700', 'line-height:1',
        'width:100%', 'height:25px', 'padding:0', 'cursor:pointer',
        'box-sizing:border-box', 'text-align:center', 'white-space:nowrap',
        'align-items:center', 'justify-content:center',
        'appearance:none', '-webkit-appearance:none',
      ].join(';');
      dockRefreshBtn.onclick = e => {
        e.stopPropagation();
        location.reload();
      };
      dockTop.appendChild(dockCaption);
      dockTop.appendChild(closeDockBtn);
      dockIndicator.appendChild(dockTop);
      dockIndicator.appendChild(dockIndicatorLabel);
      dockActions.appendChild(dockRestoreBtn);
      dockActions.appendChild(dockRefreshBtn);
      dockIndicator.appendChild(dockActions);
      makeDraggableFloatingPanel(dockIndicator, dockTop, RESULT_PANEL_DOCK_POS_KEY, {
        width: () => GLOBAL_BLOCK_QUEUE_PANEL_W,
        height: () => dockIndicator.offsetHeight || 120,
      });
      updateDockIndicator(dockStatusText || dockText(), { showRefresh: dockRefreshVisible });
      document.body.appendChild(dockIndicator);
    }
    dockBtn.onclick = () => {
      if (isGlobalQueueView) {
        setGlobalBlockQueueMinimized(true);
        return;
      }
      kwBar.style.display = 'none';
      kwToggle.textContent = '关键词';
      panelDockedActive = true;
      GM_setValue('panel_docked', true);
      panel.style.display = 'none';
      openDockIndicator();
    };

    // ── Body: CSS multi-column, fills left→right ──
    // Wrapper needed so column-fill:auto sees a fixed height
    const body = document.createElement('div');
    body.style.cssText = 'flex:1;min-height:0;overflow-x:auto;overflow-y:hidden;';

    const colContainer = document.createElement('div');
    colContainer.style.cssText = [
      // height set via rAF after DOM insertion — required for column-fill:auto
      `column-count:${colsNeeded}`,
      'column-fill:auto',
      `column-rule:1px solid ${C.border}`,
      'column-gap:0',
    ].join(';');

    const allCheckboxes = []; // { cb, handle, row }

    if (ordered.length === 0) {
      colContainer.style.columnCount = 'auto';
      const empty = document.createElement('div');
      if (isGlobalQueueView && !globalQueueShowDone() && globalBlockQueueSummary().counts.done > 0) {
        empty.textContent = '当前没有待处理账号；已屏蔽账号已折叠';
      } else {
        empty.textContent = isGlobalQueueView ? '拉黑排队为空' : '未发现符合条件的用户';
      }
      empty.style.cssText = `padding:32px;color:${C.sub};`;
      colContainer.appendChild(empty);
    } else {
      ordered.forEach(user => {
        const cat = getPrimaryCat(user);
        const color = CAT_META[cat].color;

        // Wrapper div with break-inside:avoid so a row is never split across columns
        const wrap = document.createElement('div');
        wrap.style.cssText = 'break-inside:avoid;page-break-inside:avoid;position:relative;';

        const row = document.createElement('div');
        row.style.cssText = `display:flex;align-items:flex-start;gap:4px;padding:1px ${isGlobalQueueView ? '22px' : '5px'} 1px 4px;cursor:pointer;border-bottom:1px solid ${C.border};border-left:3px solid ${color};line-height:1.18;`;
        row.title = hitTooltipFromUser(user);
        row.onmouseenter = () => { if (!row.dataset.blocked) row.style.background = C.rowHover; };
        row.onmouseleave = () => { if (!row.dataset.blocked) row.style.background = ''; };

        if (isGlobalQueueView) {
          const running = (user.queueStatus || 'queued') === 'running';
          const retryBtn = document.createElement('button');
          retryBtn.type = 'button';
          retryBtn.textContent = '↻';
          retryBtn.title = user.queueStatus === 'failed' ? `重新执行 @${user.handle}` : `重试/重新执行 @${user.handle}`;
          retryBtn.disabled = user.queueStatus !== 'failed';
          retryBtn.style.cssText = `position:absolute;top:4px;right:23px;z-index:1;width:14px;height:14px;padding:0;border:none;border-radius:999px;background:${user.queueStatus === 'failed' ? 'rgba(15,20,25,0.06)' : 'transparent'};color:${user.queueStatus === 'failed' ? C.sub : 'transparent'};font-size:12px;line-height:1;display:flex;align-items:center;justify-content:center;cursor:${user.queueStatus === 'failed' ? 'pointer' : 'default'};opacity:${user.queueStatus === 'failed' ? '1' : '0'};`;
          retryBtn.onclick = e => {
            e.stopPropagation();
            const result = retryGlobalBlockQueueItem(user.handle);
            if (!result.ok && result.reason === 'running') showToast(`@${user.handle} 正在执行中，暂时不能重试`, true);
          };
          const removeBtn = document.createElement('button');
          removeBtn.type = 'button';
          removeBtn.textContent = '×';
          removeBtn.title = running ? `@${user.handle} 正在执行中，暂时不能移出队列` : `将 @${user.handle} 移出拉黑队列`;
          removeBtn.disabled = running;
          removeBtn.style.cssText = `position:absolute;top:4px;right:5px;z-index:1;width:14px;height:14px;padding:0;border:none;border-radius:999px;background:${running ? 'transparent' : 'rgba(15,20,25,0.06)'};color:${running ? C.mute : C.sub};font-size:12px;line-height:1;display:flex;align-items:center;justify-content:center;cursor:${running ? 'not-allowed' : 'pointer'};opacity:${running ? '0.45' : '1'};`;
          removeBtn.onclick = e => {
            e.stopPropagation();
            const result = removeGlobalBlockQueueItem(user.handle);
            if (!result.ok && result.reason === 'running') showToast(`@${user.handle} 正在执行中，暂时不能移出队列`, true);
          };
          wrap.appendChild(retryBtn);
          wrap.appendChild(removeBtn);
        }

        let cb = null;
        if (isGlobalQueueView) {
          const status = document.createElement('span');
          status.textContent = user.queueStatus === 'done' ? '✓' : (user.queueStatus === 'failed' ? '!' : (user.queueStatus === 'running' ? '…' : '•'));
          status.title = user.queueStatusLabel || user.queueStatus || 'queued';
          status.style.cssText = `width:13px;margin-top:1px;flex-shrink:0;text-align:center;font-size:12px;font-weight:800;color:${color};`;
          row.appendChild(status);
        } else {
          cb = document.createElement('input');
          cb.type = 'checkbox';
          cb.checked = opts.precheck !== false;
          cb.style.cssText = 'width:11px;height:11px;margin-top:2px;flex-shrink:0;cursor:pointer;accent-color:#f4212e;';
          allCheckboxes.push({ cb, handle: user.handle, row });
          row.onclick = e => {
            if (e.target.closest('a,input,button')) return;
            cb.checked = !cb.checked;
            cb.dispatchEvent(new Event('change', { bubbles: true }));
          };
        }

        const info = document.createElement('div');
        info.style.cssText = 'flex:1;min-width:0;';
        const profileUrl = `https://x.com/${encodeURIComponent(user.handle)}`;
        const profileTitle = `打开 @${user.handle} 主页`;
        let html = `<div class="xfs-name" style="font-size:11px;font-weight:600;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;"><a class="xfs-profile-link" href="${profileUrl}" target="_blank" rel="noopener noreferrer" title="${esc(profileTitle)}" style="color:inherit;text-decoration:underline;text-decoration-thickness:1px;text-underline-offset:2px;">${esc(user.displayName)}</a></div>`;
        html += `<div style="color:${C.sub};font-size:10px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;"><a class="xfs-profile-link" href="${profileUrl}" target="_blank" rel="noopener noreferrer" title="${esc(profileTitle)}" style="color:inherit;text-decoration:none;">@${esc(user.handle)}</a></div>`;
        if (isGlobalQueueView) {
          html += `<div style="font-size:9px;color:${color};font-weight:700;">[${esc(user.queueStatusLabel || user.queueStatus || 'queued')}] ${esc(user.queueStatusDetail || '')}</div>`;
          html += `
            <div style="display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:4px;margin-top:1px;">
              <div style="min-width:0;padding:2px 4px;border:1px solid ${C.border};border-radius:6px;background:rgba(255,255,255,0.78);font-size:9px;line-height:1.25;color:${C.text};word-break:break-word;">
                <div style="font-weight:800;color:${C.sub};margin-bottom:1px;">规则</div>
                <div>${esc(user.queueRuleSummary || '无规则命中')}</div>
              </div>
              <div style="min-width:0;padding:2px 4px;border:1px solid ${C.border};border-radius:6px;background:rgba(255,255,255,0.78);font-size:9px;line-height:1.25;color:${C.text};word-break:break-word;">
                <div style="font-weight:800;color:${C.sub};margin-bottom:1px;">AI</div>
                <div>${esc(user.queueAiSummary || 'AI 未参与')}</div>
              </div>
            </div>`;
          if (user.tweetSnippet) {
            html += `<div style="font-size:9px;color:${C.sub};font-style:italic;word-break:break-all;">"${esc(user.tweetSnippet)}"</div>`;
          }
        }
        if (!isGlobalQueueView && user.cats.has('heart') && user.heartHits && user.heartHits.length > 0) {
          html += `<div style="font-size:9px;color:${C.heart};">[心形] ${esc(user.heartHits.join(''))} 在用户名中</div>`;
        }
        if (!isGlobalQueueView && user.cats.has('name_kw') && user.nameKwHits && user.nameKwHits.length > 0) {
          user.nameKwHits.forEach(kw => {
            html += `<div style="font-size:9px;color:${C.nameKw};">[用户名] ${esc(kw)}</div>`;
          });
        }
        if (!isGlobalQueueView && (user.cats.has('heart') || user.cats.has('name_kw')) && user.tweetSnippet) {
          html += `<div style="font-size:9px;color:${C.sub};font-style:italic;word-break:break-all;">"${esc(user.tweetSnippet)}"</div>`;
        }
        if (!isGlobalQueueView && user.cats.has('suspect') && user.kwHits.length > 0) {
          user.kwHits.forEach(h => {
            html += `<div style="font-size:9px;color:${C.suspect};word-break:break-all;">[${esc(h.kw)}] ${esc(h.snippet)}</div>`;
          });
        }
        if (!isGlobalQueueView && user.cats.has('regex_kw') && user.reHits && user.reHits.length > 0) {
          user.reHits.forEach(h => {
            const label = regexRuleLabel(h.pat, h.type || 'regex');
            html += `<div style="font-size:9px;color:${C.regexKw};word-break:break-all;">[${esc(label)}] ${esc(h.snippet)}</div>`;
          });
        }
        if (!isGlobalQueueView && user.hideOnlyReHits && user.hideOnlyReHits.length > 0) {
          user.hideOnlyReHits.forEach(h => {
            const label = regexRuleLabel(h.pat, h.type || 'hide_only_regex');
            html += `<div style="font-size:9px;color:${C.mute};word-break:break-all;">[${esc(label)}] ${esc(h.snippet)}</div>`;
          });
        }
        info.innerHTML = html;
        info.querySelectorAll('a.xfs-profile-link').forEach(a => {
          a.addEventListener('click', e => e.stopPropagation());
        });

        if (cb) row.appendChild(cb);
        row.appendChild(info);
        wrap.appendChild(row);
        colContainer.appendChild(wrap);
      });
    }

    body.appendChild(colContainer);

    // ── Hint bar (revealed after blocking completes) ──
    const hint = document.createElement('div');
    hint.style.cssText = `padding:5px 12px;border-top:1px solid ${C.border};font-size:11px;color:${C.sub};text-align:center;flex-shrink:0;display:none;background:${C.catBg};`;
    hint.textContent = '已加入拉黑排队 · 右上角查看执行进度';

    // ── Footer ──
    const ftr = document.createElement('div');
    ftr.style.cssText = `padding:6px 12px;border-top:1px solid ${C.border};display:flex;gap:6px;align-items:center;flex-shrink:0;`;

    function mkBtn(text, isPrimary) {
      const b = document.createElement('button');
      b.textContent = text;
      b.style.cssText = isPrimary
        ? `flex:1;background:${C.blockRed};color:#fff;border:none;border-radius:14px;padding:5px 10px;font-size:12px;font-weight:700;cursor:pointer;`
        : `background:#fff;color:${C.text};border:1px solid ${C.btnBorder};border-radius:14px;padding:5px 10px;font-size:12px;cursor:pointer;`;
      return b;
    }

    if (isGlobalQueueView) {
      const refreshBtn = mkBtn('刷新', false);
      refreshBtn.onclick = showGlobalBlockQueueDetailPanel;
      const doneToggleBtn = mkBtn(globalQueueShowDone() ? '折叠已屏蔽' : '已屏蔽', false);
      doneToggleBtn.title = globalQueueShowDone() ? '隐藏已完成、已跳过和历史已屏蔽账号' : '展开查看已完成、已跳过和长期保存的历史已屏蔽账号';
      doneToggleBtn.onclick = () => setGlobalQueueShowDone(!globalQueueShowDone());
      const pauseBtn = mkBtn(globalBlockQueuePaused() ? '继续' : '暂停', false);
      pauseBtn.onclick = () => {
        setGlobalBlockQueuePaused(!globalBlockQueuePaused());
        showGlobalBlockQueueDetailPanel();
      };
      const clearDoneBtn = mkBtn('清完成', false);
      clearDoneBtn.onclick = () => {
        clearCompletedGlobalBlockQueue();
      };
      const clearQueueBtn = mkBtn('清队列', false);
      clearQueueBtn.title = '清除当前队列中的全部非执行中条目';
      clearQueueBtn.onclick = () => {
        const summary = globalBlockQueueSummary().counts;
        const removable = (summary.queued || 0) + (summary.done || 0) + (summary.failed || 0) + (summary.skipped || 0);
        const running = summary.running || 0;
        if (!removable && !running) {
          showToast('拉黑队列已经是空的', false);
          return;
        }
        const confirmText = running
          ? `当前有 ${running} 个账号正在执行中，暂时不会被清除。确认清除其余 ${removable} 个队列条目？`
          : `确认清除当前拉黑队列中的 ${removable} 个条目？此操作不可恢复。`;
        if (!window.confirm(confirmText)) return;
        const result = clearGlobalBlockQueue();
        showGlobalBlockQueueDetailPanel();
        if (result.removed) {
          showToast(
            result.running
              ? `已清除 ${result.removed} 个队列条目；仍有 ${result.running} 个执行中账号保留`
              : `已清除 ${result.removed} 个队列条目`,
            false
          );
        } else if (result.running) {
          showToast(`当前只有 ${result.running} 个执行中账号，暂时无法清除`, true);
        }
      };
      const closePanelBtn = mkBtn('收起', true);
      closePanelBtn.onclick = () => closeBtn.click();
      ftr.appendChild(refreshBtn);
      ftr.appendChild(doneToggleBtn);
      ftr.appendChild(pauseBtn);
      ftr.appendChild(clearDoneBtn);
      ftr.appendChild(clearQueueBtn);
      ftr.appendChild(closePanelBtn);
    } else {

      const deselBtn = mkBtn('取消全选', false);
      deselBtn.onclick = () => allCheckboxes.forEach(({ cb }) => { cb.checked = false; });

      const selBtn = mkBtn('全选', false);
      selBtn.onclick = () => allCheckboxes.forEach(({ cb }) => { cb.checked = true; });

      const checkedCount = () => allCheckboxes.filter(({ cb }) => cb.checked).length;
      const blockBtn = mkBtn(`加入拉黑排队 (${checkedCount()})`, true);
      dockPrimaryButton = blockBtn;
      let blockingInProgress = false;
      let blockingComplete = false;

      allCheckboxes.forEach(({ cb }) => {
        cb.addEventListener('change', () => {
          if (!blockingInProgress && !blockingComplete) blockBtn.textContent = `加入拉黑排队 (${checkedCount()})`;
        });
      });

      async function startBlocking() {
        if (blockBtn.disabled) return;
        const uniqueHandles = [...new Set(allCheckboxes.filter(({ cb }) => cb.checked).map(({ handle }) => handle))];
        const userByHandle = new Map((allUsers || []).map(user => [normalizeHandle(user.handle), user]));
        let added = 0, existing = 0, skipped = 0;
        try {
          if (uniqueHandles.length === 0) return;

          stopBackgroundLoad = true;  // stop background scroll so page stays put
          blockingInProgress = true;
          blockBtn.disabled = true;
          selBtn.disabled = true;

          const selectedUsers = uniqueHandles.map(handle => {
            const key = normalizeHandle(handle);
            const user = userByHandle.get(key) || { handle: key, displayName: handle };
            return { ...user, handle: key, source: opts.queueSource || 'panel' };
          });
          const result = enqueueGlobalBlockUsers(selectedUsers, opts.queueSource || 'panel');
          added = result.added;
          existing = result.existing;
          skipped = result.skipped;
          allCheckboxes.filter(({ cb }) => cb.checked).forEach(({ row }) => {
            row.dataset.blocked = '1';
            row.style.opacity = '0.55';
            const nameEl = row.querySelector('.xfs-name');
            if (nameEl) nameEl.style.textDecoration = 'underline';
          });
          blockingComplete = true;
          blockingInProgress = false;
          blockBtn.disabled = false;
          blockBtn.textContent = `已入队 ${added}${existing ? `，已有 ${existing}` : ''}${skipped ? `，跳过 ${skipped}` : ''}`;
          blockBtn.title = '已加入拉黑排队，右上角可查看进度';
          badge.textContent = `已加入拉黑排队 ${added} 个${existing ? `，已有 ${existing} 个` : ''}${skipped ? `，跳过 ${skipped} 个` : ''}`;
          updateDockIndicator(badge.textContent, { showRefresh: true });
          hint.style.display = '';
          markCleanupButtonsComplete(opts.refreshButtonIds);
        } finally {
          blockingInProgress = false;
          opts.onBlockDone?.({ queued: added, existing, skipped, total: uniqueHandles.length });
        }
      }

      blockBtn.onclick = startBlocking;

      ftr.appendChild(deselBtn);
      ftr.appendChild(selBtn);
      ftr.appendChild(blockBtn);
    }

    const rateNote = document.createElement('div');
    rateNote.style.cssText = `padding:3px 12px 5px;font-size:10px;color:${C.sub};text-align:center;flex-shrink:0;opacity:0.6;background:${C.catBg};`;
    rateNote.textContent = isGlobalQueueView
      ? `为了避开平台限流，拉黑会按 ${experimentalBrowseBlockActive() ? experimentSlowBlockGapText() : '3-5秒'} 间隔排队执行；${experimentCooldownSummaryText()}`
      : '勾选账号会加入拉黑排队；为了避开平台限流，每次拉黑间隔 3-5 秒';

    const scriptFtr = document.createElement('div');
    scriptFtr.style.cssText = `padding:2px 12px 4px;font-size:9px;color:${C.sub};text-align:center;flex-shrink:0;opacity:0.5;background:${C.catBg};`;
    const verSpan = document.createTextNode(`v${GM_info.script.version} · `);
    const gfLink = document.createElement('a');
    gfLink.textContent = 'GreasyFork';
    gfLink.href = GREASYFORK_URL;
    gfLink.target = '_blank';
    gfLink.rel = 'noopener noreferrer';
    gfLink.style.cssText = `color:${C.sub};text-decoration:underline;`;
    scriptFtr.appendChild(verSpan);
    scriptFtr.appendChild(gfLink);
    scriptFtr.appendChild(document.createTextNode(' · '));
    const xBlockedLink = document.createElement('a');
    xBlockedLink.textContent = 'X 已拉黑账号';
    xBlockedLink.href = 'https://x.com/settings/blocked/all';
    xBlockedLink.target = '_blank';
    xBlockedLink.rel = 'noopener noreferrer';
    xBlockedLink.style.cssText = `color:${C.sub};text-decoration:underline;`;
    scriptFtr.appendChild(xBlockedLink);

    panel.appendChild(hdr);
    panel.appendChild(kwBar);
    panel.appendChild(body);
    panel.appendChild(ftr);
    panel.appendChild(hint);
    panel.appendChild(rateNote);
    panel.appendChild(scriptFtr);
    document.body.appendChild(panel);
    const syncColumnHeight = () => {
      colContainer.style.height = `${Math.max(0, body.clientHeight)}px`;
    };
    let resizeSaveTimer = null;
    let panelResizeObserver = null;
    if (isGlobalQueueView && typeof ResizeObserver !== 'undefined') {
      panelResizeObserver = new ResizeObserver(() => {
        syncColumnHeight();
        clearTimeout(resizeSaveTimer);
        resizeSaveTimer = setTimeout(() => {
          writeFloatingPanelSize(GLOBAL_BLOCK_QUEUE_SIZE_KEY, {
            width: panel.offsetWidth,
            height: panel.offsetHeight,
          });
          writeGlobalBlockQueuePosition({
            left: panel.offsetLeft,
            top: panel.offsetTop,
          });
          requestAnimationFrame(updateGlobalBlockQueuePanel);
        }, 180);
      });
      panelResizeObserver.observe(panel);
    }
    requestAnimationFrame(updateGlobalBlockQueuePanel);

    // Escape key closes panel
    const closePanel = () => {
      panel.remove();
      document.getElementById('xfs-panel-dock')?.remove();
      if (isGlobalQueueView) GM_setValue(GLOBAL_BLOCK_QUEUE_MINIMIZED_KEY, true);
      dockIndicator = null;
      dockIndicatorLabel = null;
      dockCaption = null;
      dockRestoreBtn = null;
      dockRefreshBtn = null;
      if (panelResizeObserver) panelResizeObserver.disconnect();
      clearTimeout(resizeSaveTimer);
      document.removeEventListener('keydown', onEsc);
      if (isGlobalQueueView) updateGlobalBlockQueuePanel();
    };
    const onEsc = e => { if (e.key === 'Escape') closePanel(); };
    document.addEventListener('keydown', onEsc);
    closeBtn.onclick = closePanel;

    // Set colContainer to the measured pixel height so column-fill:auto works.
    // Must happen after panel is in DOM so clientHeight is non-zero.
    requestAnimationFrame(() => {
      syncColumnHeight();
      if (panelDockedActive) {
        kwBar.style.display = 'none';
        kwToggle.textContent = '关键词';
        panel.style.display = 'none';
        openDockIndicator();
      }
      if (opts.autoBlock) setTimeout(startBlocking, 0);
    });
  }

  // ── Shared: wait for new tweet articles to appear ────────────────────
  // Tracks the last article DOM element, not count.
  // Virtual scroll removes old tweets from top while adding new ones at bottom,
  // so count stays flat — but the tail element reference changes on new content.
  function waitForMore(timeout) {
    const all = document.querySelectorAll('article[data-testid="tweet"]');
    const lastBefore = all[all.length - 1] || null;
    return new Promise(resolve => {
      const obs = new MutationObserver(() => {
        const cur = document.querySelectorAll('article[data-testid="tweet"]');
        const newLast = cur[cur.length - 1] || null;
        if (newLast && newLast !== lastBefore) {
          obs.disconnect(); clearTimeout(t); resolve(true);
        }
      });
      obs.observe(document.body, { childList: true, subtree: true });
      const t = setTimeout(() => { obs.disconnect(); resolve(false); }, timeout);
    });
  }

  // Wait until at least 2 tweet articles are present (original + ≥1 reply).
  // Used after auto-reload so sweepAll doesn't start on an empty or half-loaded page.
  function waitForTweetContent(timeout = 12000) {
    if (document.querySelectorAll('article[data-testid="tweet"]').length > 1) return Promise.resolve();
    return new Promise(resolve => {
      const obs = new MutationObserver(() => {
        if (document.querySelectorAll('article[data-testid="tweet"]').length > 1) {
          obs.disconnect(); clearTimeout(t); resolve();
        }
      });
      obs.observe(document.body, { childList: true, subtree: true });
      const t = setTimeout(() => { obs.disconnect(); resolve(); }, timeout);
    });
  }

  function scanModeLabel(mode) {
    return {
      content: '内容扫描',
      referral: '导流扫描',
      sweep: '整页扫描',
      list: '列表扫描',
    }[mode] || '扫描';
  }

  function updateScanButtonsLocked() {
    ['xfs-btn', 'xfs-referral-scan-btn', 'xfs-sweep-btn', 'xfs-list-btn'].forEach(id => {
      const btn = document.getElementById(id);
      if (!btn) return;
      if (activeScanMode) {
        if (!btn.dataset.xfsPrevTitle) btn.dataset.xfsPrevTitle = btn.title || '';
        btn.disabled = true;
        btn.style.opacity = '0.4';
        btn.style.pointerEvents = 'none';
        btn.title = `${scanModeLabel(activeScanMode)}正在执行`;
      } else {
        btn.disabled = false;
        btn.style.opacity = '';
        btn.style.pointerEvents = '';
        if (btn.dataset.xfsPrevTitle != null) {
          if (btn.textContent !== DONE_SVG) btn.title = btn.dataset.xfsPrevTitle;
          delete btn.dataset.xfsPrevTitle;
        }
      }
    });
  }

  function beginScanMode(mode) {
    if (activeScanMode) {
      showToast(`${scanModeLabel(activeScanMode)}正在执行，请稍后再试`, true);
      return false;
    }
    activeScanMode = mode;
    updateScanButtonsLocked();
    return true;
  }

  function endScanMode(mode, force = false) {
    if (!force && activeScanMode !== mode) return;
    activeScanMode = '';
    updateScanButtonsLocked();
  }

  // ── Quick scan: show current DOM and immediately block checked users ──
  async function autoLoadAndScan() {
    if (!beginScanMode('content')) return;
    try {
      stopBackgroundLoad = true;
      const btn = document.getElementById('xfs-btn');
      reapplyContentRulesForVisible();
      autoQueueBlockUsers(scanPage(), {
        queueSource: 'content',
        refreshButtonIds: ['xfs-btn'],
        onBlockDone: (stats) => {
          endScanMode('content');
          reapplyContentRulesForVisible();
          refreshGlobalQueueInlineButtons();
          applyHideAll(); // preserve any existing hidden state after blocking
          if (btn && (!stats || (Number(stats.queued || 0) + Number(stats.existing || 0) === 0))) {
            btn.disabled = false;
            btn.style.opacity = '';
            btn.title = '当前视图内容垃圾号自动拉黑';
          }
        },
      });
    } catch (e) {
      endScanMode('content');
      throw e;
    }
  }

  // ── Sweep all: race to bottom first, then scan back up ───────────────
  // Strategy: fraud accounts arrive late (piggybacking on trending posts) and
  // pile up at the bottom of the reply thread. Load everything to the bottom
  // first (Phase 1), then scan on the way back up (Phase 2).
  //
  // Phase 1 — load only, no scan: scroll down and wait for each batch of tweets
  //   to load from the network. Stop when no new content appears.
  // Phase 2 — scan upward: step back toward the top one viewport at a time,
  //   scanning the visible DOM at each position. X.com re-renders tweets from
  //   memory as we scroll back into their range, so no extra network requests.
  async function sweepAll() {
    if (!beginScanMode('sweep')) return;
    try {
    stopBackgroundLoad = false;
    applyHideAll(); // preserve hidden state during scrolling
    const btn      = document.getElementById('xfs-btn');
    const sweepBtn = document.getElementById('xfs-sweep-btn');
    const MAX_DOWN = 60; // max scroll-down rounds to reach bottom
    const MAX_UP   = 80; // max viewport-steps scanning back to top

    document.getElementById('xfs-panel')?.remove();
    if (btn)      { btn.disabled = true; btn.style.opacity = '0.4'; }
    if (sweepBtn) { sweepBtn.disabled = true; sweepBtn.style.opacity = '0.4'; }

    const badge = document.createElement('div');
    badge.style.cssText = `position:fixed;bottom:220px;right:62px;font-size:10px;font-weight:700;font-family:monospace;color:#fff;border-radius:8px;padding:2px 6px;z-index:2147483647;pointer-events:none;`;
    document.body.appendChild(badge);

    const acc = new Map(); // handle → user, persists across rounds
    function mergeInto(users) {
      for (const u of users) {
        if (acc.has(u.handle)) {
          const ex = acc.get(u.handle);
          u.cats.forEach(c => ex.cats.add(c));
          u.heartHits.forEach(h  => { if (!ex.heartHits.includes(h))              ex.heartHits.push(h); });
          u.nameKwHits.forEach(h => { if (!ex.nameKwHits.includes(h))             ex.nameKwHits.push(h); });
          u.kwHits.forEach(h     => { if (!ex.kwHits.find(x => x.kw  === h.kw))  ex.kwHits.push(h); });
          u.reHits.forEach(h     => { if (!ex.reHits.find(x => x.pat === h.pat)) ex.reHits.push(h); });
        } else {
          acc.set(u.handle, { ...u, cats: new Set(u.cats) });
        }
      }
    }

    // ── Phase 1: race to the bottom ──────────────────────────────────────
    badge.style.background = C.nameKw;
    for (let i = 0; i < MAX_DOWN; i++) {
      if (stopBackgroundLoad) break;
      badge.textContent = `↓ 加载 ${i + 1}/${MAX_DOWN}…`;
      window.scrollTo({ top: document.documentElement.scrollHeight, behavior: 'instant' });
      let gotMore = await waitForMore(3000);
      if (!gotMore) {
        // one retry for slow networks
        window.scrollTo({ top: document.documentElement.scrollHeight, behavior: 'instant' });
        gotMore = await waitForMore(3000);
      }
      if (!gotMore) break;
    }

    // ── Phase 2: scan on the way back up ─────────────────────────────────
    badge.style.background = C.blockRed;
    const STEP = window.innerHeight * 0.85;
    for (let i = 0; i < MAX_UP; i++) {
      if (stopBackgroundLoad) break;
      mergeInto(scanPage());
      badge.textContent = `↑ 扫描 ${i + 1} · 已找 ${acc.size} 个`;
      if (window.scrollY <= 0) break;
      window.scrollTo({ top: Math.max(0, window.scrollY - STEP), behavior: 'instant' });
      await sleep(600); // re-render only, no network load needed
    }

    badge.remove();
    applyHideAll(); // keep hide state applied after scanning
    // Merge users found by the hide feature that React may have unloaded from the DOM
    mergeInto(Array.from(matchedUsersCache.values()));
    autoQueueBlockUsers(Array.from(acc.values()), { queueSource: 'sweep', refreshButtonIds: ['xfs-sweep-btn'] });

    if (btn)      { btn.disabled = false; btn.style.opacity = ''; }
    if (sweepBtn) { sweepBtn.disabled = false; sweepBtn.style.opacity = ''; }
    } finally {
      endScanMode('sweep');
    }
  }

  // ── Sweep user list: likes / retweets / followers pages ─────────────
  // Scrolls to the bottom collecting every UserCell handle, then shows
  // the panel for bulk blocking. Pure DOM — no private API calls needed,
  // so it survives X.com endpoint changes.
  async function sweepUserList() {
    if (!beginScanMode('list')) return;
    try {
    stopBackgroundLoad = false;
    const listBtn = document.getElementById('xfs-list-btn');
    const MAX_DOWN = 60;

    document.getElementById('xfs-panel')?.remove();
    if (listBtn) { listBtn.disabled = true; listBtn.style.opacity = '0.4'; }

    const badge = document.createElement('div');
    badge.style.cssText = `position:fixed;bottom:160px;right:62px;font-size:10px;font-weight:700;font-family:monospace;color:#fff;border-radius:8px;padding:2px 6px;z-index:2147483647;pointer-events:none;background:${C.mute};`;
    document.body.appendChild(badge);

    const acc = new Map();

    function collectCells() {
      document.querySelectorAll('[data-testid="UserCell"]').forEach(cell => {
        if (skipVerifiedAccountsActive && nodeHasVerifiedBadge(cell)) return;
        // @handle span — X.com reliably renders these as visible span text
        let handle = null;
        for (const sp of cell.querySelectorAll('span')) {
          const t = sp.textContent.trim();
          if (t.startsWith('@') && /^@[A-Za-z0-9_]{1,15}$/.test(t)) {
            handle = t.slice(1); break;
          }
        }
        if (!handle || acc.has(handle)) return;

        // Display name: text content of any profile link to this handle
        let displayName = handle;
        for (const a of cell.querySelectorAll(`a[href="/${handle}"]`)) {
          const txt = getTextWithEmoji(a).trim();
          if (txt && !txt.startsWith('@')) { displayName = txt; break; }
        }

        acc.set(handle, {
          handle, displayName,
          cats: new Set(['liker']),
          heartHits: [], nameKwHits: [], kwHits: [],
        });
      });
    }

    for (let i = 0; i < MAX_DOWN; i++) {
      if (stopBackgroundLoad) break;
      collectCells();
      badge.textContent = `↓ 加载 ${i + 1}/${MAX_DOWN} · 已收集 ${acc.size} 人`;
      window.scrollTo({ top: document.documentElement.scrollHeight, behavior: 'instant' });
      const gotMore = await waitForMore(2500);
      if (!gotMore) break;
    }
    collectCells(); // final pass after last scroll

    badge.remove();
    autoQueueBlockUsers(Array.from(acc.values()), { queueSource: 'list', refreshButtonIds: ['xfs-list-btn'] });
    if (listBtn) { listBtn.disabled = false; listBtn.style.opacity = ''; }
    } finally {
      endScanMode('list');
    }
  }

  // ── Floating icon buttons ────────────────────────────────────────────
  // User with minus: "block all from likes/retweets/followers list"
  const LIST_SVG      = '👤';  // bulk block from likes/retweets/followers list
  const SCAN_SVG      = '🔍';  // targeted scan current page
  const BLOCK_SCAN_SVG = '🚫'; // targeted content block current page
  const SWEEP_SVG     = '⚡';  // sweep all replies
  const DONE_SVG      = '✓';  // cleanup complete, click to reload
  const EYE_SVG       = '👁';  // hide toggle; active state is shown by color/border
  const GEAR_SVG      = '⚙';  // low-frequency tools: keyword import/export
  const COLLAPSE_SVG  = '-';  // collapse the right-side tool stack
  const EXPAND_SVG    = 'XFS';  // restore the right-side tool stack
  const QUEUE_SVG     = '隊';  // open global block queue card

  // ── Hide helpers ─────────────────────────────────────────────────────
  function applyHideToArticle(art) {
    if (isMainTweetArticle(art)) {
      clearMainTweetXfsState(art);
      return;
    }
    if (isProtectedVerifiedArticle(art)) {
      clearProtectedVerifiedArticleState(art);
      return;
    }
    const handle = extractHandleFromArticle(art);
    if (isAiExemptHandle(handle)) {
      art.dataset.xfsAiHidden = '';
      if (art.dataset.xfsHidden === '1') {
        art.dataset.xfsHidden = '';
        ['max-height','min-height','overflow','padding','margin-top','margin-bottom','pointer-events','border-bottom']
          .forEach(p => art.style.removeProperty(p));
      }
      clearBlockedArticleStyle(art);
      return;
    }
    const shouldHideMatched = hideMatchedActive && art.dataset.xfsHideMatched === '1';
    const shouldHideReferral = hideReferralActive && art.dataset.xfsReferralAccount === '1';
    const shouldHideBlocked = shouldHideBlockedArticles() && art.dataset.xfsBlocked === '1';
    const shouldHideAi = isAiHiddenHandle(handle);
    const shouldHide = shouldHideMatched || shouldHideReferral || shouldHideBlocked || shouldHideAi;
    if (shouldHide && art.dataset.xfsHidden !== '1') {
      if (shouldHideMatched) incrementHideRuleStatsFromArticle(art);
      art.dataset.xfsHidden = '1';
      clearBlockedArticleStyle(art);
      art.style.setProperty('max-height',    '2px',    'important');
      art.style.setProperty('min-height',    '0',      'important');
      art.style.setProperty('overflow',      'hidden', 'important');
      art.style.setProperty('padding',       '0',      'important');
      art.style.setProperty('margin-top',    '0',      'important');
      art.style.setProperty('margin-bottom', '0',      'important');
      art.style.setProperty('pointer-events','none',   'important');
      art.style.setProperty('border-bottom', `1px solid ${C.border}`, 'important');
    } else if (!shouldHide && art.dataset.xfsHidden === '1') {
      art.dataset.xfsHidden = '';
      ['max-height','min-height','overflow','padding','margin-top','margin-bottom','pointer-events','border-bottom']
        .forEach(p => art.style.removeProperty(p));
      if (art.dataset.xfsBlocked === '1') applyBlockedArticleStyle(art);
    }
  }

  function applyHideAll() {
    document.querySelectorAll('article[data-testid="tweet"]').forEach(applyHideToArticle);
  }

  function reapplyContentRulesForVisible() {
    if (!/\/status\/\d/.test(location.pathname) || isListPage()) return;
    document.querySelectorAll('article[data-testid="tweet"]').forEach(art => {
      if (isMainTweetArticle(art)) return;
      if (isProtectedVerifiedArticle(art)) {
        clearProtectedVerifiedArticleState(art);
        return;
      }
      const handle = art.dataset.xfsReferralHandle || extractHandleFromArticle(art);
      const key = normalizeHandle(handle);
      if (!key) return;
      const displayName = extractDisplayNameFromArticle(art, key) || key;
      const textEl = art.querySelector('[data-testid="tweetText"]');
      const cardEl = art.querySelector('[data-testid="card.wrapper"]');
      const bodyLinkText = [
        ...(textEl ? [...textEl.querySelectorAll('a[href]')] : []),
        ...(cardEl ? [...cardEl.querySelectorAll('a[href]')] : []),
      ].map(a => a.textContent).join(' ');
      const fullText = [textEl ? getTextWithEmoji(textEl) : null, cardEl ? getTextWithEmoji(cardEl) : null, bodyLinkText].filter(Boolean).join(' ');
      const tweetSnippet = buildUserPreviewSnippet(textEl ? getTextWithEmoji(textEl) : '', cardEl ? getTextWithEmoji(cardEl) : '', bodyLinkText);
      const { matched, actionableMatched, actionableCats, heartHits, nameKwHits, kwHits, reHits, hideOnlyReHits, allHideOnlyReHits } = matchesFilters(displayName, fullText);
      setArticleHideRuleStats(art, { nameKwHits, kwHits, reHits, hideOnlyReHits });
      const alreadyBlocked = blockedHandles.has(key);
      art.dataset.xfsHideMatched = (matched && !alreadyBlocked) ? '1' : '0';
      const btn = art.querySelector(`button[data-xfs-handle]`);
      if (btn) {
        btn.dataset.xfsMatched = (matched && !alreadyBlocked) ? '1' : '0';
        btn.dataset.xfsHideOnlyMatched = (!actionableMatched && allHideOnlyReHits.length > 0 && !alreadyBlocked) ? '1' : '0';
        if (matched && !alreadyBlocked) btn.dataset.xfsMatchTooltip = hitTooltipFromMatchInfo({ heartHits, nameKwHits, kwHits, reHits, hideOnlyReHits });
        else delete btn.dataset.xfsMatchTooltip;
        if (allHideOnlyReHits.length > 0 && !alreadyBlocked) btn.dataset.xfsHideOnlyTooltip = '命中只隐藏不拉黑规则';
        else delete btn.dataset.xfsHideOnlyTooltip;
        updateInlineBlockButton(btn);
      }
      if (actionableMatched && !alreadyBlocked) {
        matchedHandlesInView.add(key);
        const user = { handle: key, displayName, cats: actionableCats, heartHits: [...heartHits], nameKwHits: [...nameKwHits], kwHits: [...kwHits], reHits: [...reHits], hideOnlyReHits: [...hideOnlyReHits], tweetSnippet };
        matchedUsersCache.set(key, user);
        maybeAutoQueueBrowseMatchedUser(user, art);
      } else {
        matchedHandlesInView.delete(key);
        matchedUsersCache.delete(key);
      }
    });
    updateHideBadge();
    applyHideAll();
  }

  /*
  // Disabled low-follower scoring. Kept for future risk scoring if needed.
  // function lowFollowerReason(handle) {
  //   const item = cachedReferralAccount(handle);
  //   const followers = item?.followers;
  //   return followers !== null && followers <= DEFAULT_LOW_FOLLOWER_THRESHOLD ? followers : null;
  // }
  */

  function referralReason(handle) {
    const item = cachedReferralAccount(handle);
    return item && item.isReferral ? item : null;
  }

  function buttonMatchedReason(btn) {
    if (btn.dataset.xfsMatched === '1') return 'matched';
    if (btn.dataset.xfsReferralAccount === '1') return 'referral';
    if (btn.dataset.xfsHideOnlyMatched === '1') return 'hide_only';
    return '';
  }

  function updateInlineBlockButton(btn) {
    const isBlocked = btn.dataset.xfsState === 'blocked';
    const queueItem = isBlocked ? null : globalBlockQueueItemForHandle(btn.dataset.xfsHandle);
    const queueStatus = queueItem?.status || '';
    const isQueued = ['queued', 'running'].includes(queueStatus);
    const isFailed = queueStatus === 'failed';
    const reason = buttonMatchedReason(btn);
    const isHot = reason !== '';
    const color = reason === 'referral' ? C.referralHot : (reason === 'hide_only' ? C.hideOnlyHot : C.blockRed);
    const stateColor = isBlocked ? C.mute : (isHot ? color : (isQueued ? C.nameKw : (isFailed ? C.blockRed : C.btnBorder)));
    btn.dataset.xfsQueueStatus = queueStatus;
    btn.textContent = isBlocked ? IBTN_CHECK_SVG : (isQueued ? '…' : (isFailed ? '!' : IBTN_BLOCK_SVG));
    btn.style.border = `${isHot && !isBlocked ? 2.5 : 1.5}px solid ${stateColor}`;
    btn.style.color = isBlocked ? C.mute : (isHot ? color : (isQueued ? C.nameKw : (isFailed ? C.blockRed : C.sub)));
    btn.style.boxShadow = !isBlocked && isHot
      ? `0 0 0 3px ${color}45,0 0 10px ${color}38`
      : (!isBlocked && isFailed ? `0 0 0 2px ${C.blockRed}40` : '');
    btn.style.background = isBlocked ? `${C.mute}18` : (isHot ? `${color}22` : (isQueued ? `${C.nameKw}16` : 'transparent'));
    btn.style.opacity = isHot && !isBlocked ? '1' : btn.style.opacity || '1';
    const prefix = reason === 'matched' ? '[匹配过滤] ' : (reason === 'referral' ? '[导流号] ' : (reason === 'hide_only' ? '[只隐藏规则] ' : ''));
    const handle = btn.dataset.xfsHandle || '';
    const details = [btn.dataset.xfsHideOnlyTooltip, btn.dataset.xfsMatchTooltip, btn.dataset.xfsReferralTooltip].filter(Boolean).join('\n');
    const actionTitle = isBlocked
      ? `已拉黑 · 点击取消 @${handle}`
      : (isQueued ? `已在拉黑排队中 · 点击查看详情 @${handle}` : (isFailed ? `排队执行失败 · 点击重新加入 @${handle}` : `拉黑 @${handle}`));
    btn.title = prefix + actionTitle
      + (details ? `\n\n命中规则:\n${details}` : '');
  }

  function setReferralButtons(handle, item) {
    const key = normalizeHandle(handle);
    if (isProtectedVerifiedHandle(key)) {
      clearProtectedVerifiedArticlesInView();
      return;
    }
    const isReferral = !!(item && item.isReferral);
    document.querySelectorAll(`button[data-xfs-handle]`).forEach(btn => {
      if (normalizeHandle(btn.dataset.xfsHandle) !== key) return;
      btn.dataset.xfsReferralAccount = isReferral ? '1' : '0';
      if (isReferral && item.urls?.length) btn.dataset.xfsReferralUrl = item.urls[0];
      if (isReferral) btn.dataset.xfsReferralTooltip = `导流号: ${referralItemDescription(item)}`;
      else delete btn.dataset.xfsReferralTooltip;
      updateInlineBlockButton(btn);
    });
  }

  function applyReferralAccountToArticles(handle) {
    const key = normalizeHandle(handle);
    const item = cachedReferralAccount(key);
    const isReferral = !!(item && item.isReferral);
    const firstArt = document.querySelectorAll('article[data-testid="tweet"]')[0] || null;
    document.querySelectorAll('article[data-testid="tweet"]').forEach(art => {
      if (art === firstArt) return;
      if (isProtectedVerifiedArticle(art)) {
        clearProtectedVerifiedArticleState(art);
        return;
      }
      const artHandle = normalizeHandle(art.dataset.xfsReferralHandle || extractHandleFromArticle(art));
      if (artHandle !== key) return;
      art.dataset.xfsReferralHandle = artHandle;
      art.dataset.xfsReferralAccount = isReferral ? '1' : '0';
      if (isReferral && item.urls?.length) art.dataset.xfsReferralUrl = item.urls[0];
      applyHideToArticle(art);
    });
    setReferralButtons(key, item);
    updateReferralBadge();
  }

  function shouldSkipReferralScan(art, handle) {
    const key = normalizeHandle(handle);
    if (!key) return true;
    if (matchedUsersCache.has(key)) return true;
    return !!(art && art.dataset.xfsHideMatched === '1');
  }

  function scheduleReferralCheck(art, handle, isOP = false, hintText = '') {
    if (!/\/status\/\d/.test(location.pathname) || isListPage()) return;
    const key = normalizeHandle(handle);
    if (!key || isOP || isProtectedVerifiedArticle(art)) {
      art.dataset.xfsReferralAccount = '0';
      art.dataset.xfsReferralQueued = '0';
      if (isProtectedVerifiedArticle(art)) clearProtectedVerifiedArticleState(art);
      return;
    }
    if (shouldSkipReferralScan(art, key)) {
      art.dataset.xfsReferralHandle = key;
      art.dataset.xfsReferralAccount = '0';
      art.dataset.xfsReferralQueued = '0';
      return;
    }
    art.dataset.xfsReferralHandle = key;
    rememberReferralIntentHint(key, hintText || extractDisplayNameFromArticle(art, key));
    const shouldForceRefresh = !!referralIntentHints.get(key) && !referralHintRefreshDone.has(key);

    const cached = cachedReferralAccount(key);
    if (cached !== null && !(shouldForceRefresh && cached.isReferral === false)) {
      applyReferralAccountToArticles(key);
      return;
    }
    if (!autoReferralDetectActive && !hideReferralActive && !youngAccountFilterActive) return;
    if (art.dataset.xfsReferralQueued === '1') return;
    art.dataset.xfsReferralQueued = '1';

    fetchReferralAccount(handle, { forceRefresh: shouldForceRefresh })
      .then(() => {
        if (shouldForceRefresh) referralHintRefreshDone.add(key);
        art.dataset.xfsReferralQueued = '0';
        applyReferralAccountToArticles(key);
      })
      .catch(e => {
        if (shouldForceRefresh && !isReferralRateLimitError(e)) referralHintRefreshDone.add(key);
        art.dataset.xfsReferralQueued = '0';
        if (hideReferralActive) warnReferralLookupFailure(e);
      });
  }

  function applyReferralForVisible() {
    const firstArt = document.querySelectorAll('article[data-testid="tweet"]')[0] || null;
    document.querySelectorAll('article[data-testid="tweet"]').forEach(art => {
      if (art === firstArt) return;
      if (isProtectedVerifiedArticle(art)) {
        clearProtectedVerifiedArticleState(art);
        return;
      }
      const handle = art.dataset.xfsReferralHandle || extractHandleFromArticle(art);
      const key = normalizeHandle(handle);
      if (!key || blockedHandles.has(key)) return;
      scheduleReferralCheck(art, key, false);
    });
    updateReferralBadge();
  }

  async function scanReferralAccountsInView() {
    if (!beginScanMode('referral')) return;
    let handedOffToBlocker = false;
    const skippedMatchedHandles = new Set();
    const progress = showProgressToast('导流号扫描已开始，正在读取当前回复...', C.referralHot);
    try {
      const domReferralHandles = captureReferralAccountsFromProfileDom(document);
      const firstArt = document.querySelectorAll('article[data-testid="tweet"]')[0] || null;
      const handles = [];
      const displayNames = new Map();
      const rememberHandle = (handle, displayName = '') => {
        const key = normalizeHandle(handle);
        if (!key || blockedHandles.has(key) || isProtectedVerifiedHandle(key)) return;
        if (matchedUsersCache.has(key)) {
          skippedMatchedHandles.add(key);
          return;
        }
        if (displayName) displayNames.set(key, displayName);
        if (!handles.includes(key)) handles.push(key);
      };
      document.querySelectorAll('article[data-testid="tweet"]').forEach(art => {
        if (art === firstArt) return;
        if (isProtectedVerifiedArticle(art)) {
          clearProtectedVerifiedArticleState(art);
          return;
        }
        const handle = art.dataset.xfsReferralHandle || extractHandleFromArticle(art);
        const key = normalizeHandle(handle);
        const displayName = key ? extractDisplayNameFromArticle(art, key) : '';
        if (key) rememberReferralIntentHint(key, displayName);
        if (shouldSkipReferralScan(art, key)) {
          skippedMatchedHandles.add(key);
          return;
        }
        rememberHandle(key, displayName);
      });
      domReferralHandles.forEach(handle => rememberHandle(handle));
      if (handles.length === 0) {
        progress.update(skippedMatchedHandles.size > 0
          ? `当前视图没有可扫描的回复用户，已跳过 ${skippedMatchedHandles.size} 个已标记垃圾号`
          : '当前视图没有可扫描的回复用户');
        progress.close(1200);
        return;
      }

      let cachedReferralCount = handles.filter(handle => referralReason(handle)).length;
      const lookupHandles = handles.filter(handle => {
        const cached = cachedReferralAccount(handle);
        return cached === null || cached.isReferral === false;
      });
      if (lookupHandles.length === 0) {
        progress.update(cachedReferralCount > 0
          ? `已识别 ${cachedReferralCount} 个导流号，无需重复查询`
          : '当前视图没有未检查账号，未发现导流号');
      } else {
        progress.update(cachedReferralCount > 0
          ? `已识别 ${cachedReferralCount} 个导流号，补查 ${lookupHandles.length} 个未命中账号`
          : `正在搜索导流号 0/${lookupHandles.length}`);
      }

      let lookupError = null;
      for (let i = 0; i < lookupHandles.length; i++) {
        const handle = lookupHandles[i];
        const forceRefresh = cachedReferralAccount(handle)?.isReferral === false;
        progress.update(cachedReferralCount > 0
          ? `已识别 ${cachedReferralCount} 个，补查 ${i + 1}/${lookupHandles.length}`
          : `正在搜索导流号 ${i + 1}/${lookupHandles.length}`);
        try {
          await fetchReferralAccount(handle, { forceRefresh });
          cachedReferralCount = handles.filter(h => referralReason(h)).length;
        } catch (e) {
          lookupError = lookupError || e;
          if (isReferralRateLimitError(e)) break;
        }
      }
      captureReferralAccountsFromProfileDom(document);
      applyReferralForVisible();
      const users = handles
        .map(handle => {
          const item = cachedReferralAccount(handle);
          return item && item.isReferral ? {
            handle,
            displayName: displayNames.get(handle) || handle,
            cats: new Set(['referral']),
            heartHits: [],
            nameKwHits: [],
            kwHits: [{ kw: item.isYoungAccount && !item.isLinkReferral ? '新号' : '导流号', snippet: referralItemDescription(item) }],
            reHits: [],
            tweetSnippet: referralItemDescription(item),
          } : null;
        })
        .filter(Boolean);
      if (users.length === 0) {
        if (lookupError) {
          progress.update('导流号搜索受限，请稍后再试');
          progress.close(1600);
          warnReferralLookupFailure(lookupError);
        } else {
          progress.update('搜索完成，未发现导流号');
          progress.close(1200);
        }
        return;
      }
      progress.update(lookupHandles.length > 0
        ? `发现 ${users.length} 个导流号，正在加入拉黑排队...`
        : `使用已识别的 ${users.length} 个导流号，正在加入拉黑排队...`);
      progress.close(900);
      handedOffToBlocker = true;
      autoQueueBlockUsers(users, {
        queueSource: 'referral',
        refreshButtonIds: ['xfs-referral-scan-btn'],
        onBlockDone: () => endScanMode('referral'),
      });
    } finally {
      if (!handedOffToBlocker) endScanMode('referral');
    }
  }

  function updateHideBadge() {
    const badge = document.getElementById('xfs-hide-badge');
    if (!badge) return;
    const n = matchedHandlesInView.size;
    badge.textContent = n > 99 ? '99+' : String(n);
    badge.style.display = n > 0 ? 'flex' : 'none';
    if (n > 0) resetContentCleanupButtonsIfComplete();
  }

  function updateReferralBadge() {
    const badge = document.getElementById('xfs-referral-badge');
    if (!badge) return;
    const n = document.querySelectorAll('article[data-testid="tweet"][data-xfs-referral-account="1"]').length;
    badge.textContent = n > 99 ? '99+' : String(n);
    badge.style.display = n > 0 ? 'flex' : 'none';
  }

  function formatBlockedCount(n) {
    return Number(n || 0).toLocaleString('en-US');
  }

  function updatePersistentBlockedBadge() {
    document.querySelectorAll('.xfs-persistent-blocked-count').forEach(badge => {
      badge.textContent = `累计 ${formatBlockedCount(persistentBlockedCount)}`;
      badge.title = '仅供参考：这是 XFS 脚本累计成功拉黑数，不是 X 平台全部已拉黑账号数。只从该统计功能上线后开始记录，保存在本地，不受脚本更新影响。';
    });
  }

  function incrementPersistentBlockedCount(n = 1) {
    const inc = Math.max(0, parseInt(n, 10) || 0);
    if (!inc) return;
    persistentBlockedCount += inc;
    GM_setValue('persistent_blocked_count', persistentBlockedCount);
    updatePersistentBlockedBadge();
  }

  const TOOLBAR_DEFAULT_RIGHT = 18;
  const TOOLBAR_BASE_BOTTOM = 160;

  function clampToolbarPosition() {
    const maxRight = Math.max(8, window.innerWidth - 44);
    toolbarRight = Math.min(Math.max(8, Number(toolbarRight) || TOOLBAR_DEFAULT_RIGHT), maxRight);
    const maxBottom = Math.max(24, window.innerHeight - 292);
    toolbarBaseBottom = Math.min(Math.max(24, Number(toolbarBaseBottom) || TOOLBAR_BASE_BOTTOM), maxBottom);
  }

  function toolbarRightPx(delta = 0) {
    clampToolbarPosition();
    return `${toolbarRight + delta}px`;
  }

  function toolbarBottomPx(bottom) {
    clampToolbarPosition();
    return `${toolbarBaseBottom + (bottom - TOOLBAR_BASE_BOTTOM)}px`;
  }

  function setToolbarPosition(el, bottom, rightDelta = 0) {
    if (!el) return;
    el.style.right = toolbarRightPx(rightDelta);
    el.style.bottom = toolbarBottomPx(bottom);
  }

  function ensureGlobalBlockQueuePanel() {
    if (!document.body) return null;
    let p = document.getElementById('xfs-global-block-queue');
    if (p) return p;
    const pos = readGlobalBlockQueuePosition();
    const size = readFloatingPanelSize(GLOBAL_BLOCK_QUEUE_SIZE_KEY, { width: GLOBAL_BLOCK_QUEUE_PANEL_W, height: 168 });
    p = document.createElement('div');
    p.id = 'xfs-global-block-queue';
    p.style.cssText = [
      'position:fixed', `top:${pos.top}px`, `left:${pos.left}px`,
      `width:${size.width}px`, `height:${size.height}px`, 'box-sizing:border-box', 'padding:7px 8px',
      'background:#f7f9f9', `color:${C.text}`,
      'border:1px solid rgba(207,217,222,0.82)', 'border-radius:8px',
      'box-shadow:0 6px 22px rgba(15,20,25,0.10)',
      'font-size:11px', 'line-height:1.35',
      'resize:both', 'overflow:auto',
      'min-width:136px', 'min-height:118px',
      'max-width:calc(100vw - 16px)', 'max-height:calc(100vh - 16px)',
      `font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif`,
      'z-index:2147483646',
    ].join(';');
    document.body.appendChild(p);
    if (typeof ResizeObserver !== 'undefined') {
      let saveTimer = null;
      const resizeObserver = new ResizeObserver(() => {
        if (!document.body.contains(p)) {
          resizeObserver.disconnect();
          clearTimeout(saveTimer);
          return;
        }
        clearTimeout(saveTimer);
        saveTimer = setTimeout(() => {
          writeFloatingPanelSize(GLOBAL_BLOCK_QUEUE_SIZE_KEY, {
            width: p.offsetWidth,
            height: p.offsetHeight,
          });
          const next = clampGlobalBlockQueuePosition({ left: p.offsetLeft, top: p.offsetTop }, p);
          p.style.left = `${next.left}px`;
          p.style.top = `${next.top}px`;
          writeGlobalBlockQueuePosition(next);
        }, 160);
      });
      resizeObserver.observe(p);
    }
    return p;
  }

  function clampGlobalBlockQueuePosition(pos, p = document.getElementById('xfs-global-block-queue')) {
    const w = p?.offsetWidth || GLOBAL_BLOCK_QUEUE_PANEL_W;
    const h = p?.offsetHeight || 72;
    const maxLeft = Math.max(0, window.innerWidth - w - 8);
    const maxTop = Math.max(0, window.innerHeight - h - 8);
    return {
      left: Math.min(Math.max(0, Number(pos.left) || 0), maxLeft),
      top: Math.min(Math.max(0, Number(pos.top) || 0), maxTop),
    };
  }

  function rectsOverlap(a, b) {
    return !!(a && b && a.left < b.right && a.right > b.left && a.top < b.bottom && a.bottom > b.top);
  }

  function avoidGlobalQueuePanelOverlap(p) {
    const panel = document.getElementById('xfs-panel');
    if (!panel || panel.style.display === 'none') return;
    const pr = panel.getBoundingClientRect();
    const qr = p.getBoundingClientRect();
    if (!rectsOverlap(pr, qr)) return;
    const aboveTop = pr.top - qr.height - 8;
    if (aboveTop < 0 && !globalBlockQueueMinimized()) {
      GM_setValue(GLOBAL_BLOCK_QUEUE_MINIMIZED_KEY, true);
      setTimeout(updateGlobalBlockQueuePanel, 0);
    }
    const next = clampGlobalBlockQueuePosition({ left: pr.left, top: Math.max(0, aboveTop) }, p);
    p.style.left = `${next.left}px`;
    p.style.top = `${next.top}px`;
    p.style.right = 'auto';
    writeGlobalBlockQueuePosition(next);
  }

  function makeGlobalBlockQueuePanelDraggable(p, handle) {
    handle.style.cursor = 'move';
    handle.onpointerdown = e => {
      if (e.button != null && e.button !== 0) return;
      if (e.target.closest('button,a,input,textarea,select')) return;
      e.preventDefault();
      globalQueuePanelDragging = true;
      const startX = e.clientX;
      const startY = e.clientY;
      const startLeft = p.offsetLeft;
      const startTop = p.offsetTop;
      p.setPointerCapture?.(e.pointerId);
      const onMove = ev => {
        const next = clampGlobalBlockQueuePosition({
          left: startLeft + ev.clientX - startX,
          top: startTop + ev.clientY - startY,
        }, p);
        p.style.left = `${next.left}px`;
        p.style.top = `${next.top}px`;
        p.style.right = 'auto';
      };
      const onUp = ev => {
        globalQueuePanelDragging = false;
        p.releasePointerCapture?.(ev.pointerId);
        window.removeEventListener('pointermove', onMove);
        window.removeEventListener('pointerup', onUp);
        avoidGlobalQueuePanelOverlap(p);
        writeGlobalBlockQueuePosition({ left: p.offsetLeft, top: p.offsetTop });
      };
      window.addEventListener('pointermove', onMove);
      window.addEventListener('pointerup', onUp, { once: true });
    };
  }

  function updateGlobalBlockQueuePanel() {
    if (globalQueuePanelDragging) return;
    const minimized = globalBlockQueueMinimized();
    if (!minimized) {
      const panel = document.getElementById('xfs-panel');
      if (panel?.dataset.xfsGlobalQueueView === '1') return;
      if (globalQueuePanelSuppressed) return;
      showGlobalBlockQueueDetailPanel(false);
      return;
    }
    const detailPanel = document.getElementById('xfs-panel');
    if (detailPanel?.dataset.xfsGlobalQueueView === '1') detailPanel.remove();
    if (globalQueuePanelSuppressed) {
      document.getElementById('xfs-global-block-queue')?.remove();
      return;
    }
    const { counts } = globalBlockQueueSummary();
    const paused = globalBlockQueuePaused();
    const active = counts.queued + counts.running;
    const failed = counts.failed || 0;
    const done = counts.done || 0;
    const round = readGlobalQueueRound();
    const cooling = Number(round.cooldownUntil || 0) > Date.now();
    const experimentActive = experimentalBrowseBlockActive();
    const p = ensureGlobalBlockQueuePanel();
    if (!p) return;
    p.style.right = 'auto';
    p.style.padding = '8px';
    const pos = clampGlobalBlockQueuePosition(readGlobalBlockQueuePosition(), p);
    p.style.left = `${pos.left}px`;
    p.style.top = `${pos.top}px`;
    p.style.opacity = '1';
    p.innerHTML = '';
    const hdr = document.createElement('div');
    hdr.style.cssText = 'display:flex;flex-direction:column;align-items:stretch;gap:6px;';
    const topRow = document.createElement('div');
    topRow.style.cssText = 'display:flex;align-items:flex-start;justify-content:space-between;gap:6px;';
    const title = document.createElement('div');
    title.textContent = experimentActive ? '边刷边拉黑' : '拉黑排队';
    title.style.cssText = `flex:1;min-width:0;font-weight:900;font-size:11px;line-height:1.1;color:${experimentActive ? C.blockRed : C.text};white-space:nowrap;overflow:hidden;text-overflow:ellipsis;`;
    const topActions = document.createElement('div');
    topActions.style.cssText = 'display:flex;align-items:center;gap:4px;flex:0 0 auto;';
    const dismissBtn = document.createElement('button');
    dismissBtn.type = 'button';
    dismissBtn.textContent = 'x';
    dismissBtn.title = '关闭此卡片；可从排队详情再次打开';
    dismissBtn.style.cssText = `border:1px solid ${C.btnBorder};border-radius:7px;background:#fff;color:${C.sub};font-size:10px;font-weight:800;padding:2px 5px;cursor:pointer;line-height:1.2;`;
    dismissBtn.onclick = () => {
      globalQueuePanelSuppressed = true;
      p.remove();
    };
    topActions.appendChild(dismissBtn);
    topRow.appendChild(title);
    topRow.appendChild(topActions);
    const stats = document.createElement('div');
    stats.textContent = `排 ${counts.queued} · 执 ${counts.running}`;
    stats.style.cssText = `font-size:10px;font-weight:800;color:${active ? C.text : C.sub};white-space:nowrap;`;
    const doneLine = document.createElement('div');
    doneLine.textContent = `完 ${done} · 失 ${failed}`;
    doneLine.style.cssText = `font-size:10px;font-weight:700;color:${failed ? C.blockRed : C.sub};white-space:nowrap;`;
    const roundLine = document.createElement('div');
    roundLine.textContent = globalQueueRoundText(round);
    roundLine.title = cooling ? '队列正在自动冷却，结束后会继续执行' : `节奏控制：${experimentCooldownSummaryText()}`;
    roundLine.style.cssText = `font-size:10px;font-weight:800;color:${cooling ? C.blockRed : C.sub};white-space:nowrap;`;
    const timing = effectiveExperimentTimingConfig();
    const timingLine = document.createElement('div');
    timingLine.textContent = `时 ${experimentActive ? experimentSlowBlockGapText() : '3-5秒'} · 冷 ${formatGlobalQueueCooldown(timing.shortCooldownMs)}/${formatGlobalQueueCooldown(timing.longCooldownMs)}`;
    timingLine.title = `当前时间设置：间隔 ${experimentActive ? experimentSlowBlockGapText() : '3-5秒'}；每 ${GLOBAL_BLOCK_QUEUE_SHORT_COOLDOWN_EVERY} 个暂停 ${formatGlobalQueueCooldown(timing.shortCooldownMs)}；每 ${GLOBAL_BLOCK_QUEUE_LONG_COOLDOWN_EVERY} 个暂停 ${formatGlobalQueueCooldown(timing.longCooldownMs)}`;
    timingLine.style.cssText = `font-size:9px;font-weight:700;color:${C.sub};white-space:nowrap;overflow:hidden;text-overflow:ellipsis;`;
    const state = document.createElement('span');
    state.textContent = paused ? '暂停' : (cooling ? '冷却中' : (counts.running ? '执行中' : (counts.queued ? '等待' : '空闲')));
    state.style.cssText = `color:${paused || cooling ? C.blockRed : (counts.running ? C.nameKw : C.sub)};font-size:10px;font-weight:800;`;
    const actionBtnCss = `border:1px solid ${C.btnBorder};border-radius:7px;background:#fff;color:${C.sub};font-size:10px;font-weight:800;padding:3px 5px;cursor:pointer;width:100%;`;
    const resumeBtn = document.createElement('button');
    resumeBtn.type = 'button';
    resumeBtn.textContent = paused ? '继续' : '暂停';
    resumeBtn.title = paused ? '重新登录后点击继续拉黑排队' : '暂停拉黑排队';
    resumeBtn.style.cssText = `border:1px solid ${paused ? C.blockRed : C.btnBorder};border-radius:7px;background:${paused ? '#fff1f1' : '#fff'};color:${paused ? C.blockRed : C.sub};font-size:10px;font-weight:800;padding:3px 5px;cursor:pointer;width:100%;`;
    resumeBtn.onclick = () => {
      if (paused && !getCsrf()) {
        showToast('仍未找到登录凭证，请先重新登录 X/Twitter', true);
        return;
      }
      setGlobalBlockQueuePaused(!paused);
    };
    const minBtn = document.createElement('button');
    minBtn.type = 'button';
    minBtn.textContent = '展开';
    minBtn.title = minimized ? '展开拉黑排队' : '最小化拉黑排队';
    minBtn.style.cssText = actionBtnCss;
    minBtn.onclick = () => setGlobalBlockQueueMinimized(!minimized);
    const settingsBtn = document.createElement('button');
    settingsBtn.type = 'button';
    settingsBtn.textContent = '设置';
    settingsBtn.title = '打开边刷边拉黑设置';
    settingsBtn.style.cssText = actionBtnCss;
    settingsBtn.onclick = () => {
      closeToolsPanel();
      showExperimentalBrowseBlockPanel();
    };
    const clearDoneBtn = document.createElement('button');
    clearDoneBtn.type = 'button';
    clearDoneBtn.textContent = '清已完成';
    clearDoneBtn.title = done ? '把已完成数字归零，只清已完成项目' : '当前没有已完成项目';
    clearDoneBtn.style.cssText = actionBtnCss;
    clearDoneBtn.style.opacity = done ? '1' : '0.55';
    clearDoneBtn.style.cursor = done ? 'pointer' : 'default';
    clearDoneBtn.onclick = () => {
      if (!done) return;
      const removed = clearDoneGlobalBlockQueue();
      if (removed) showToast(`已清除 ${removed} 个已完成项目`, false);
    };
    const actionGrid = document.createElement('div');
    actionGrid.style.cssText = 'display:grid;grid-template-columns:repeat(2, minmax(0, 1fr));gap:4px;';
    actionGrid.appendChild(resumeBtn);
    actionGrid.appendChild(minBtn);
    actionGrid.appendChild(settingsBtn);
    actionGrid.appendChild(clearDoneBtn);
    hdr.appendChild(topRow);
    hdr.appendChild(stats);
    hdr.appendChild(doneLine);
    hdr.appendChild(roundLine);
    hdr.appendChild(timingLine);
    hdr.appendChild(state);
    hdr.appendChild(actionGrid);
    makeGlobalBlockQueuePanelDraggable(p, hdr);
    p.appendChild(hdr);
    avoidGlobalQueuePanelOverlap(p);
  }

  function startGlobalBlockQueueMonitor() {
    ensureGlobalBlockQueuePanel();
    syncCompletedGlobalBlocksToThisTab();
    updateGlobalBlockQueuePanel();
    refreshGlobalQueueInlineButtons();
    maybeStartGlobalBlockQueueWorker();
    if (globalQueueUiTimer) clearInterval(globalQueueUiTimer);
    globalQueueUiTimer = setInterval(() => {
      syncCompletedGlobalBlocksToThisTab();
      updateGlobalBlockQueuePanel();
      refreshGlobalQueueInlineButtons();
      maybeStartGlobalBlockQueueWorker();
    }, 1200);
  }

  function updateToolbarPositions() {
    [
      ['xfs-stack-toggle-btn', 160, 0],
      ['xfs-gear-btn', 200, 0],
      ['xfs-referral-scan-btn', 240, 0],
      ['xfs-referral-btn', 280, 0],
      ['xfs-sweep-btn', 320, 0],
      ['xfs-queue-btn', 320, 40],
      ['xfs-btn', 360, 0],
      ['xfs-hide-btn', 400, 0],
      ['xfs-btn-backdrop', 196, -4],
      ['xfs-btn-section-settings', 200, -2],
      ['xfs-btn-section-referral', 236, -2],
      ['xfs-btn-section-content', 316, -2],
      ['xfs-btn-sep-1', 302, 2],
      ['xfs-btn-sep-2', 226, 2],
      ['xfs-tools-panel', 166, 40],
    ].forEach(([id, bottom, rightDelta]) => {
      const el = document.getElementById(id);
      if (!el) return;
      if (bottom == null) el.style.right = toolbarRightPx(rightDelta);
      else setToolbarPosition(el, bottom, rightDelta);
    });
  }

  function saveToolbarPosition() {
    clampToolbarPosition();
    GM_setValue('toolbar_right', toolbarRight);
    GM_setValue('toolbar_base_bottom', toolbarBaseBottom);
  }

  function toolbarExperimentWarningTitle() {
    return '边刷边拉黑模式开启, 可以在设置中关闭';
  }
  function homeToolbarTipText() {
    return '主页精简工具栏：这里只提供设置入口。本工具主要针对回复区，不过滤 Twitter/X 主页主贴。';
  }

  function mkIconBtn(id, svg, title, bottom, color, onclick) {
    const b = document.createElement('button');
    b.id = id;
    b.textContent = svg;
    b.title = title;
    b.style.cssText = [
      'position:fixed', `bottom:${toolbarBottomPx(bottom)}`, `right:${toolbarRightPx()}`,
      'width:32px', 'height:32px', 'border-radius:50%',
      'background:rgba(255,255,255,0.92)',
      'backdrop-filter:blur(4px)', '-webkit-backdrop-filter:blur(4px)',
      `border:2px solid ${color}`, `color:${color}`,
      'cursor:pointer', 'padding:0', 'box-sizing:border-box',
      'display:flex', 'align-items:center', 'justify-content:center',
      'font-family:"Apple Color Emoji","Segoe UI Emoji","Noto Color Emoji",system-ui,sans-serif',
      'font-size:15px', 'line-height:1',
      'z-index:2147483646',
      'box-shadow:0 2px 8px rgba(0,0,0,0.16)',
      'transition:transform 0.15s,box-shadow 0.15s',
    ].join(';');
    b.onmouseenter = () => { if (!b.disabled) { b.style.transform = 'scale(1.12)'; b.style.boxShadow = '0 3px 14px rgba(0,0,0,0.26)'; } };
    b.onmouseleave = () => { b.style.transform = ''; b.style.boxShadow = '0 2px 8px rgba(0,0,0,0.16)'; };
    b.onclick = onclick;
    return b;
  }

  function markCleanupButtonsComplete(ids = ['xfs-btn', 'xfs-sweep-btn', 'xfs-referral-scan-btn', 'xfs-list-btn']) {
    ids.forEach(id => {
      const b = document.getElementById(id);
      if (!b) return;
      b.dataset.xfsCleanupComplete = '1';
      b.disabled = false;
      b.style.opacity = '';
      b.style.pointerEvents = '';
      b.textContent = DONE_SVG;
      b.title = '已加入拉黑排队，点击刷新页面';
      b.style.border = `2px solid ${C.mute}`;
      b.style.color = C.mute;
      b.style.background = `${C.mute}18`;
      b.onclick = () => location.reload();
    });
  }

  function resetCompleteButton(id, icon, title, color, onclick) {
    const b = document.getElementById(id);
    if (!b || b.dataset.xfsCleanupComplete !== '1') return;
    b.dataset.xfsCleanupComplete = '0';
    b.disabled = false;
    b.style.opacity = '';
    b.style.pointerEvents = '';
    b.textContent = icon;
    b.title = title;
    b.style.border = `2px solid ${color}`;
    b.style.color = color;
    b.style.background = 'rgba(255,255,255,0.92)';
    b.onclick = onclick;
  }

  function resetContentCleanupButtonsIfComplete() {
    resetCompleteButton('xfs-btn', BLOCK_SCAN_SVG, '当前视图内容垃圾号自动拉黑', C.blockRed, autoLoadAndScan);
    resetCompleteButton('xfs-sweep-btn', SWEEP_SVG, '整页回复内容垃圾号一网打尽', C.nameKw, () => {
      if (sweepHasRun) {
        sessionStorage.setItem('xfs-auto-sweep', location.pathname);
        location.reload();
      } else {
        sweepHasRun = true;
        sweepAll();
      }
    });
  }

  function closeToolsPanel() {
    document.getElementById('xfs-tools-panel')?.remove();
  }

  function closeRuleTestPanel() {
    document.getElementById('xfs-rule-test-panel')?.remove();
    clearRuleTestHighlights();
  }

  function showRuleTestPanel() {
    document.getElementById('xfs-rule-test-panel')?.remove();
    const p = document.createElement('div');
    p.id = 'xfs-rule-test-panel';
    p.style.cssText = [
      'position:fixed', `right:${toolbarRightPx(40)}`, 'top:92px',
      'width:min(360px, calc(100vw - 24px))', 'max-height:calc(100vh - 112px)',
      'overflow:auto', 'padding:10px',
      'background:rgba(255,255,255,0.97)',
      'backdrop-filter:blur(6px)', '-webkit-backdrop-filter:blur(6px)',
      `border:1px solid ${C.btnBorder}`, 'border-radius:8px',
      'box-shadow:0 4px 18px rgba(0,0,0,0.18)',
      `font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif`,
      `color:${C.text}`, 'font-size:12px',
      'display:flex', 'flex-direction:column', 'gap:9px',
      'z-index:2147483647',
    ].join(';');

    const hdr = document.createElement('div');
    hdr.style.cssText = 'display:flex;align-items:center;gap:8px;';
    const title = document.createElement('div');
    title.textContent = '正则规则测试';
    title.style.cssText = `flex:1;font-size:13px;font-weight:800;color:${C.text};`;
    const close = document.createElement('button');
    close.textContent = '×';
    close.title = '关闭';
    close.style.cssText = `border:none;background:transparent;color:${C.sub};font-size:18px;line-height:1;cursor:pointer;padding:0 4px;`;
    close.onclick = closeRuleTestPanel;
    hdr.appendChild(title);
    hdr.appendChild(close);
    p.appendChild(hdr);

    const intro = document.createElement('div');
    intro.textContent = '这里只做临时测试。请先反复测试并确认命中稳定、没有误命中，再点右侧小按钮加入正式规则，避免误伤正常用户。';
    intro.style.cssText = `font-size:11px;line-height:1.45;color:${C.sub};`;
    p.appendChild(intro);

    function setRuleTestStatus(statusEl, text, color = C.sub) {
      statusEl.textContent = text;
      statusEl.style.color = color;
    }

    function hasKeywordValue(list, value) {
      const target = _normKw(value);
      return list.some(item => _normKw(item) === target);
    }

    function addKeywordFromField(raw, type, statusEl) {
      const value = String(raw || '').trim();
      const label = type === 'name' ? '用户名关键词' : '内容关键词';
      if (!value) {
        setRuleTestStatus(statusEl, `请输入要加入${label}的文本`, C.blockRed);
        return;
      }
      const parsed = _regexPatternParts(value);
      const keyword = (parsed.scope !== 'both' ? parsed.pat : value).trim();
      if (!keyword) {
        setRuleTestStatus(statusEl, `请输入要加入${label}的文本`, C.blockRed);
        return;
      }
      const list = type === 'name' ? SUSPECT_NAME_KWS : SUSPECT_KWS;
      if (hasKeywordValue(list, keyword)) {
        setRuleTestStatus(statusEl, `${label}已存在：${keyword}`, C.sub);
        showToast(`${label}已存在`, false);
        return;
      }
      if (!addManualKeyword(type, keyword)) {
        setRuleTestStatus(statusEl, `${label}已存在：${keyword}`, C.sub);
        showToast(`${label}已存在`, false);
        return;
      }
      setRuleTestStatus(statusEl, `已加入${label}：${keyword}`, C.regexKw);
      showToast(`已加入${label}`, false);
    }

    function addScopedRegexFromField(raw, scope, statusEl) {
      const value = String(raw || '').trim();
      const scopeLabel = scope === 'name' ? '用户名' : '内容';
      const targetScope = scope === 'name' ? 'name' : 'body';
      if (!value) {
        setRuleTestStatus(statusEl, `请输入要加入${scopeLabel}正则的规则`, C.blockRed);
        return;
      }
      const parsed = _regexPatternParts(value);
      if (!parsed.pat) {
        setRuleTestStatus(statusEl, `请输入有效的${scopeLabel}正则`, C.blockRed);
        return;
      }
      if (parsed.scope !== 'both' && parsed.scope !== targetScope) {
        setRuleTestStatus(statusEl, `${scopeLabel}测试框只接受 ${scope === 'name' ? 'name:' : 'content:'} 前缀或不带前缀的正则`, C.blockRed);
        return;
      }
      try {
        new RegExp(parsed.pat, 'mu');
      } catch (err) {
        setRuleTestStatus(statusEl, `正则无效：${err?.message || err}`, C.blockRed);
        return;
      }
      const normalized = `${scope === 'name' ? 'name' : 'content'}:${parsed.pat}`;
      if (SUSPECT_RE_KWS.some(item => String(item).trim() === normalized)) {
        setRuleTestStatus(statusEl, `正则已存在：${normalized}`, C.sub);
        showToast('正则规则已存在', false);
        return;
      }
      if (!addManualKeyword('regex', normalized)) {
        setRuleTestStatus(statusEl, `正则已存在：${normalized}`, C.sub);
        showToast('正则规则已存在', false);
        return;
      }
      setRuleTestStatus(statusEl, `已加入正则：${normalized}`, C.regexKw);
      showToast('已加入正则规则', false);
    }

    function addHideOnlyRegexFromField(raw, statusEl) {
      const value = String(raw || '').trim();
      if (!value) {
        setRuleTestStatus(statusEl, '请输入要加入只隐藏正则的规则', C.blockRed);
        return;
      }
      const parsed = _regexPatternParts(value);
      if (!parsed.pat) {
        setRuleTestStatus(statusEl, '请输入有效的只隐藏正则', C.blockRed);
        return;
      }
      if (parsed.scope !== 'both' && parsed.scope !== 'body') {
        setRuleTestStatus(statusEl, '只隐藏正则只接受 content: 前缀或不带前缀的内容正则', C.blockRed);
        return;
      }
      try {
        new RegExp(parsed.pat, 'mu');
      } catch (err) {
        setRuleTestStatus(statusEl, `正则无效：${err?.message || err}`, C.blockRed);
        return;
      }
      const normalized = `content:${parsed.pat}`;
      if (HIDE_ONLY_RE_KWS.some(item => String(item).trim() === normalized)) {
        setRuleTestStatus(statusEl, `只隐藏正则已存在：${normalized}`, C.sub);
        showToast('只隐藏正则已存在', false);
        return;
      }
      if (!addManualKeyword('hide_only_regex', normalized)) {
        setRuleTestStatus(statusEl, `只隐藏正则已存在：${normalized}`, C.sub);
        showToast('只隐藏正则已存在', false);
        return;
      }
      setRuleTestStatus(statusEl, `已加入只隐藏正则：${normalized}`, C.mute);
      showToast('已加入只隐藏正则', false);
    }

    function mkField(labelText, exampleText, placeholder, accent) {
      const wrap = document.createElement('label');
      wrap.style.cssText = 'display:flex;flex-direction:column;gap:5px;';
      const row = document.createElement('div');
      row.style.cssText = 'display:flex;align-items:center;gap:6px;';
      const label = document.createElement('span');
      label.textContent = labelText;
      label.style.cssText = `font-size:11px;font-weight:700;color:${accent};`;
      const example = document.createElement('button');
      example.type = 'button';
      example.textContent = `例：${exampleText}`;
      example.style.cssText = `border:none;background:transparent;color:${C.regexKw};font-size:10px;cursor:pointer;padding:0;text-align:left;`;
      row.appendChild(label);
      row.appendChild(example);
      const input = document.createElement('textarea');
      input.rows = 2;
      input.placeholder = placeholder;
      input.spellcheck = false;
      input.style.cssText = [
        `border:1px solid ${C.btnBorder}`, 'border-radius:8px',
        'padding:7px 8px', 'font-size:12px', 'line-height:1.35',
        `color:${C.text}`, 'background:#fff', 'resize:vertical',
        'min-height:42px', 'outline:none',
        `font-family:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace`,
      ].join(';');
      example.onclick = () => {
        input.value = exampleText;
        input.focus();
      };
      const quickRow = document.createElement('div');
      quickRow.style.cssText = 'display:flex;gap:6px;align-items:center;justify-content:space-between;';
      wrap.appendChild(row);
      wrap.appendChild(input);
      wrap.appendChild(quickRow);
      return { wrap, input, quickRow };
    }

    function mkFieldTestBtn(text, color) {
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.textContent = text;
      btn.style.cssText = `border:1px solid ${color};background:${color};color:#fff;border-radius:10px;padding:5px 12px;font-size:11px;font-weight:800;line-height:1.45;cursor:pointer;box-shadow:0 3px 10px ${color}33;`;
      return btn;
    }

    function mkMiniBtn(text, color) {
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.textContent = text;
      btn.style.cssText = `border:1px solid ${color};background:#fff;color:${color};border-radius:999px;padding:1px 6px;font-size:9px;font-weight:700;line-height:1.45;cursor:pointer;`;
      return btn;
    }

    const nameField = mkField('测试用户名范围', '互fo', '例如：互fo', C.nameKw);
    const contentField = mkField('测试内容范围', '想找个|哥哥', '例如：想找个|哥哥', C.blockRed);
    p.appendChild(nameField.wrap);
    p.appendChild(contentField.wrap);

    const nameStatus = document.createElement('div');
    nameStatus.textContent = '用户名范围待测试';
    nameStatus.style.cssText = `min-height:16px;font-size:11px;color:${C.sub};line-height:1.35;`;
    const contentStatus = document.createElement('div');
    contentStatus.textContent = '内容范围待测试';
    contentStatus.style.cssText = nameStatus.style.cssText;

    const testNameBtn = mkFieldTestBtn('测试用户名范围', C.nameKw);
    testNameBtn.title = '先测试当前用户名范围正则';
    testNameBtn.onclick = e => {
      e?.preventDefault?.();
      e?.stopPropagation?.();
      const nameRaw = nameField.input.value.trim();
      if (!nameRaw) {
        setRuleTestStatus(nameStatus, '请输入用于测试的用户名正则', C.blockRed);
        return;
      }
      setRuleTestStatus(nameStatus, '正在测试用户名范围...', C.sub);
      let result;
      try {
        result = runNameRuleTest(nameRaw);
      } catch (err) {
        const msg = err?.message || String(err || 'unknown error');
        setRuleTestStatus(nameStatus, `测试失败：${msg}`, C.blockRed);
        showToast(`正则测试失败：${msg}`, true);
        return;
      }
      applyRuleTestResult(result, nameStatus, '用户名', result.nameHits);
    };

    const nameAddGroup = document.createElement('div');
    nameAddGroup.style.cssText = 'display:flex;gap:4px;align-items:center;margin-left:auto;justify-content:flex-end;flex-wrap:wrap;';

    const addNameKwBtn = mkMiniBtn('+ 用户名关键词', C.nameKw);
    addNameKwBtn.title = '把当前输入按普通文本加入用户名关键词';
    addNameKwBtn.onclick = e => {
      e?.preventDefault?.();
      e?.stopPropagation?.();
      addKeywordFromField(nameField.input.value, 'name', nameStatus);
    };
    const addNameReBtn = mkMiniBtn('+ name:正则', C.regexKw);
    addNameReBtn.title = '把当前输入加入正式正则规则，并限定为用户名范围';
    addNameReBtn.onclick = e => {
      e?.preventDefault?.();
      e?.stopPropagation?.();
      addScopedRegexFromField(nameField.input.value, 'name', nameStatus);
    };
    nameField.quickRow.appendChild(testNameBtn);
    nameAddGroup.appendChild(addNameKwBtn);
    nameAddGroup.appendChild(addNameReBtn);
    nameField.quickRow.appendChild(nameAddGroup);

    const testContentBtn = mkFieldTestBtn('测试内容范围', C.blockRed);
    testContentBtn.title = '先测试当前内容范围正则';
    testContentBtn.onclick = e => {
      e?.preventDefault?.();
      e?.stopPropagation?.();
      const contentRaw = contentField.input.value.trim();
      if (!contentRaw) {
        setRuleTestStatus(contentStatus, '请输入用于测试的内容正则', C.blockRed);
        return;
      }
      setRuleTestStatus(contentStatus, '正在测试内容范围...', C.sub);
      let result;
      try {
        result = runContentRuleTest(contentRaw);
      } catch (err) {
        const msg = err?.message || String(err || 'unknown error');
        setRuleTestStatus(contentStatus, `测试失败：${msg}`, C.blockRed);
        showToast(`正则测试失败：${msg}`, true);
        return;
      }
      applyRuleTestResult(result, contentStatus, '内容', result.contentHits);
    };

    const contentAddGroup = document.createElement('div');
    contentAddGroup.style.cssText = 'display:flex;gap:4px;align-items:center;margin-left:auto;justify-content:flex-end;flex-wrap:wrap;';

    const addContentKwBtn = mkMiniBtn('+ 内容关键词', C.blockRed);
    addContentKwBtn.title = '把当前输入按普通文本加入内容关键词';
    addContentKwBtn.onclick = e => {
      e?.preventDefault?.();
      e?.stopPropagation?.();
      addKeywordFromField(contentField.input.value, 'content', contentStatus);
    };
    const addContentReBtn = mkMiniBtn('+ content:正则', C.regexKw);
    addContentReBtn.title = '把当前输入加入正式正则规则，并限定为内容范围';
    addContentReBtn.onclick = e => {
      e?.preventDefault?.();
      e?.stopPropagation?.();
      addScopedRegexFromField(contentField.input.value, 'content', contentStatus);
    };
    const addHideOnlyReBtn = mkMiniBtn('+ 只隐藏正则', C.mute);
    addHideOnlyReBtn.title = '把当前输入加入只隐藏不拉黑的内容正则；适合超级有效但高误伤、只想先隐藏降噪的规则';
    addHideOnlyReBtn.onclick = e => {
      e?.preventDefault?.();
      e?.stopPropagation?.();
      addHideOnlyRegexFromField(contentField.input.value, contentStatus);
    };
    contentField.quickRow.appendChild(testContentBtn);
    contentAddGroup.appendChild(addContentKwBtn);
    contentAddGroup.appendChild(addContentReBtn);
    contentAddGroup.appendChild(addHideOnlyReBtn);
    contentField.quickRow.appendChild(contentAddGroup);

    const caution = document.createElement('div');
    caution.textContent = '建议先拿当前页面多条回复详细测试，确认命中稳定，再决定放哪一类。那种超级有效、能明显降噪、但误伤也偏高的规则，请优先加到“只隐藏正则”，让它只隐藏不拉黑；不要一上来就塞进自动拉黑流，不然很容易把人搞晕、也容易误伤正常用户。';
    caution.style.cssText = `font-size:10px;line-height:1.45;color:${C.blockRed};background:${C.blockRed}10;border:1px solid ${C.blockRed}33;border-radius:8px;padding:7px 8px;`;

    const actions = document.createElement('div');
    actions.style.cssText = 'display:flex;justify-content:flex-end;align-items:center;';
    const clearBtn = document.createElement('button');
    clearBtn.type = 'button';
    clearBtn.textContent = '关闭';
    clearBtn.style.cssText = `background:#fff;color:${C.sub};border:1px solid ${C.btnBorder};border-radius:8px;padding:7px 10px;font-size:12px;cursor:pointer;`;
    clearBtn.onclick = closeRuleTestPanel;

    function applyRuleTestResult(result, statusEl, label, hitCount) {
      if (result.error) {
        setRuleTestStatus(statusEl, result.error, C.blockRed);
        return;
      }
      setRuleTestStatus(statusEl, `${label}：已扫 ${result.scanned} 条 · 命中 ${hitCount}${result.failed ? ` · 跳过 ${result.failed}` : ''}`, hitCount ? C.regexKw : C.sub);
      showToast(`正则测试：${label}命中 ${hitCount}`, false);
    }

    actions.appendChild(clearBtn);
    p.appendChild(nameStatus);
    p.appendChild(contentStatus);
    p.appendChild(caution);
    p.appendChild(actions);
    document.body.appendChild(p);
  }

  function showCategoryHelp() {
    window.alert([
      '两类账号说明',
      '',
      '内容垃圾号：根据回复正文、用户名关键词、正则规则判断。适合处理重复话术、色情/诈骗引流回复。',
      '只隐藏正则：也是按回复正文匹配，但命中后只隐藏，不会仅因这条规则进入自动拉黑候选。它特别适合那些超级有效、能明显压下页面噪音、但误伤也偏高的模式。拿不准的规则先放这里，不要直接进自动拉黑。',
      '',
      '导流号：根据账号主页里的 x.com/twitter.com 导流链接，或“简介含大号且含任意链接”判断。只检查已加载回复用户，受平台接口/限速影响，识别会稍有延迟。',
      '自动检测导流号：低频后台检查滚动加载过的回复用户，命中后右上角拉黑按钮会变橙色。',
      '不自动隐藏/拉黑会员：默认开启。页面上显示会员标识的回复用户不会被隐藏、标红/橙或加入自动拉黑候选；手动拉黑按钮仍可用。',
      '',
      '拉黑新号：默认关闭。开启后，导流扫描会把少于所选天数或晚于所选日期注册的账号也标成橙色，并纳入导流扫描的拉黑候选。日期选择框默认是一个月之前的今天。它需要额外查询主页，慢、容易限流，而且新号不一定是垃圾号，误伤风险较高。',
      '',
      '内容扫描和导流扫描会把命中的账号加入拉黑排队，排队执行以避开平台限流。',
    ].join('\n'));
  }

  function showExperimentalBrowseBlockPanel() {
    document.getElementById('xfs-experiment-panel')?.remove();
    const state = readExperimentalBrowseBlockState();
    const active = experimentalBrowseBlockActive();
    const p = document.createElement('div');
    p.id = 'xfs-experiment-panel';
    p.style.cssText = [
      'position:fixed', `right:${toolbarRightPx(40)}`, `bottom:${toolbarBottomPx(166)}`,
      'width:min(430px, calc(100vw - 24px))', 'box-sizing:border-box',
      'background:rgba(255,255,255,0.98)', `color:${C.text}`,
      `border:1px solid ${C.blockRed}`, 'border-radius:8px',
      'box-shadow:0 8px 28px rgba(0,0,0,0.22)',
      'padding:10px', 'z-index:2147483647',
      `font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif`,
      'font-size:12px', 'display:flex', 'flex-direction:column', 'gap:8px',
    ].join(';');
    const title = document.createElement('div');
    title.textContent = '边刷边拉黑';
    title.style.cssText = `font-size:13px;font-weight:800;color:${C.blockRed};`;
    const warn = document.createElement('div');
    warn.textContent = '危险：该功能会在浏览时把命中当前关键词/正则规则的账号自动加入拉黑排队，可能大量误伤。只有在这些规则长期测试低误伤率后才应该开启。';
    warn.style.cssText = `padding:8px;border:1px solid ${C.blockRed};border-radius:8px;background:#fff1f1;color:${C.blockRed};line-height:1.45;font-weight:700;`;
    const note = document.createElement('div');
    note.style.cssText = `color:${C.sub};line-height:1.45;`;
    const timingWrap = document.createElement('div');
    timingWrap.style.cssText = `border:1px solid ${C.btnBorder};border-radius:8px;padding:8px;background:#fff;display:flex;flex-direction:column;gap:7px;`;
    const timingTitle = document.createElement('div');
    timingTitle.textContent = '时间设置';
    timingTitle.style.cssText = `font-size:12px;font-weight:800;color:${C.text};`;
    const timingSummary = document.createElement('div');
    timingSummary.style.cssText = `font-size:10px;line-height:1.45;color:${C.sub};`;
    const timingAdvice = document.createElement('div');
    timingAdvice.textContent = `如果经常被平台登出，说明风控偏紧。建议先把时间至少调到：基础间隔 15 秒、每 ${GLOBAL_BLOCK_QUEUE_SHORT_COOLDOWN_EVERY} 个暂停 30 秒、每 ${GLOBAL_BLOCK_QUEUE_LONG_COOLDOWN_EVERY} 个暂停 5 分钟；如果还是容易掉登录，就继续往上加。可以另开一个 X/Twitter 页面挂后台，让它慢慢跑。`;
    timingAdvice.style.cssText = `font-size:10px;line-height:1.45;color:${C.sub};padding:6px 7px;border-radius:7px;background:${C.catBg};`;
    const timingGrid = document.createElement('div');
    timingGrid.style.cssText = 'display:grid;grid-template-columns:minmax(0,1fr) 96px;gap:6px 8px;align-items:center;';

    function mkTimingInput(labelText, unitText, min, max) {
      const label = document.createElement('div');
      label.textContent = labelText;
      label.style.cssText = `font-size:11px;color:${C.text};`;
      const wrap = document.createElement('label');
      wrap.style.cssText = 'display:flex;align-items:center;gap:6px;';
      const input = document.createElement('input');
      input.type = 'number';
      input.min = String(min);
      input.max = String(max);
      input.step = '1';
      input.style.cssText = `width:56px;border:1px solid ${C.btnBorder};border-radius:7px;background:#fff;color:${C.text};font-size:11px;padding:4px 6px;`;
      const unit = document.createElement('span');
      unit.textContent = unitText;
      unit.style.cssText = `font-size:11px;color:${C.sub};white-space:nowrap;`;
      wrap.appendChild(input);
      wrap.appendChild(unit);
      timingGrid.appendChild(label);
      timingGrid.appendChild(wrap);
      return input;
    }

    const slowInput = mkTimingInput('基础间隔', '秒', 15, 600);
    const shortInput = mkTimingInput(`每 ${GLOBAL_BLOCK_QUEUE_SHORT_COOLDOWN_EVERY} 个暂停时长`, '秒', 30, 1800);
    const longInput = mkTimingInput(`每 ${GLOBAL_BLOCK_QUEUE_LONG_COOLDOWN_EVERY} 个暂停时长`, '分钟', 5, 120);

    function syncTimingUi() {
      const current = effectiveExperimentTimingConfig();
      const expiresText = state.expiresAt ? new Date(state.expiresAt).toLocaleString() : '未开启';
      slowInput.value = String(Math.round(current.slowBlockDelayMs / 1000));
      shortInput.value = String(Math.round(current.shortCooldownMs / 1000));
      longInput.value = String(Math.round(current.longCooldownMs / 60000));
      timingSummary.textContent = `当前生效：间隔 ${experimentSlowBlockGapText()}；${experimentCooldownSummaryText()}。实际执行时还会额外加随机抖动。这里只改时长，不改每 ${GLOBAL_BLOCK_QUEUE_SHORT_COOLDOWN_EVERY} 个 / 每 ${GLOBAL_BLOCK_QUEUE_LONG_COOLDOWN_EVERY} 个的触发次数。`;
      note.textContent = active
        ? `当前已开启。过期时间：${expiresText}。执行拉黑会使用你当前设置的时间，并强制跳过会员账号。`
        : '开启后仅在当前浏览周期有效；所有 X/Twitter 标签页共享状态。关闭所有标签页后下次进入会自动关闭，最晚 24 小时自动关闭。';
    }

    function persistTimingUi() {
      saveExperimentTimingConfig({
        slowBlockDelayMs: Number(slowInput.value || 0) * 1000,
        shortCooldownMs: Number(shortInput.value || 0) * 1000,
        longCooldownMs: Number(longInput.value || 0) * 60 * 1000,
      });
      syncTimingUi();
    }

    [slowInput, shortInput, longInput].forEach(input => {
      input.onchange = persistTimingUi;
      input.onblur = persistTimingUi;
    });
    timingWrap.appendChild(timingTitle);
    timingWrap.appendChild(timingGrid);
    timingWrap.appendChild(timingSummary);
    timingWrap.appendChild(timingAdvice);
    syncTimingUi();
    const confirmRow = document.createElement('label');
    confirmRow.style.cssText = 'display:flex;align-items:flex-start;gap:7px;line-height:1.35;';
    const confirm = document.createElement('input');
    confirm.type = 'checkbox';
    confirm.style.cssText = 'margin-top:2px;accent-color:#f4212e;';
    const confirmText = document.createElement('span');
    confirmText.textContent = '我确认这些关键词/正则已经长期测试为低误伤，并接受误伤账号被加入拉黑排队的风险。';
    confirmRow.appendChild(confirm);
    confirmRow.appendChild(confirmText);
    const actions = document.createElement('div');
    actions.style.cssText = 'display:flex;gap:8px;align-items:center;';
    const enableBtn = document.createElement('button');
    enableBtn.type = 'button';
    enableBtn.textContent = active ? '重新开启 24 小时' : '开启边刷边拉黑';
    enableBtn.style.cssText = `flex:1;background:${C.blockRed};color:#fff;border:none;border-radius:8px;padding:7px 10px;font-size:12px;font-weight:800;cursor:pointer;`;
    enableBtn.onclick = () => {
      if (!confirm.checked) {
        showToast('必须先确认误伤风险', true);
        return;
      }
      enableExperimentalBrowseBlock();
      p.remove();
    };
    const closeBtn = document.createElement('button');
    closeBtn.type = 'button';
    closeBtn.textContent = '收起';
    closeBtn.style.cssText = `background:#fff;color:${C.sub};border:1px solid ${C.btnBorder};border-radius:8px;padding:7px 10px;font-size:12px;cursor:pointer;`;
    closeBtn.onclick = () => p.remove();
    actions.appendChild(enableBtn);
    actions.appendChild(closeBtn);
    p.appendChild(title);
    p.appendChild(warn);
    p.appendChild(note);
    p.appendChild(timingWrap);
    p.appendChild(confirmRow);
    p.appendChild(actions);
    document.body.appendChild(p);
  }

  function showToolsPanel() {
    closeToolsPanel();
    const panelBottom = toolbarBottomPx(166);
    const p = document.createElement('div');
    p.id = 'xfs-tools-panel';
    p.style.cssText = [
      'position:fixed', `right:${toolbarRightPx(40)}`, `bottom:${panelBottom}`,
      'width:min(430px, calc(100vw - 24px))', `max-height:calc(100vh - ${panelBottom} - 16px)`, 'overflow:auto', 'padding:8px',
      'background:rgba(255,255,255,0.96)',
      'backdrop-filter:blur(6px)', '-webkit-backdrop-filter:blur(6px)',
      `border:1px solid ${C.btnBorder}`,
      'border-radius:8px',
      'box-shadow:0 4px 18px rgba(0,0,0,0.18)',
      `font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif`,
      `color:${C.text}`, 'font-size:12px',
      'display:flex', 'flex-direction:column', 'gap:6px',
      'z-index:2147483647',
    ].join(';');

    const title = document.createElement('div');
    title.textContent = '设置 / 工具';
    title.style.cssText = `font-size:12px;font-weight:700;color:${C.sub};padding:0 2px 2px;`;
    p.appendChild(title);

    const grid = document.createElement('div');
    grid.style.cssText = [
      'display:grid',
      'grid-template-columns:repeat(2, minmax(0, 1fr))',
      'gap:6px',
      'align-items:start',
    ].join(';');

    function mkToolBtn(text, onclick) {
      const b = document.createElement('button');
      b.textContent = text;
      b.style.cssText = `background:#fff;color:${C.text};border:1px solid ${C.btnBorder};border-radius:8px;padding:6px 9px;font-size:12px;font-weight:600;text-align:left;cursor:pointer;`;
      b.onclick = () => { onclick(); };
      return b;
    }

    function refreshYoungAccountControls() {
      youngAccountBtn.textContent = `拉黑新号：${youngAccountFilterActive ? '开' : '关'}`;
      youngAccountBtn.style.borderColor = youngAccountFilterActive ? C.blockRed : C.btnBorder;
      youngAccountBtn.style.color = youngAccountFilterActive ? C.blockRed : C.sub;
      youngAccountBtn.style.background = youngAccountFilterActive ? '#fff1f1' : '#fff';
      youngDetailWrap.style.display = youngAccountFilterActive ? 'flex' : 'none';
      youngModeSelect.value = youngAccountCutoffMode;
      youngAccountSelect.value = String(youngAccountMaxAgeDays);
      youngDateInput.value = youngAccountCutoffDate;
      youngAccountSelect.style.display = youngAccountCutoffMode === 'days' ? '' : 'none';
      youngDateInput.style.display = youngAccountCutoffMode === 'date' ? '' : 'none';
      youngRowText.textContent = youngAccountCutoffMode === 'date' ? '晚于' : '少于';
    }

    function refreshVerifiedProtectionControls() {
      verifiedProtectBtn.textContent = `不自动隐藏/拉黑会员：${skipVerifiedAccountsActive ? '开' : '关'}`;
      verifiedProtectBtn.style.borderColor = skipVerifiedAccountsActive ? C.mute : C.btnBorder;
      verifiedProtectBtn.style.color = skipVerifiedAccountsActive ? C.mute : C.sub;
      verifiedProtectBtn.style.background = skipVerifiedAccountsActive ? '#effaf7' : '#fff';
      verifiedProtectBtn.title = '默认开启。页面上显示会员标识的回复用户不会被隐藏、标红/橙或加入自动拉黑候选；手动拉黑按钮仍可用。';
    }

    function refreshHideOnlyRulesControls() {
      hideOnlyRulesBtn.textContent = `只隐藏不拉黑关键字：${hideOnlyRulesActive ? '开' : '关'}`;
      hideOnlyRulesBtn.style.borderColor = hideOnlyRulesActive ? C.mute : C.btnBorder;
      hideOnlyRulesBtn.style.color = hideOnlyRulesActive ? C.mute : C.sub;
      hideOnlyRulesBtn.style.background = hideOnlyRulesActive ? '#effaf7' : '#fff';
      hideOnlyRulesBtn.title = '默认开启。这个类别专门留给“超级有效、但误伤偏高”的规则做隐藏降噪。关闭后，“只隐藏正则”会暂时失效；普通关键词和普通正则不受影响。';
    }

    const autoReferralBtn = mkToolBtn('', () => {
      autoReferralDetectActive = !autoReferralDetectActive;
      GM_setValue('auto_referral_detect', autoReferralDetectActive);
      autoReferralBtn.textContent = `自动检测导流号：${autoReferralDetectActive ? '开' : '关'}`;
      autoReferralBtn.style.borderColor = autoReferralDetectActive ? C.referralHot : C.btnBorder;
      autoReferralBtn.style.color = autoReferralDetectActive ? C.referralHot : C.sub;
      autoReferralBtn.style.background = autoReferralDetectActive ? '#fff8ed' : '#fff';
      if (autoReferralDetectActive) applyReferralForVisible();
      showToast(autoReferralDetectActive ? '自动检测导流号已开启' : '自动检测导流号已关闭', false);
    });
    autoReferralBtn.textContent = `自动检测导流号：${autoReferralDetectActive ? '开' : '关'}`;
    autoReferralBtn.style.borderColor = autoReferralDetectActive ? C.referralHot : C.btnBorder;
    autoReferralBtn.style.color = autoReferralDetectActive ? C.referralHot : C.sub;
    autoReferralBtn.style.background = autoReferralDetectActive ? '#fff8ed' : '#fff';

    const verifiedProtectBtn = mkToolBtn('', () => {
      skipVerifiedAccountsActive = !skipVerifiedAccountsActive;
      GM_setValue('skip_verified_accounts', skipVerifiedAccountsActive);
      refreshVerifiedProtectionControls();
      if (skipVerifiedAccountsActive) {
        clearProtectedVerifiedArticlesInView();
      } else {
        document.querySelectorAll('article[data-testid="tweet"]').forEach(art => {
          if (articleHasVerifiedBadge(art)) delete art.dataset.xfsIbtn;
        });
        reapplyContentRulesForVisible();
        applyReferralForVisible();
        injectInlineButtons();
        applyHideAll();
      }
      showToast(skipVerifiedAccountsActive ? '会员保护已开启' : '会员保护已关闭', false);
    });
    refreshVerifiedProtectionControls();

    const hideOnlyRulesBtn = mkToolBtn('', () => {
      hideOnlyRulesActive = !hideOnlyRulesActive;
      GM_setValue('hide_only_rules_active', hideOnlyRulesActive);
      refreshHideOnlyRulesControls();
      reapplyContentRulesForVisible();
      applyHideAll();
      refreshKeywordPanelIfOpen();
      showToast(hideOnlyRulesActive ? '只隐藏不拉黑关键字已开启' : '只隐藏不拉黑关键字已关闭', false);
    });
    refreshHideOnlyRulesControls();

    function refreshAiReviewControls() {
      aiReviewBtn.textContent = `AI 复核：${aiReviewActive ? '开' : '关'}`;
      aiReviewBtn.style.borderColor = aiReviewActive ? C.nameKw : C.btnBorder;
      aiReviewBtn.style.color = aiReviewActive ? C.nameKw : C.sub;
      aiReviewBtn.style.background = aiReviewActive ? '#f2fbfc' : '#fff';
      aiAutoRuleBtn.textContent = `AI 自动改规则：${aiAutoRulesActive ? '开' : '关'}`;
      aiAutoRuleBtn.style.borderColor = aiAutoRulesActive ? C.regexKw : C.btnBorder;
      aiAutoRuleBtn.style.color = aiAutoRulesActive ? C.regexKw : C.sub;
      aiAutoRuleBtn.style.background = aiAutoRulesActive ? '#f2fbfc' : '#fff';
      aiReviewModelInput.value = aiReviewModel();
      aiReviewKeyInput.value = aiReviewApiKey();
      aiReviewStatus.textContent = aiReviewConfigured()
        ? `模型 ${aiReviewModelInput.value || aiReviewModel()} · key 已配置 · 学习样本 ${aiLearningExamples.length} 条 · 自动改规则 ${aiAutoRulesActive ? '开' : '关'}`
        : (aiReviewActive ? '已开启，但尚未配置 API key' : '默认关闭；开启后，非用户名命中的可疑账号会先送 AI 复核。');
      aiReviewStatus.title = aiReviewStatus.textContent;
    }
    refreshAiReviewControlsFn = refreshAiReviewControls;

    const aiReviewWrap = document.createElement('div');
    aiReviewWrap.style.cssText = `border:1px solid ${C.nameKw};background:#f7feff;border-radius:8px;padding:7px;display:flex;flex-direction:column;gap:6px;`;
    const aiReviewTitle = document.createElement('div');
    aiReviewTitle.textContent = 'AI 复核';
    aiReviewTitle.style.cssText = `font-size:11px;font-weight:800;color:${C.nameKw};`;
    const aiReviewNote = document.createElement('div');
    aiReviewNote.textContent = '用户名/昵称问题直接拉黑；其余可疑账号交给 AI 复核。AI 只做 block / hide / ignore 三选一。';
    aiReviewNote.style.cssText = `font-size:10px;line-height:1.35;color:${C.sub};`;
    const aiReviewBtn = mkToolBtn('', () => {
      aiReviewActive = !aiReviewActive;
      GM_setValue(AI_REVIEW_ENABLED_KEY, aiReviewActive);
      refreshAiReviewControls();
      showToast(aiReviewActive ? 'AI 复核已开启' : 'AI 复核已关闭', false);
    });
    const aiAutoRuleBtn = mkToolBtn('', () => {
      aiAutoRulesActive = !aiAutoRulesActive;
      GM_setValue(AI_AUTO_RULES_KEY, aiAutoRulesActive);
      refreshAiReviewControls();
      showToast(aiAutoRulesActive ? 'AI 自动改规则已开启' : 'AI 自动改规则已关闭', false);
    });
    const aiReviewModelInput = document.createElement('input');
    aiReviewModelInput.type = 'text';
    aiReviewModelInput.placeholder = AI_REVIEW_DEFAULT_MODEL;
    aiReviewModelInput.style.cssText = `border:1px solid ${C.btnBorder};border-radius:8px;padding:5px 8px;font-size:10px;width:100%;box-sizing:border-box;`;
    aiReviewModelInput.onchange = () => {
      const next = normalizeAiReviewModel(aiReviewModelInput.value);
      aiReviewModelInput.value = next;
      GM_setValue(AI_REVIEW_MODEL_KEY, next);
      refreshAiReviewControls();
      showToast(`AI 模型已保存：${next}`, false);
    };
    const aiReviewKeyInput = document.createElement('input');
    aiReviewKeyInput.type = 'password';
    aiReviewKeyInput.placeholder = 'OpenAI API key';
    aiReviewKeyInput.autocomplete = 'off';
    aiReviewKeyInput.style.cssText = `border:1px solid ${C.btnBorder};border-radius:8px;padding:5px 8px;font-size:10px;width:100%;box-sizing:border-box;`;
    aiReviewKeyInput.onchange = () => {
      const next = String(aiReviewKeyInput.value || '').trim();
      GM_setValue(AI_REVIEW_API_KEY_KEY, next);
      refreshAiReviewControls();
      showToast(next ? 'AI API key 已保存' : 'AI API key 已清空', false);
    };
    const aiReviewClearBtn = mkToolBtn('清除 API key', () => {
      aiReviewKeyInput.value = '';
      GM_setValue(AI_REVIEW_API_KEY_KEY, '');
      refreshAiReviewControls();
      showToast('AI API key 已清空', false);
    });
    const aiReviewStatus = document.createElement('div');
    aiReviewStatus.style.cssText = `font-size:10px;line-height:1.35;color:${C.sub};word-break:break-word;`;
    aiReviewWrap.appendChild(aiReviewTitle);
    aiReviewWrap.appendChild(aiReviewBtn);
    aiReviewWrap.appendChild(aiAutoRuleBtn);
    aiReviewWrap.appendChild(aiReviewModelInput);
    aiReviewWrap.appendChild(aiReviewKeyInput);
    aiReviewWrap.appendChild(aiReviewClearBtn);
    aiReviewWrap.appendChild(aiReviewStatus);
    refreshAiReviewControls();

    const aiLearningWrap = document.createElement('div');
    aiLearningWrap.style.cssText = `border:1px solid ${C.regexKw};background:#f6fbff;border-radius:8px;padding:7px;display:flex;flex-direction:column;gap:6px;`;
    const aiLearningTitle = document.createElement('div');
    aiLearningTitle.textContent = 'AI 学习调试';
    aiLearningTitle.style.cssText = `font-size:11px;font-weight:800;color:${C.regexKw};`;
    const aiLearningStatus = document.createElement('div');
    aiLearningStatus.style.cssText = `font-size:10px;line-height:1.35;color:${C.sub};word-break:break-word;`;
    const aiLearningList = document.createElement('div');
    aiLearningList.style.cssText = `display:flex;flex-direction:column;gap:4px;max-height:140px;overflow:auto;padding-right:2px;`;
    const aiLearningRefreshBtn = mkToolBtn('刷新学习样本', () => {
      refreshAiReviewControls();
      refreshAiLearningControls();
      showToast('AI 学习样本已刷新', false);
    });
    const aiLearningClearBtn = mkToolBtn('清空学习样本', () => {
      if (!window.confirm('清空所有 AI 学习样本和最近一次写入记录？')) return;
      aiLearningExamples = [];
      GM_setValue(AI_LEARNING_EXAMPLES_KEY, []);
      GM_setValue(AI_LEARNING_LAST_KEY, null);
      refreshAiReviewControls();
      refreshAiLearningControls();
      showToast('AI 学习样本已清空', false);
    });
    function refreshAiLearningControls() {
      const last = loadAiLearningLast();
      const rawCount = Array.isArray(GM_getValue(AI_LEARNING_EXAMPLES_KEY, [])) ? GM_getValue(AI_LEARNING_EXAMPLES_KEY, []).length : 0;
      aiLearningStatus.textContent = last
        ? `存储 ${aiLearningExamples.length} 条 / 原始 ${rawCount} 条 · 最近一次 ${last.label} @${last.handle || '-'}${last.source ? ` · ${last.source}` : ''}${last.reason ? ` · ${last.reason}` : ''}`
        : `存储 ${aiLearningExamples.length} 条 / 原始 ${rawCount} 条 · 还没有写入过学习样本`;
      aiLearningStatus.title = aiLearningStatus.textContent;
      aiLearningList.textContent = '';
      const items = aiLearningExamples.slice(0, 8);
      if (!items.length) {
        const empty = document.createElement('div');
        empty.textContent = '暂无学习样本';
        empty.style.cssText = `font-size:10px;color:${C.sub};padding:4px 0;`;
        aiLearningList.appendChild(empty);
        return;
      }
      items.forEach(item => {
        const row = document.createElement('div');
        row.style.cssText = `padding:4px 6px;border:1px solid ${C.border};border-radius:6px;background:#fff;font-size:10px;line-height:1.35;word-break:break-word;`;
        row.textContent = `${item.label} · @${item.handle || '-'}${item.displayName ? ` (${item.displayName})` : ''}${item.source ? ` · ${item.source}` : ''}${item.reason ? ` · ${item.reason}` : ''}`;
        aiLearningList.appendChild(row);
      });
    }
    refreshAiLearningControlsFn = refreshAiLearningControls;
    aiLearningWrap.appendChild(aiLearningTitle);
    aiLearningWrap.appendChild(aiLearningRefreshBtn);
    aiLearningWrap.appendChild(aiLearningClearBtn);
    aiLearningWrap.appendChild(aiLearningStatus);
    aiLearningWrap.appendChild(aiLearningList);
    refreshAiLearningControls();

    function refreshRemoteRulesControls() {
      remoteRulesBtn.textContent = `远程规则订阅：${remoteRulesActive ? '开' : '关'}`;
      remoteRulesBtn.style.borderColor = remoteRulesActive ? C.nameKw : C.btnBorder;
      remoteRulesBtn.style.color = remoteRulesActive ? C.nameKw : C.sub;
      remoteRulesBtn.style.background = remoteRulesActive ? '#f2fbfc' : '#fff';
      remoteUpdateBtn.textContent = remoteRulesFetching ? '正在更新...' : '立即更新远程规则';
      remoteUpdateBtn.disabled = !remoteRulesActive || remoteRulesFetching;
      remoteUpdateBtn.style.opacity = remoteUpdateBtn.disabled ? '0.55' : '1';
      remoteUpdateBtn.style.cursor = remoteUpdateBtn.disabled ? 'default' : 'pointer';
      remoteStatus.textContent = remoteRulesActive
        ? `${remoteRulesSummary()} · ${remoteRulesFetchedText()}${remoteRulesLastChange ? ` · ${remoteRulesLastChange}` : ''}`
        : '默认关闭；开启后每小时从 GitHub 拉取一次。';
      remoteStatus.title = remoteRulesLastError ? `上次失败：${remoteRulesLastError}` : remoteStatus.textContent;
    }

    const remoteWrap = document.createElement('div');
    remoteWrap.style.cssText = `border:1px solid ${C.nameKw};background:#f7feff;border-radius:8px;padding:7px;display:flex;flex-direction:column;gap:6px;`;
    const remoteTitle = document.createElement('div');
    remoteTitle.textContent = '远程规则订阅';
    remoteTitle.style.cssText = `font-size:11px;font-weight:800;color:${C.nameKw};`;
    const remoteNote = document.createElement('div');
    remoteNote.textContent = '默认关闭。开启后同步内容、用户名、正则、只隐藏正则和导流号主页正则五类远程规则；失败时沿用本地缓存。其中“只隐藏正则”适合那些超级有效但高误伤、应先用于隐藏降噪的规则。';
    remoteNote.style.cssText = `font-size:10px;line-height:1.35;color:${C.sub};`;
    const remoteStatus = document.createElement('div');
    remoteStatus.style.cssText = `font-size:10px;line-height:1.35;color:${C.sub};word-break:break-word;`;
    const remoteRulesBtn = mkToolBtn('', () => {
      remoteRulesActive = !remoteRulesActive;
      GM_setValue('remote_rules_active', remoteRulesActive);
      reloadKws();
      refreshKeywordPanelIfOpen();
      refreshRemoteRulesControls();
      showToast(remoteRulesActive ? '远程规则订阅已开启' : '远程规则订阅已关闭', false);
      if (remoteRulesActive) {
        refreshRemoteRules({ force: true, silent: false }).then(refreshRemoteRulesControls);
        refreshRemoteRulesControls();
      }
    });
    const remoteUpdateBtn = mkToolBtn('', () => {
      refreshRemoteRulesControls();
      refreshRemoteRules({ force: true, silent: false }).then(refreshRemoteRulesControls);
    });
    remoteUpdateBtn.title = '手动从 GitHub 拉取最新远程规则';
    remoteWrap.appendChild(remoteTitle);
    remoteWrap.appendChild(remoteRulesBtn);
    remoteWrap.appendChild(remoteUpdateBtn);
    remoteWrap.appendChild(remoteStatus);
    remoteWrap.appendChild(remoteNote);
    refreshRemoteRulesControls();

    const youngWrap = document.createElement('div');
    youngWrap.style.cssText = `border:1px solid ${C.blockRed};background:#fff7f7;border-radius:8px;padding:7px;display:flex;flex-direction:column;gap:6px;`;
    const youngTitle = document.createElement('div');
    youngTitle.textContent = '高误伤：屏蔽新用户';
    youngTitle.style.cssText = `font-size:11px;font-weight:800;color:${C.blockRed};`;
    const youngNote = document.createElement('div');
    youngNote.textContent = '新号会进入橙标和导流扫描拉黑候选；需要逐个查主页，速度慢，容易限流，新号不一定是垃圾号。';
    youngNote.style.cssText = `font-size:10px;line-height:1.35;color:${C.sub};`;
    const youngAccountBtn = mkToolBtn('', () => {
      youngAccountFilterActive = !youngAccountFilterActive;
      GM_setValue('young_account_filter_active', youngAccountFilterActive);
      refreshYoungAccountControls();
      if (youngAccountFilterActive) applyReferralForVisible();
      showToast(youngAccountFilterActive ? `拉黑新号已开启：${youngAccountRuleLabel()}` : '拉黑新号已关闭', false);
    });
    const youngDetailWrap = document.createElement('div');
    youngDetailWrap.style.cssText = 'display:flex;flex-direction:column;gap:6px;';
    const youngRow = document.createElement('label');
    youngRow.style.cssText = `display:flex;align-items:center;gap:6px;font-size:11px;color:${C.text};`;
    const youngModeSelect = document.createElement('select');
    youngModeSelect.style.cssText = `width:100%;border:1px solid ${C.btnBorder};border-radius:7px;background:#fff;color:${C.text};font-size:11px;padding:4px;`;
    [
      ['days', '按天数'],
      ['date', '按日期'],
    ].forEach(([value, label]) => {
      const opt = document.createElement('option');
      opt.value = value;
      opt.textContent = label;
      youngModeSelect.appendChild(opt);
    });
    youngModeSelect.onchange = () => {
      youngAccountCutoffMode = normalizeYoungAccountCutoffMode(youngModeSelect.value);
      GM_setValue('young_account_cutoff_mode', youngAccountCutoffMode);
      referralCache.forEach((item, key) => {
        const effective = materializeReferralItem(item);
        referralCache.set(key, { ...item, isReferral: effective.isReferral, isYoungAccount: effective.isYoungAccount, accountAgeDays: effective.accountAgeDays });
      });
      saveReferralCache();
      applyReferralForVisible();
      refreshYoungAccountControls();
      showToast(`拉黑新号已切换为${youngAccountCutoffMode === 'date' ? '按日期' : '按天数'}`, false);
    };
    const youngAccountSelect = document.createElement('select');
    youngAccountSelect.style.cssText = `flex:1;min-width:0;border:1px solid ${C.btnBorder};border-radius:7px;background:#fff;color:${C.text};font-size:11px;padding:4px;`;
    YOUNG_ACCOUNT_DAY_OPTIONS.forEach(days => {
      const opt = document.createElement('option');
      opt.value = String(days);
      opt.textContent = `${days} 天`;
      youngAccountSelect.appendChild(opt);
    });
    const youngDateInput = document.createElement('input');
    youngDateInput.type = 'date';
    youngDateInput.max = toDateInputValue(new Date());
    youngDateInput.style.cssText = `flex:1;min-width:0;border:1px solid ${C.btnBorder};border-radius:7px;background:#fff;color:${C.text};font-size:11px;padding:4px;`;
    youngAccountSelect.onchange = () => {
      youngAccountMaxAgeDays = normalizeYoungAccountDays(youngAccountSelect.value);
      GM_setValue('young_account_max_age_days', youngAccountMaxAgeDays);
      referralCache.forEach((item, key) => {
        const effective = materializeReferralItem(item);
        referralCache.set(key, { ...item, isReferral: effective.isReferral, isYoungAccount: effective.isYoungAccount, accountAgeDays: effective.accountAgeDays });
      });
      saveReferralCache();
      applyReferralForVisible();
      refreshYoungAccountControls();
      showToast(`拉黑新号阈值已设为 ${youngAccountMaxAgeDays} 天`, false);
    };
    youngDateInput.onchange = () => {
      youngAccountCutoffDate = normalizeDateInputValue(youngDateInput.value);
      GM_setValue('young_account_cutoff_date', youngAccountCutoffDate);
      referralCache.forEach((item, key) => {
        const effective = materializeReferralItem(item);
        referralCache.set(key, { ...item, isReferral: effective.isReferral, isYoungAccount: effective.isYoungAccount, accountAgeDays: effective.accountAgeDays });
      });
      saveReferralCache();
      applyReferralForVisible();
      refreshYoungAccountControls();
      showToast(`拉黑新号日期已设为 ${youngAccountCutoffDate}`, false);
    };
    const youngRowText = document.createElement('span');
    youngRowText.textContent = '少于';
    youngRow.appendChild(youngRowText);
    youngRow.appendChild(youngAccountSelect);
    youngRow.appendChild(youngDateInput);
    const browseBlockBtnRow = document.createElement('div');
    browseBlockBtnRow.style.cssText = 'display:flex;gap:6px;align-items:stretch;';
    const browseBlockBtn = mkToolBtn('', () => {
      closeToolsPanel();
      showExperimentalBrowseBlockPanel();
    });
    browseBlockBtn.style.flex = '1';
    const browseBlockStopBtn = document.createElement('button');
    browseBlockStopBtn.type = 'button';
    browseBlockStopBtn.textContent = '停止';
    browseBlockStopBtn.style.cssText = `background:#fff;color:${C.blockRed};border:1px solid ${C.blockRed};border-radius:7px;font-size:11px;font-weight:800;padding:0 10px;cursor:pointer;white-space:nowrap;`;
    browseBlockStopBtn.onclick = () => {
      if (!experimentalBrowseBlockActive()) return;
      disableExperimentalBrowseBlock('边刷边拉黑已关闭，拉黑队列会继续保留', { hideQueuePanel: false });
      refreshBrowseBlockEntry();
    };
    function refreshBrowseBlockEntry() {
      const active = experimentalBrowseBlockActive();
      browseBlockBtn.textContent = `边刷边拉黑：${active ? '开' : '关'}`;
      browseBlockBtn.style.borderColor = active ? C.blockRed : C.btnBorder;
      browseBlockBtn.style.color = active ? C.blockRed : C.sub;
      browseBlockBtn.style.background = active ? '#fff1f1' : '#fff';
      browseBlockBtn.title = '高误伤危险功能：浏览时把命中当前规则的账号自动加入拉黑排队，开启前需要确认风险。';
      browseBlockStopBtn.style.display = active ? '' : 'none';
      browseBlockStopBtn.disabled = !active;
      browseBlockStopBtn.style.opacity = active ? '1' : '0.45';
      browseBlockStopBtn.style.cursor = active ? 'pointer' : 'default';
      browseBlockStopBtn.title = active ? '立即停止边刷边拉黑，保留现有拉黑队列' : '边刷边拉黑当前未开启';
    }
    const browseBlockNote = document.createElement('div');
    browseBlockNote.textContent = '边刷边拉黑会按当前规则自动加队列，开启前必须确认低误伤。';
    browseBlockNote.style.cssText = `font-size:10px;line-height:1.35;color:${C.blockRed};`;
    youngWrap.appendChild(youngTitle);
    youngWrap.appendChild(youngAccountBtn);
    youngDetailWrap.appendChild(youngModeSelect);
    youngDetailWrap.appendChild(youngRow);
    youngDetailWrap.appendChild(youngNote);
    youngWrap.appendChild(youngDetailWrap);
    browseBlockBtnRow.appendChild(browseBlockBtn);
    browseBlockBtnRow.appendChild(browseBlockStopBtn);
    youngWrap.appendChild(browseBlockBtnRow);
    youngWrap.appendChild(browseBlockNote);
    refreshYoungAccountControls();
    refreshBrowseBlockEntry();

    const editBtn = mkToolBtn('关键词定义', () => {
      closeToolsPanel();
      showPanel(scanPage(), { keywordsOpen: true });
    });
    editBtn.style.borderColor = C.regexKw;
    editBtn.style.color = C.regexKw;
    editBtn.style.background = '#f2fbfc';
    editBtn.title = '打开内容关键词、用户名关键词、正则和只隐藏正则编辑面板；其中只隐藏正则适合高效果但高误伤的降噪规则';
    const statsBtn = mkToolBtn('关键词命中统计', showHideRuleStatsPanel);
    statsBtn.style.borderColor = C.suspect;
    statsBtn.style.color = C.suspect;
    statsBtn.title = '查看每条关键词和正则累计命中并隐藏了多少次回复';
    const ruleTestBtn = mkToolBtn('正则测试', () => {
      closeToolsPanel();
      showRuleTestPanel();
    });
    ruleTestBtn.style.borderColor = C.regexKw;
    ruleTestBtn.style.color = C.regexKw;
    ruleTestBtn.title = '打开正则规则测试面板；可测试后直接加入用户名关键词、内容关键词、scoped 正则或只隐藏正则';
    remoteWrap.style.gridRow = 'span 4';
    youngWrap.style.gridRow = 'span 4';
    p.appendChild(editBtn);
    p.appendChild(statsBtn);
    p.appendChild(ruleTestBtn);
    grid.appendChild(autoReferralBtn);
    grid.appendChild(verifiedProtectBtn);
    grid.appendChild(hideOnlyRulesBtn);
    grid.appendChild(aiReviewWrap);
    grid.appendChild(aiLearningWrap);
    grid.appendChild(remoteWrap);
    grid.appendChild(youngWrap);
    grid.appendChild(mkToolBtn('两类账号说明', showCategoryHelp));
    grid.appendChild(mkToolBtn('导出自定义词', exportKws));
    grid.appendChild(mkToolBtn('合并导入自定义词', () => importKws('merge')));
    grid.appendChild(mkToolBtn('覆盖自定义词', () => importKws('replace')));
    p.appendChild(grid);

    const toolsFtr = document.createElement('div');
    toolsFtr.style.cssText = `padding:2px 2px 0;font-size:9px;color:${C.sub};text-align:center;opacity:0.62;`;
    toolsFtr.appendChild(document.createTextNode(`v${GM_info?.script?.version || ''} · `));
    const toolsGfLink = document.createElement('a');
    toolsGfLink.textContent = 'GreasyFork';
    toolsGfLink.href = GREASYFORK_URL;
    toolsGfLink.target = '_blank';
    toolsGfLink.rel = 'noopener noreferrer';
    toolsGfLink.style.cssText = `color:${C.sub};text-decoration:underline;`;
    toolsFtr.appendChild(toolsGfLink);
    p.appendChild(toolsFtr);

    document.body.appendChild(p);

    setTimeout(() => {
      const onDown = e => {
        if (p.contains(e.target) || e.target?.id === 'xfs-gear-btn') return;
        closeToolsPanel();
        document.removeEventListener('mousedown', onDown, true);
      };
      document.addEventListener('mousedown', onDown, true);
    }, 0);
  }

  function injectGearBtn() {
    if (!document.body) return;
    if (document.getElementById('xfs-gear-btn')) return;
    const btn = mkIconBtn('xfs-gear-btn', GEAR_SVG, '设置 / 关键词定义', 200, C.sub, e => {
      e?.preventDefault?.();
      e?.stopPropagation?.();
      if (document.getElementById('xfs-tools-panel')) closeToolsPanel();
      else showToolsPanel();
    });
    document.body.appendChild(btn);
  }

  function removeGearBtn() {
    document.getElementById('xfs-gear-btn')?.remove();
    closeToolsPanel();
  }
  function injectHomeToolbar() {
    if (!document.body) return;
    if (location.pathname !== '/home') return;
    injectGearBtn();
    const gearBtn = document.getElementById('xfs-gear-btn');
    if (gearBtn) {
      gearBtn.title = `设置 / 关键词定义\n${homeToolbarTipText()}`;
      gearBtn.style.width = '38px';
      gearBtn.style.height = '38px';
      gearBtn.style.right = toolbarRightPx(-3);
      gearBtn.style.bottom = toolbarBottomPx(197);
      gearBtn.style.border = '1px solid rgba(83,100,113,0.12)';
      gearBtn.style.background = 'linear-gradient(180deg, rgba(255,255,255,0.98), rgba(247,249,251,0.94))';
      gearBtn.style.color = C.text;
      gearBtn.style.boxShadow = '0 10px 24px rgba(15,20,25,0.12), inset 0 1px 0 rgba(255,255,255,0.78)';
      gearBtn.style.fontSize = '16px';
      gearBtn.onmouseenter = () => {
        if (gearBtn.disabled) return;
        gearBtn.style.transform = 'translateY(-1px) scale(1.04)';
        gearBtn.style.boxShadow = '0 14px 28px rgba(15,20,25,0.18), inset 0 1px 0 rgba(255,255,255,0.82)';
      };
      gearBtn.onmouseleave = () => {
        gearBtn.style.transform = '';
        gearBtn.style.boxShadow = '0 10px 24px rgba(15,20,25,0.12), inset 0 1px 0 rgba(255,255,255,0.78)';
      };
    }
    updateToolbarPositions();
  }

  // ── Inline block button icons ────────────────────────────────────────
  const IBTN_BLOCK_SVG = '⊘';  // circled slash — block
  const IBTN_CHECK_SVG = '✓';  // checkmark — already blocked

  // ── Inline block buttons ──────────────────────────────────────────────
  // Injects a small block icon next to every tweet's username.
  // Highlighted (red) = matches current filter rules. Dim (gray) = no match but still clickable.
  function injectInlineButtons() {
    document.querySelectorAll('article[data-testid="tweet"]:not([data-xfs-ibtn])').forEach(art => {
      art.dataset.xfsIbtn = '1';
      if (isMainTweetArticle(art)) {
        clearMainTweetXfsState(art);
        art.querySelectorAll('button[data-xfs-handle]').forEach(btn => btn.remove());
        return;
      }

      const nameEl = art.querySelector('[data-testid="User-Name"]');
      if (!nameEl) return;

      const handle = extractHandleFromArticle(art);
      if (!handle) return;

      const displayName = extractDisplayNameFromArticle(art, handle) || handle;

      const textEl = art.querySelector('[data-testid="tweetText"]');
      const cardEl = art.querySelector('[data-testid="card.wrapper"]');
      const bodyLinkText = [
        ...(textEl ? [...textEl.querySelectorAll('a[href]')] : []),
        ...(cardEl  ? [...cardEl.querySelectorAll('a[href]')]  : []),
      ].map(a => a.textContent).join(' ');
      const fullText = [textEl ? getTextWithEmoji(textEl) : null, cardEl ? getTextWithEmoji(cardEl) : null, bodyLinkText].filter(Boolean).join(' ');
      const tweetSnippet = buildUserPreviewSnippet(textEl ? getTextWithEmoji(textEl) : '', cardEl ? getTextWithEmoji(cardEl) : '', bodyLinkText);

      const isProtectedVerified = isProtectedVerifiedArticle(art);
      const allowFilterHighlight = location.pathname !== '/home';
      const matchInfo = allowFilterHighlight && !isProtectedVerified
        ? matchesFilters(displayName, fullText)
        : { matched: false, actionableMatched: false, cats: new Set(), actionableCats: new Set(), heartHits: [], nameKwHits: [], kwHits: [], reHits: [], hideOnlyReHits: [], allHideOnlyReHits: [] };
      const { matched, actionableMatched, actionableCats, heartHits, nameKwHits, kwHits, reHits, hideOnlyReHits, allHideOnlyReHits } = matchInfo;
      if (isProtectedVerified) clearProtectedVerifiedArticleState(art);
      else setArticleHideRuleStats(art, { nameKwHits, kwHits, reHits, hideOnlyReHits });
      const alreadyBlocked = blockedHandles.has(normalizeHandle(handle));
      const isOP = isMainTweetArticle(art);
      art.dataset.xfsHideMatched = (!isOP && matched && !alreadyBlocked) ? '1' : '0';
      if (alreadyBlocked) art.dataset.xfsReferralAccount = '0';
      else if (!isProtectedVerified) scheduleReferralCheck(art, handle, isOP, displayName);
      if (!isOP && actionableMatched && !alreadyBlocked && /\/status\/\d/.test(location.pathname)) {
        matchedHandlesInView.add(handle);
        if (!matchedUsersCache.has(handle))
          matchedUsersCache.set(handle, { handle, displayName, cats: actionableCats, heartHits: [...heartHits], nameKwHits: [...nameKwHits], kwHits: [...kwHits], reHits: [...reHits], hideOnlyReHits: [...hideOnlyReHits], tweetSnippet });
        maybeAutoQueueBrowseMatchedUser({
          handle,
          displayName,
          cats: actionableCats,
          heartHits: [...heartHits],
          nameKwHits: [...nameKwHits],
          kwHits: [...kwHits],
          reHits: [...reHits],
          hideOnlyReHits: [...hideOnlyReHits],
          tweetSnippet,
        }, art);
      }

      if (alreadyBlocked) {
        art.dataset.xfsBlocked = '1';
        for (const a of nameEl.querySelectorAll('a')) {
          const txt = getTextWithEmoji(a).trim();
          if (txt && !txt.startsWith('@')) {
            a.style.setProperty('text-decoration', 'line-through', 'important');
            break;
          }
        }
        clearBlockedArticleStyle(art);
        if (shouldHideBlockedArticles()) applyHideToArticle(art);
        else applyBlockedArticleStyle(art);
      }

      const btn = document.createElement('button');
      btn.dataset.xfsHandle  = handle;
      btn.dataset.xfsState   = alreadyBlocked ? 'blocked' : 'unblocked';
      btn.dataset.xfsMatched = matched ? '1' : '0';
      btn.dataset.xfsHideOnlyMatched = (!actionableMatched && allHideOnlyReHits.length > 0 && !alreadyBlocked) ? '1' : '0';
      if (matched) btn.dataset.xfsMatchTooltip = hitTooltipFromMatchInfo({ heartHits, nameKwHits, kwHits, reHits, hideOnlyReHits });
      if (allHideOnlyReHits.length > 0 && !alreadyBlocked) btn.dataset.xfsHideOnlyTooltip = '命中只隐藏不拉黑规则';
      const referral = isProtectedVerified ? null : referralReason(handle);
      btn.dataset.xfsReferralAccount = referral ? '1' : '0';
      if (referral?.urls?.length) btn.dataset.xfsReferralUrl = referral.urls[0];
      if (referral) btn.dataset.xfsReferralTooltip = `导流号: ${referralItemDescription(referral)}`;
      btn.textContent = alreadyBlocked ? IBTN_CHECK_SVG : IBTN_BLOCK_SVG;

      // Use explicit properties only — 'all:unset' resets display and causes invisible buttons.
      // These inline styles have higher specificity than any site stylesheet.
      Object.assign(btn.style, {
        display:        'inline-flex',
        alignItems:     'center',
        justifyContent: 'center',
        width:          '18px',
        height:         '18px',
        borderRadius:   '50%',
        border:         `1.5px solid ${C.btnBorder}`,
        color:          C.sub,
        background:     alreadyBlocked ? `${C.mute}18` : 'transparent',
        cursor:         'pointer',
        padding:        '0',
        margin:         '0 4px',
        flexShrink:     '0',
        boxSizing:      'border-box',
        verticalAlign:  'middle',
        transition:     'background 0.12s,transform 0.1s',
        opacity:        '1',
        boxShadow:      '',
        lineHeight:     '1',
        fontFamily:     'inherit',
        fontSize:       '11px',
        outline:        'none',
        zIndex:         '10',
        position:       'relative',
      });
      updateInlineBlockButton(btn);

      btn.onmouseenter = () => {
        if (btn.disabled) return;
        const isBlocked = btn.dataset.xfsState === 'blocked';
        const reason = buttonMatchedReason(btn);
        const color = reason === 'referral' ? C.referralHot : (reason === 'hide_only' ? C.hideOnlyHot : C.blockRed);
        btn.style.background = isBlocked ? `${C.suspect}20` : (reason ? `${color}18` : `${C.sub}12`);
        btn.style.transform  = 'scale(1.18)';
      };
      btn.onmouseleave = () => {
        updateInlineBlockButton(btn);
        btn.style.transform  = '';
      };

      btn.onclick = async e => {
        e.preventDefault(); e.stopPropagation();
        if (btn.disabled) return;
        const isBlocked = btn.dataset.xfsState === 'blocked';
        const queueItem = isBlocked ? null : globalBlockQueueItemForHandle(handle);
        if (['queued', 'running'].includes(queueItem?.status)) {
          showToast(`@${handle} 已在拉黑排队中`, false);
          return;
        }
        btn.disabled = true; btn.style.opacity = '0.35';

        if (isBlocked) {
          const csrf = getCsrf();
          if (!csrf) { btn.disabled = false; btn.style.opacity = '1'; showToast('未找到登录凭证（ct0 cookie）', true); return; }
          try {
            await unblockUser(handle, csrf);
            blockedHandles.delete(handle);
            blockedHandles.delete(normalizeHandle(handle));
            undimArticlesByHandle(handle);
            purgeAiMemoryForHandle(handle);
            rememberAiExemptHandle(handle, { source: 'manual_unblock', reason: 'manual unblock' });
            recordAiLearningExample({ handle, displayName, source: 'manual_unblock' }, 'ignore', { reason: 'manual unblock' });
            showToast(`@${handle} 已取消拉黑`, false);
            document.querySelectorAll(`button[data-xfs-handle="${CSS.escape(handle)}"]`).forEach(b => {
              b.dataset.xfsState = 'unblocked';
              b.disabled         = false;
              b.textContent      = IBTN_BLOCK_SVG;
              b.style.opacity    = '1';
              updateInlineBlockButton(b);
            });
          } catch {
            btn.disabled = false; btn.style.opacity = '1';
            showToast(`取消拉黑 @${handle} 失败`, true);
          }
        } else {
          const result = enqueueGlobalBlockUsers([{ handle, displayName, source: 'inline' }], 'inline');
          document.querySelectorAll('button[data-xfs-handle]').forEach(b => {
            if (normalizeHandle(b.dataset.xfsHandle) !== normalizeHandle(handle)) return;
            b.disabled = false;
            b.style.opacity = '1';
            updateInlineBlockButton(b);
          });
          showToast(result.added ? `@${handle} 已加入拉黑排队` : `@${handle} 已在拉黑排队中`, false);
        }
      };

      // Inject just before the caret (three-dots) button — it sits in the same
      // tweet-header flex row as User-Name, whose parent does NOT have overflow:hidden.
      // Fallback: absolute-position inside the article.
      const caretEl = art.querySelector('[data-testid="caret"]');
      if (caretEl) {
        caretEl.insertAdjacentElement('beforebegin', btn);
      } else {
        art.style.position = 'relative';
        Object.assign(btn.style, { position: 'absolute', top: '8px', right: '40px' });
        art.appendChild(btn);
      }
      if (/\/status\/\d/.test(location.pathname)) applyHideToArticle(art);
    });
    if (/\/status\/\d/.test(location.pathname)) updateHideBadge();
  }

  // ── Status page buttons: scan + sweep (reply thread only) ───────────
  function isListPage(path) {
    const p = path || location.pathname;
    return /\/status\/\d+\/(likes|retweets|reposts)$/.test(p) || /\/followers$/.test(p);
  }

  // ── Button group backdrop ────────────────────────────────────────────
  // A pill-shaped panel behind the stacked buttons:
  // content hide, content scan/block, sweep, referral hide, referral scan/block, settings.
  // read as one unified plugin widget rather than separate circles.
  // Dimensions derived from button positions: gear(200), referral scan(240), referral hide(280), sweep(320), scan(360), hide(400).
  function injectBtnBackdrop() {
    if (!document.body) return;
    const experimentActive = experimentalBrowseBlockActive();
    const warningTitle = experimentActive ? toolbarExperimentWarningTitle() : 'X Fraud Scanner 工具栏';

    if (!document.getElementById('xfs-btn-backdrop')) {
      const bd = document.createElement('div');
      bd.id = 'xfs-btn-backdrop';
      bd.style.cssText = [
        'position:fixed', `right:${toolbarRightPx(-4)}`, `bottom:${toolbarBottomPx(196)}`,
        'width:40px', 'height:240px',
        'background:rgba(255,255,255,0.82)',
        'backdrop-filter:blur(6px)', '-webkit-backdrop-filter:blur(6px)',
        `border:1.5px solid ${experimentActive ? C.blockRed : C.btnBorder}`,
        'border-radius:20px',
        `box-shadow:${experimentActive ? `0 0 0 4px ${C.blockRed}12,0 3px 18px rgba(244,33,46,0.14)` : '0 2px 16px rgba(0,0,0,0.12)'}`,
        'pointer-events:auto',
        `cursor:${experimentActive ? 'help' : 'default'}`,
        'z-index:2147483644',
      ].join(';');
      bd.title = warningTitle;
      document.body.appendChild(bd);
    } else {
      const bd = document.getElementById('xfs-btn-backdrop');
      bd.title = warningTitle;
      bd.style.border = `1.5px solid ${experimentActive ? C.blockRed : C.btnBorder}`;
      bd.style.boxShadow = experimentActive
        ? `0 0 0 4px ${C.blockRed}12,0 3px 18px rgba(244,33,46,0.14)`
        : '0 2px 16px rgba(0,0,0,0.12)';
      bd.style.cursor = experimentActive ? 'help' : 'default';
    }

    [
      { id: 'content',  bottom: 316, height: 116, background: 'rgba(244,33,46,0.055)' },
      { id: 'referral', bottom: 236, height: 76,  background: 'rgba(95,111,137,0.075)' },
      { id: 'settings', bottom: 200, height: 32,  background: 'rgba(83,100,113,0.050)' },
    ].forEach((section) => {
      if (document.getElementById(`xfs-btn-section-${section.id}`)) return;
      const el = document.createElement('div');
      el.id = `xfs-btn-section-${section.id}`;
      el.style.cssText = [
        'position:fixed', `right:${toolbarRightPx(-2)}`, `bottom:${toolbarBottomPx(section.bottom)}`,
        'width:36px', `height:${section.height}px`,
        `background:${section.background}`,
        'border-radius:18px',
        'pointer-events:none',
        'z-index:2147483645',
      ].join(';');
      document.body.appendChild(el);
    });

    [302, 226].forEach((bottom, i) => {
      if (document.getElementById(`xfs-btn-sep-${i + 1}`)) return;
      const sep = document.createElement('div');
      sep.id = `xfs-btn-sep-${i + 1}`;
      sep.style.cssText = [
        'position:fixed', `right:${toolbarRightPx(2)}`, `bottom:${toolbarBottomPx(bottom)}`,
        'width:28px', 'height:2px',
        `background:${C.btnBorder}`,
        'opacity:0.9',
        'border-radius:2px',
        'pointer-events:none',
        'z-index:2147483646',
      ].join(';');
      document.body.appendChild(sep);
    });
  }

  function removeBtnBackdrop() {
    document.getElementById('xfs-btn-backdrop')?.remove();
    document.querySelectorAll('[id^="xfs-btn-section-"],[id^="xfs-btn-sep-"]').forEach(el => el.remove());
  }

  function toggleButtonStack() {
    buttonsCollapsed = !buttonsCollapsed;
    GM_setValue('buttons_collapsed', buttonsCollapsed);
    closeToolsPanel();
    if (buttonsCollapsed) {
      removeBtnStack();
    } else {
      injectBtn();
    }
    updateStackToggleBtn();
    updateToolbarPositions();
  }

  function enableToolbarDrag(btn) {
    let drag = null;
    btn.onpointerdown = e => {
      if (e.button !== 0) return;
      clampToolbarPosition();
      drag = {
        x: e.clientX,
        y: e.clientY,
        right: toolbarRight,
        bottom: toolbarBaseBottom,
        moved: false,
      };
      try { btn.setPointerCapture?.(e.pointerId); } catch (_) {}
    };
    btn.onpointermove = e => {
      if (!drag) return;
      const dx = e.clientX - drag.x;
      const dy = e.clientY - drag.y;
      if (Math.abs(dx) + Math.abs(dy) > 4) drag.moved = true;
      if (!drag.moved) return;
      toolbarRight = drag.right - dx;
      toolbarBaseBottom = drag.bottom - dy;
      clampToolbarPosition();
      updateToolbarPositions();
      e.preventDefault();
    };
    const endDrag = e => {
      if (!drag) return;
      const moved = drag.moved;
      drag = null;
      try { btn.releasePointerCapture?.(e.pointerId); } catch (_) {}
      if (moved) {
        btn.dataset.xfsDragged = '1';
        saveToolbarPosition();
        setTimeout(() => {
          if (btn.dataset.xfsDragged === '1') btn.dataset.xfsDragged = '0';
        }, 250);
        e.preventDefault();
      }
    };
    btn.onpointerup = endDrag;
    btn.onpointercancel = endDrag;
  }

  function injectStackToggleBtn() {
    if (!document.body) return;
    let btn = document.getElementById('xfs-stack-toggle-btn');
    if (!btn) {
      btn = mkIconBtn('xfs-stack-toggle-btn', buttonsCollapsed ? EXPAND_SVG : COLLAPSE_SVG, '', 160, C.sub, e => {
        if (btn.dataset.xfsDragged === '1') {
          btn.dataset.xfsDragged = '0';
          e?.preventDefault?.();
          return;
        }
        toggleButtonStack();
      });
      btn.style.touchAction = 'none';
      btn.onmouseenter = () => {
        if (btn.disabled) return;
        btn.style.opacity = '1';
        btn.style.transform = buttonsCollapsed ? 'translateX(-1px)' : 'scale(1.06)';
        btn.style.boxShadow = buttonsCollapsed ? '0 4px 16px rgba(83,100,113,0.24)' : '0 2px 10px rgba(0,0,0,0.14)';
      };
      btn.onmouseleave = () => {
        btn.style.transform = '';
        updateStackToggleBtn();
      };
      enableToolbarDrag(btn);
      document.body.appendChild(btn);
    }
    updateStackToggleBtn();
    updateToolbarPositions();
  }

  function updateStackToggleBtn() {
    const btn = document.getElementById('xfs-stack-toggle-btn');
    if (!btn) return;
    const experimentActive = experimentalBrowseBlockActive();
    const collapsed = buttonsCollapsed;
    btn.textContent = collapsed ? EXPAND_SVG : COLLAPSE_SVG;
    btn.title = collapsed
      ? `X Fraud Scanner · 已收起，点击展开右侧工具栏；拖动可移动${experimentActive ? `\n${toolbarExperimentWarningTitle()}` : ''}`
      : `X Fraud Scanner · 收起右侧工具栏；拖动可移动${experimentActive ? `\n${toolbarExperimentWarningTitle()}` : ''}`;
    btn.style.width = collapsed ? '46px' : '32px';
    btn.style.height = collapsed ? '30px' : '32px';
    btn.style.borderRadius = collapsed ? '15px' : '50%';
    btn.style.opacity = collapsed ? '0.92' : '0.58';
    btn.style.background = collapsed ? 'rgba(255,255,255,0.94)' : 'rgba(255,255,255,0.76)';
    btn.style.border = experimentActive
      ? `1.5px solid ${C.blockRed}`
      : (collapsed ? `1.5px solid ${C.sub}` : `1.5px solid ${C.btnBorder}`);
    btn.style.boxShadow = experimentActive
      ? `0 0 0 3px ${C.blockRed}18, ${collapsed ? '0 3px 12px rgba(244,33,46,0.18)' : '0 1px 8px rgba(244,33,46,0.14)'}`
      : (collapsed ? '0 3px 12px rgba(83,100,113,0.18)' : '0 1px 6px rgba(0,0,0,0.10)');
    btn.style.fontFamily = 'system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif';
    btn.style.fontSize = collapsed ? '11px' : '18px';
    btn.style.fontWeight = collapsed ? '800' : '700';
    btn.style.letterSpacing = '0';
    btn.style.color = experimentActive ? C.blockRed : C.sub;
  }

  function removeStackToggleBtn() {
    document.getElementById('xfs-stack-toggle-btn')?.remove();
  }

  function injectExperimentKillSwitch() {
    removeExperimentKillSwitch();
  }

  function removeExperimentKillSwitch() {
    document.getElementById('xfs-experiment-kill-btn')?.remove();
  }

  function removeBtnStack() {
    document.getElementById('xfs-btn')?.remove();
    document.getElementById('xfs-referral-scan-btn')?.remove();
    document.getElementById('xfs-sweep-btn')?.remove();
    document.getElementById('xfs-queue-btn')?.remove();
    removeGearBtn();
    removeReferralBtn();
    removeHideBtn();
    removeBtnBackdrop();
  }

  function injectBtn() {
    if (!document.body) return;
    if (!/\/status\/\d/.test(location.pathname)) return;
    if (isListPage()) return; // likes/retweets/followers use their own button
    injectStackToggleBtn();
    if (buttonsCollapsed) {
      removeBtnStack();
      injectExperimentKillSwitch();
      return;
    }
    injectHideBtn();
    injectBtnBackdrop();
    injectReferralBtn();
    injectGearBtn();
    injectExperimentKillSwitch();
    if (!document.getElementById('xfs-referral-scan-btn')) {
      document.body.appendChild(mkIconBtn(
        'xfs-referral-scan-btn', SCAN_SVG, '扫描并自动拉黑当前视图导流号；只检查已加载回复，识别会稍有延迟', 240, C.referral, scanReferralAccountsInView));
    }
    if (!document.getElementById('xfs-btn')) {
      document.body.appendChild(mkIconBtn(
        'xfs-btn', BLOCK_SCAN_SVG, '当前视图内容垃圾号自动拉黑', 360, C.blockRed, autoLoadAndScan));
    }
    if (!document.getElementById('xfs-sweep-btn')) {
      document.body.appendChild(mkIconBtn(
        'xfs-sweep-btn', SWEEP_SVG, '整页回复内容垃圾号一网打尽', 320, C.nameKw, () => {
          if (sweepHasRun) {
            // Second+ click: reload page first so already-blocked accounts are gone,
            // then auto-trigger sweep once the page has reloaded.
            sessionStorage.setItem('xfs-auto-sweep', location.pathname);
            location.reload();
          } else {
            sweepHasRun = true;
            sweepAll();
          }
        }));
    }
    if (!document.getElementById('xfs-queue-btn')) {
      document.body.appendChild(mkIconBtn(
        'xfs-queue-btn', QUEUE_SVG, '打开拉黑排队卡片', 320, C.blockRed, () => {
          globalQueuePanelSuppressed = false;
          showGlobalBlockQueueDetailPanel(true);
        }));
    }
    updateToolbarPositions();
    updateScanButtonsLocked();
  }

  function removeBtn() {
    removeBtnStack();
    removeStackToggleBtn();
    removeExperimentKillSwitch();
  }

  // ── Likes / retweets / followers page button ─────────────────────────
  function injectListBtn() {
    if (!document.body) return;
    if (document.getElementById('xfs-list-btn')) return;
    if (!isListPage()) return;
    const path = location.pathname;
    const label = /\/likes$/.test(path)             ? '批量拉黑点赞者'
                : /\/(retweets|reposts)$/.test(path) ? '批量拉黑转发者'
                : '批量拉黑关注者';
    document.body.appendChild(
      mkIconBtn('xfs-list-btn', LIST_SVG, label, 200, C.mute, sweepUserList));
    updateScanButtonsLocked();
  }

  function removeListBtn() {
    document.getElementById('xfs-list-btn')?.remove();
  }

  // ── Referral-account hide toggle button ──────────────────────────────
  // Defaults on. Hides replies from accounts that match profile referral rules.
  function updateReferralBtn() {
    const btn = document.getElementById('xfs-referral-btn');
    if (!btn) return;
    const badge = document.getElementById('xfs-referral-badge');
    btn.textContent = EYE_SVG;
    if (badge) btn.appendChild(badge);
    btn.title = hideReferralActive
      ? '导流号回复已隐藏（橙标），点击显示。受平台接口/限速影响，识别会稍有延迟'
      : '点击隐藏导流号回复（橙标）。只检查已加载回复，识别会稍有延迟';
    btn.style.background = hideReferralActive ? 'rgba(95,111,137,0.14)' : 'rgba(255,255,255,0.92)';
    btn.style.border = hideReferralActive ? `2px solid ${C.referral}` : `2px dashed ${C.btnBorder}`;
    btn.style.color = hideReferralActive ? C.referral : C.sub;
    btn.style.opacity = hideReferralActive ? '1' : '0.55';
    btn.style.boxShadow = hideReferralActive ? `0 0 0 2px ${C.referral}22,0 2px 8px rgba(0,0,0,0.16)` : '0 2px 8px rgba(0,0,0,0.12)';
    updateReferralBadge();
  }

  function injectReferralBtn() {
    if (!document.body) return;
    if (document.getElementById('xfs-referral-btn')) return;
    if (!/\/status\/\d/.test(location.pathname)) return;
    if (isListPage()) return;

    const btn = mkIconBtn('xfs-referral-btn', EYE_SVG, '', 280, C.referral, null);

    const badge = document.createElement('span');
    badge.id = 'xfs-referral-badge';
    badge.style.cssText = [
      'position:absolute', 'top:-5px', 'right:-5px',
      'min-width:16px', 'height:16px',
      `background:${C.referral}`, 'color:#fff',
      'border-radius:8px', 'font-size:9px', 'font-weight:700',
      'display:none', 'align-items:center', 'justify-content:center',
      'padding:0 3px', 'box-sizing:border-box',
      'pointer-events:none', 'line-height:1',
    ].join(';');
    btn.appendChild(badge);

    btn.onclick = () => {
      hideReferralActive = !hideReferralActive;
      GM_setValue('hide_referral_accounts', hideReferralActive);
      btn.textContent = EYE_SVG;
      btn.appendChild(badge);
      updateReferralBtn();
      if (hideReferralActive) applyReferralForVisible();
      applyHideAll();
      showToast(hideReferralActive ? '导流号隐藏已开启' : '导流号隐藏已关闭', false);
    };

    document.body.appendChild(btn);
    updateReferralBtn();
    if (hideReferralActive) applyReferralForVisible();
  }

  function removeReferralBtn() {
    document.getElementById('xfs-referral-btn')?.remove();
  }

  // ── Hide-matched toggle button ───────────────────────────────────────
  // Top button in the content-spam group. Collapses matched articles to a 1px gray
  // separator line. State persists across SPA navigations via GM storage.
  function updateMatchedHideBtn() {
    const btn = document.getElementById('xfs-hide-btn');
    if (!btn) return;
    const badge = document.getElementById('xfs-hide-badge');
    btn.textContent = EYE_SVG;
    if (badge) btn.appendChild(badge);
    btn.title = hideMatchedActive
      ? '内容垃圾号回复已隐藏（红标），点击显示'
      : '点击隐藏匹配关键词/正则的内容垃圾号回复（红标）';
    btn.style.background = hideMatchedActive ? 'rgba(244,33,46,0.10)' : 'rgba(255,255,255,0.92)';
    btn.style.border = hideMatchedActive ? `2px solid ${C.blockRed}` : `2px dashed ${C.btnBorder}`;
    btn.style.color = hideMatchedActive ? C.blockRed : C.sub;
    btn.style.opacity = hideMatchedActive ? '1' : '0.55';
    btn.style.boxShadow = hideMatchedActive ? `0 0 0 2px ${C.blockRed}22,0 2px 8px rgba(0,0,0,0.16)` : '0 2px 8px rgba(0,0,0,0.12)';
    updateHideBadge();
  }

  function injectHideBtn() {
    if (!document.body) return;
    if (document.getElementById('xfs-hide-btn')) return;
    if (!/\/status\/\d/.test(location.pathname)) return;
    if (isListPage()) return;

    const btn = mkIconBtn(
      'xfs-hide-btn',
      EYE_SVG,
      hideMatchedActive ? '内容垃圾号回复已隐藏，点击显示' : '点击隐藏匹配关键词/正则的内容垃圾号回复',
      400, C.sub, null
    );

    // Badge: shows count of matched handles accumulated this scroll session
    const badge = document.createElement('span');
    badge.id = 'xfs-hide-badge';
    badge.style.cssText = [
      'position:absolute', 'top:-5px', 'right:-5px',
      'min-width:16px', 'height:16px',
      `background:${C.blockRed}`, 'color:#fff',
      'border-radius:8px', 'font-size:9px', 'font-weight:700',
      'display:none', 'align-items:center', 'justify-content:center',
      'padding:0 3px', 'box-sizing:border-box',
      'pointer-events:none', 'line-height:1',
    ].join(';');
    btn.appendChild(badge);

    btn.onclick = () => {
      hideMatchedActive = !hideMatchedActive;
      GM_setValue('hide_matched', hideMatchedActive);
      updateMatchedHideBtn();
      applyHideAll();
    };

    document.body.appendChild(btn);
    updateMatchedHideBtn();
    applyHideAll();
  }

  function removeHideBtn() {
    document.getElementById('xfs-hide-btn')?.remove();
  }

  function ensureRouteButtons() {
    if (!document.body) return;
    const p = location.pathname;
    if      (isListPage(p))          injectListBtn();
    else if (/\/status\/\d/.test(p)) injectBtn();
    else if (p === '/home')          injectHomeToolbar();
  }

  function routeButtonsReady() {
    const p = location.pathname;
    const ids = isListPage(p) ? ['xfs-list-btn']
              : /\/status\/\d/.test(p) ? (buttonsCollapsed
                ? ['xfs-stack-toggle-btn']
                : ['xfs-stack-toggle-btn', 'xfs-btn-backdrop', 'xfs-hide-btn', 'xfs-referral-btn', 'xfs-btn', 'xfs-referral-scan-btn', 'xfs-sweep-btn', 'xfs-gear-btn'])
              : p === '/home' ? ['xfs-gear-btn'] : [];
    return ids.every(id => document.getElementById(id));
  }

  // ── SPA route watcher (deferred until DOM is ready) ─────────────────
  let uiStarted = false;
  function startUI() {
    if (uiStarted) return;
    if (!document.body) {
      setTimeout(startUI, 50);
      return;
    }
    uiStarted = true;

    let lastPath = location.pathname;
    let ibtnTimer = null;
    let profileTimer = null;
    let routeBtnTimer = null;
    let watchdogTimer = null;

    function startButtonWatchdog(duration = 30000, interval = 500) {
      clearTimeout(watchdogTimer);
      const until = Date.now() + duration;
      const tick = () => {
        ensureRouteButtons();
        if (Date.now() < until && !routeButtonsReady()) {
          watchdogTimer = setTimeout(tick, interval);
        }
      };
      tick();
    }

    // If this page was reloaded by the sweep button to flush blocked accounts,
    // auto-trigger sweep once the page is ready.
    const autoSweepPath = sessionStorage.getItem('xfs-auto-sweep');
    if (autoSweepPath && autoSweepPath === location.pathname) {
      sessionStorage.removeItem('xfs-auto-sweep');
      waitForTweetContent().then(() => { sweepHasRun = true; sweepAll(); });
    }

    // ── Navigation handler — called directly by pushState/replaceState/popstate ──
    // Fires synchronously with the URL change, so no DOM-timing race.
    function handleNav() {
      const cur = location.pathname;
      if (cur === lastPath) return;
      lastPath = cur;
      sweepHasRun = false;
      endScanMode(activeScanMode, true);
      matchedHandlesInView.clear();
      matchedUsersCache.clear();
      referralIntentHints.clear();
      referralHintRefreshDone.clear();
      removeBtn();
      removeListBtn();
      const currentPanel = document.getElementById('xfs-panel');
      if (!(currentPanel?.dataset.xfsGlobalQueueView === '1')) currentPanel?.remove();
      setTimeout(captureReferralAccountsFromProfileDom, 300);
      setTimeout(ensureRouteButtons, 300);
      startButtonWatchdog(12000, 500);
      injectExperimentKillSwitch();
    }
    _navCallbacks.push(handleNav);

    // ── MutationObserver — inline buttons + fallback for nav events ──
    // No longer responsible for URL-change detection (handled by handleNav above).
    // The fallback injectBtn() calls are cheap due to the early-return guard inside.
    const observer = new MutationObserver(() => {
      clearTimeout(ibtnTimer);
      ibtnTimer = setTimeout(injectInlineButtons, 300);
      clearTimeout(profileTimer);
      profileTimer = setTimeout(captureReferralAccountsFromProfileDom, 250);

      // Fallback: re-inject main buttons if DOM settled before the nav timer fired.
      clearTimeout(routeBtnTimer);
      routeBtnTimer = setTimeout(ensureRouteButtons, 300);
    });
    observer.observe(document.body, { childList: true, subtree: true });
    // Initial inject on page load
    startExperimentalBrowseBlockHeartbeat();
    startGlobalBlockQueueMonitor();
    injectExperimentKillSwitch();
    setTimeout(captureReferralAccountsFromProfileDom, 900);
    setTimeout(injectInlineButtons, 1200);
    setTimeout(ensureRouteButtons, 1200);

    // Startup watchdog: X.com can leave the DOM quiet before React has rendered
    // the target route. Re-check for a short window and repair any partial group.
    startButtonWatchdog(30000, 500);

    // Re-check when the user switches back to a backgrounded tab.
    document.addEventListener('visibilitychange', () => {
      if (document.hidden) return;
      ensureRouteButtons();
      injectExperimentKillSwitch();
      startButtonWatchdog(5000, 500);
    });
  }

  exposeDebugTools();
  scheduleRemoteRulesRefresh();
  startUI();
  document.addEventListener('DOMContentLoaded', startUI);
  window.addEventListener('load', startUI);

})();
