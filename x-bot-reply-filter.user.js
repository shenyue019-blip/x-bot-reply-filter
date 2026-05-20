// ==UserScript==
// @name         X Bot Reply Filter
// @namespace    local.x.bot.reply.filter
// @version      0.2.4
// @description  Hide likely bot/spam replies on X with conservative local scoring and local block/mute logs.
// @match        https://x.com/*
// @match        https://twitter.com/*
// @downloadURL  https://raw.githubusercontent.com/shenyue019-blip/x-bot-reply-filter/main/x-bot-reply-filter.user.js
// @updateURL    https://raw.githubusercontent.com/shenyue019-blip/x-bot-reply-filter/main/x-bot-reply-filter.user.js
// @run-at       document-idle
// @grant        none
// ==/UserScript==

(function () {
  "use strict";

  const LOG_KEY = "x_bot_reply_filter_logs_v1";
  const QUEUE_KEY = "x_bot_reply_filter_queue_v1";
  const RULES_KEY = "x_bot_reply_filter_rules_v1";
  const STATS_KEY = "x_bot_reply_filter_stats_v1";
  const TIME_SETTINGS_KEY = "x_bot_reply_filter_time_settings_v1";
  const UI_POS_KEY = "x_bot_reply_filter_ui_pos_v1";
  const UI_COLLAPSED_KEY = "x_bot_reply_filter_ui_collapsed_v1";
  const WHITELIST_KEY = "x_bot_reply_filter_whitelist_v1";
  const HIDDEN_ATTR = "data-x-bot-reply-filter-hidden";
  const TWEET_SELECTOR = 'article[data-testid="tweet"]';

  const config = {
    enabled: true,
    threshold: 8,
    skipVerified: true,
    queueFiltered: true,
    logFilteredReplies: true,
    maxLogs: 400,
    maxQueue: 300,
    hideQuoteTweets: false,
    scanDelayMs: 350,
    revealMs: 10000,
  };

  const state = {
    hiddenCount: 0,
    revealUntil: 0,
    timer: null,
    panel: null,
    logPanel: null,
    queuePanel: null,
    rulesPanel: null,
    toolbarCollapsed: false,
    lastMenuArticle: null,
    lastMenuArticleAt: 0,
    loggedKeys: new Set(),
    autoBlockRunning: false,
    autoBlockTimer: null,
    autoBlockProcessed: 0,
    autoBlockStartedAt: 0,
  };

  const defaultCustomRules = {
    schemaVersion: 1,
    contentKeywords: ["主页领取", "进群", "看主页", "私信我", "加我", "稳赚", "带单", "裸聊", "约炮"],
    nameKeywords: ["福利", "带单", "稳赚", "同城", "裸聊", "外围"],
    regexKeywords: [
      "content:/^[\\\\p{Extended_Pictographic}\\\\s\\\\p{P}]{8,}$/u",
      "name:/^[a-z]{4,10}\\\\d{5,}$/i",
    ],
  };

  const defaultTimeSettings = {
    baseIntervalSec: 15,
    pauseEvery20Sec: 30,
    pauseEvery60Min: 5,
    maxRunMinutes: 120,
  };

  const genericReplies = new Set([
    "amazing",
    "awesome",
    "based",
    "bullish",
    "cool",
    "done",
    "gm",
    "gn",
    "great",
    "great post",
    "interesting",
    "lfg",
    "nice",
    "sir",
    "support",
    "this is huge",
    "very nice",
    "wagmi",
    "wow",
  ]);

  const highRiskPatterns = [
    /\b(airdrop|claim|giveaway|whitelist|presale|free mint|mint now|connect wallet)\b/i,
    /\b(seed phrase|private key|wallet verification|sync wallet|validate wallet)\b/i,
    /\b(profit|passive income|earn money|make money|daily income|guaranteed return)\b/i,
    /\b(dm me|inbox me|message me|check my profile|link in bio)\b/i,
    /\b(telegram|whatsapp|discord\.gg|t\.me\/|bit\.ly|tinyurl|linktr\.ee)\b/i,
    /\b(onlyfans|camgirl|escort|adult dating)\b/i,
    /空投|领空投|白名单|预售|免费铸造|连接钱包|助记词|私钥/i,
    /带单|跟单|喊单|稳赚|保本|日赚|套利|量化收益|资金盘|合约体验/i,
    /私信|私我|加我|进群|福利群|看主页|主页有|主页领取|联系我/i,
    /裸聊|约炮|上门|同城交友|外围|全套|包夜|调教|白给/i,
  ];

  const mediumRiskPatterns = [
    /\b(crypto|token|coin|solana|ethereum|bitcoin|web3|nft|memecoin)\b/i,
    /\b(signal|signals|trading group|investment group)\b/i,
    /互关|互粉|互赞|求关注|涨粉|刷粉|引流/i,
    /USDT|虚拟币|币圈|链上|交易所|上币|拉盘|打新项目/i,
  ];

  const safeTradeContext = /闲鱼|咸鱼|二手|实物|淘宝|京东|支付宝|拼多多|股票|基金|美股|A股|期货|石油|原油|黄金|白银|贵金属|期权|外汇|券商|银行|跨行|提现|退票|记录|明细|日常|合法|正当|公平|手续费/i;

  const botHandlePatterns = [
    /^[a-z]{4,10}\d{5,}$/i,
    /^[a-z]+_[a-z]+\d{4,}$/i,
    /^[A-Z][a-z]+[A-Z][a-z]+\d{4,}$/,
  ];

  const riskyNamePatterns = [
    /约炮|外围|全套|包夜|私约|裸聊|调教|福利|白给|同城/i,
    /空投|带单|跟单|稳赚|返利|量化|合约|币圈|打新/i,
  ];

  const invisibleRe = /[\u200B-\u200F\u2028-\u202F\u2060-\u206F\uFEFF\u00AD\u034F\u061C\u180E]/g;

  function deconfuse(text) {
    return String(text || "")
      .replace(invisibleRe, "")
      .replace(/[Ａ-Ｚａ-ｚ０-９]/g, (char) =>
        String.fromCharCode(char.charCodeAt(0) - 0xfee0)
      );
  }

  function normalizeText(text) {
    return deconfuse(text)
      .normalize("NFD")
      .replace(/[\u0300-\u036f]/g, "")
      .replace(/https?:\/\/\S+/gi, "")
      .replace(/\bpic\.twitter\.com\/\S+/gi, "")
      .replace(/\s+/g, " ")
      .trim()
      .toLowerCase();
  }

  function compactText(text) {
    return normalizeText(text).replace(/[^\p{L}\p{N}]/gu, "");
  }

  function extractTextWithEmoji(node) {
    if (!node) return "";
    let text = "";
    for (const child of node.childNodes) {
      if (child.nodeType === Node.TEXT_NODE) {
        text += child.nodeValue || "";
      } else if (child.nodeType === Node.ELEMENT_NODE) {
        if (child.tagName === "IMG" && child.alt) {
          text += child.alt;
        } else {
          text += extractTextWithEmoji(child);
        }
      }
    }
    return text;
  }

  function getArticleText(article) {
    const textBlocks = [...article.querySelectorAll('[data-testid="tweetText"]')];
    if (textBlocks.length === 0) return "";
    return textBlocks.map(extractTextWithEmoji).join("\n").trim();
  }

  function getAuthorName(article) {
    const node = article.querySelector('[data-testid="User-Name"]');
    if (!node) return "";
    return (node.textContent || "").split("@")[0].trim();
  }

  function getAuthorHandle(article) {
    const links = article.querySelectorAll('[data-testid="User-Name"] a[href]');
    for (const link of links) {
      const href = link.getAttribute("href") || "";
      const match = href.match(/^\/([A-Za-z0-9_]{1,15})(?:\/)?$/);
      if (match) return match[1].toLowerCase();
    }
    return "";
  }

  function getTweetUrl(article) {
    const links = article.querySelectorAll('a[href*="/status/"]');
    for (const link of links) {
      const href = link.getAttribute("href") || "";
      if (/\/status\/\d+/.test(href)) {
        return new URL(href, location.origin).href;
      }
    }
    return location.href;
  }

  function loadJson(key, fallback) {
    try {
      const value = JSON.parse(localStorage.getItem(key) || "null");
      return value == null ? fallback : value;
    } catch {
      return fallback;
    }
  }

  function saveJson(key, value) {
    localStorage.setItem(key, JSON.stringify(value));
  }

  function loadUiPosition() {
    const pos = loadJson(UI_POS_KEY, {});
    return {
      right: validPositiveNumber(pos.right, 18),
      bottom: validPositiveNumber(pos.bottom, 160),
    };
  }

  function saveUiPosition(pos) {
    saveJson(UI_POS_KEY, {
      right: validPositiveNumber(pos.right, 18),
      bottom: validPositiveNumber(pos.bottom, 160),
    });
  }

  function validPositiveNumber(value, fallback) {
    const number = Number(value);
    if (!Number.isFinite(number)) return fallback;
    if (number <= 0) return fallback;
    return number;
  }

  function loadTimeSettings() {
    const saved = loadJson(TIME_SETTINGS_KEY, {});
    return {
      baseIntervalSec: validPositiveNumber(saved.baseIntervalSec, defaultTimeSettings.baseIntervalSec),
      pauseEvery20Sec: validPositiveNumber(saved.pauseEvery20Sec, defaultTimeSettings.pauseEvery20Sec),
      pauseEvery60Min: validPositiveNumber(saved.pauseEvery60Min, defaultTimeSettings.pauseEvery60Min),
      maxRunMinutes: validPositiveNumber(saved.maxRunMinutes, defaultTimeSettings.maxRunMinutes),
    };
  }

  function saveTimeSettings(settings) {
    saveJson(TIME_SETTINGS_KEY, {
      baseIntervalSec: validPositiveNumber(settings.baseIntervalSec, defaultTimeSettings.baseIntervalSec),
      pauseEvery20Sec: validPositiveNumber(settings.pauseEvery20Sec, defaultTimeSettings.pauseEvery20Sec),
      pauseEvery60Min: validPositiveNumber(settings.pauseEvery60Min, defaultTimeSettings.pauseEvery60Min),
      maxRunMinutes: validPositiveNumber(settings.maxRunMinutes, defaultTimeSettings.maxRunMinutes),
    });
  }

  function getQueueDelayMs(processedCount) {
    const settings = loadTimeSettings();
    if (processedCount > 0 && processedCount % 60 === 0) {
      return settings.pauseEvery60Min * 60 * 1000;
    }
    if (processedCount > 0 && processedCount % 20 === 0) {
      return settings.pauseEvery20Sec * 1000;
    }
    return settings.baseIntervalSec * 1000;
  }

  function getCookie(name) {
    const escaped = name.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    const match = document.cookie.match(new RegExp(`(?:^|; )${escaped}=([^;]*)`));
    return match ? decodeURIComponent(match[1]) : "";
  }

  function loadRules() {
    const saved = loadJson(RULES_KEY, {});
    return {
      schemaVersion: 1,
      contentKeywords: Array.isArray(saved.contentKeywords) ? saved.contentKeywords : defaultCustomRules.contentKeywords,
      nameKeywords: Array.isArray(saved.nameKeywords) ? saved.nameKeywords : defaultCustomRules.nameKeywords,
      regexKeywords: Array.isArray(saved.regexKeywords) ? saved.regexKeywords : defaultCustomRules.regexKeywords,
    };
  }

  function saveRules(rules) {
    saveJson(RULES_KEY, {
      schemaVersion: 1,
      contentKeywords: normalizeRuleList(rules.contentKeywords),
      nameKeywords: normalizeRuleList(rules.nameKeywords),
      regexKeywords: normalizeRuleList(rules.regexKeywords),
    });
  }

  function normalizeRuleList(value) {
    return Array.isArray(value)
      ? value.map((item) => String(item || "").trim()).filter(Boolean)
      : [];
  }

  function escapeRegExp(text) {
    return String(text).replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  }

  function parseRegexRule(ruleText) {
    let scope = "both";
    let source = String(ruleText || "").trim();
    if (/^content:/i.test(source)) {
      scope = "content";
      source = source.replace(/^content:/i, "").trim();
    } else if (/^name:/i.test(source)) {
      scope = "name";
      source = source.replace(/^name:/i, "").trim();
    }

    const slash = source.match(/^\/(.+)\/([a-z]*)$/i);
    try {
      return {
        scope,
        label: ruleText,
        regex: slash ? new RegExp(slash[1], slash[2]) : new RegExp(source, "i"),
      };
    } catch {
      return null;
    }
  }

  function addRuleHit(ruleKey) {
    const stats = loadJson(STATS_KEY, {});
    stats[ruleKey] = (Number(stats[ruleKey]) || 0) + 1;
    saveJson(STATS_KEY, stats);
  }

  function normalizeHandle(value) {
    const handle = String(value || "").trim().toLowerCase().replace(/^@+/, "");
    return /^[a-z0-9_]{1,15}$/.test(handle) ? handle : "";
  }

  function isWhitelisted(handle) {
    const normalized = normalizeHandle(handle);
    if (!normalized) return false;
    const whitelist = loadJson(WHITELIST_KEY, []);
    return whitelist.some((item) => normalizeHandle(item) === normalized);
  }

  function addWhitelistHandle(handle) {
    const normalized = normalizeHandle(handle);
    if (!normalized) return false;
    const whitelist = loadJson(WHITELIST_KEY, []);
    if (!whitelist.some((item) => normalizeHandle(item) === normalized)) {
      whitelist.push(`@${normalized}`);
      saveJson(WHITELIST_KEY, whitelist);
    }
    return true;
  }

  function countMatches(text, regex) {
    return (text.match(regex) || []).length;
  }

  function countPatternHits(patterns, rawText, normalized, compact) {
    let hits = 0;
    const names = [];
    for (const pattern of patterns) {
      if (pattern.test(rawText) || pattern.test(normalized) || pattern.test(compact)) {
        hits += 1;
        names.push(pattern.source.slice(0, 36));
      }
    }
    return { hits, names };
  }

  function isPromoted(article) {
    return /\bpromoted\b|推广/i.test(article.innerText || "");
  }

  function isVerified(article) {
    const userName = article.querySelector('[data-testid="User-Name"]');
    if (!userName) return false;
    const text = userName.innerText || userName.textContent || "";
    return (
      userName.querySelector('[data-testid="icon-verified"]') !== null ||
      userName.querySelector('svg[aria-label*="Verified"], svg[aria-label*="认证"], svg[aria-label*="已验证"]') !== null ||
      /Verified account|已认证|已验证/.test(text)
    );
  }

  function isQuoteTweet(article) {
    return article.querySelector('[role="link"][href*="/status/"] article') !== null;
  }

  function pushReason(reasons, reason, points) {
    reasons.push(`${reason}+${points}`);
  }

  function scoreArticle(article, duplicateCount) {
    const rawText = getArticleText(article);
    const normalized = normalizeText(rawText);
    const compact = compactText(rawText);
    const name = getAuthorName(article);
    const handle = getAuthorHandle(article);
    const reasons = [];
    const ruleHits = [];
    let score = 0;

    if (!rawText.trim() || isWhitelisted(handle) || (config.skipVerified && isVerified(article))) {
      return { score: 0, reasons, ruleHits, rawText, normalized, name, handle };
    }

    const customRules = loadRules();
    const contentText = `${rawText}\n${normalized}\n${compact}`;
    const nameText = `${name}\n${normalizeText(name)}\n${compactText(name)}`;

    for (const keyword of normalizeRuleList(customRules.contentKeywords)) {
      const re = new RegExp(escapeRegExp(keyword), "i");
      if (re.test(contentText)) {
        score += 4;
        ruleHits.push(`content:${keyword}`);
        pushReason(reasons, "custom content keyword", 4);
      }
    }

    for (const keyword of normalizeRuleList(customRules.nameKeywords)) {
      const re = new RegExp(escapeRegExp(keyword), "i");
      if (re.test(nameText)) {
        score += 4;
        ruleHits.push(`name:${keyword}`);
        pushReason(reasons, "custom name keyword", 4);
      }
    }

    for (const rawRule of normalizeRuleList(customRules.regexKeywords)) {
      const parsed = parseRegexRule(rawRule);
      if (!parsed) continue;
      const hitContent = parsed.scope !== "name" && parsed.regex.test(contentText);
      parsed.regex.lastIndex = 0;
      const hitName = parsed.scope !== "content" && parsed.regex.test(nameText);
      parsed.regex.lastIndex = 0;
      if (hitContent || hitName) {
        score += 5;
        ruleHits.push(`regex:${rawRule}`);
        pushReason(reasons, "custom regex", 5);
      }
    }

    const highRisk = countPatternHits(highRiskPatterns, rawText, normalized, compact);
    if (highRisk.hits > 0) {
      const points = Math.min(7, highRisk.hits * 3);
      score += points;
      pushReason(reasons, "high risk keyword", points);
    }

    const mediumRisk = countPatternHits(mediumRiskPatterns, rawText, normalized, compact);
    if (mediumRisk.hits > 0) {
      const points = Math.min(4, mediumRisk.hits * 2);
      score += points;
      pushReason(reasons, "medium risk keyword", points);
    }

    const urlCount = countMatches(rawText, /(https?:\/\/|t\.co\/|bit\.ly\/|tinyurl\.com\/|t\.me\/|discord\.gg\/)/gi);
    if (urlCount >= 2) {
      score += 4;
      pushReason(reasons, "multiple links", 4);
    } else if (urlCount === 1 && highRisk.hits + mediumRisk.hits > 0) {
      score += 2;
      pushReason(reasons, "link with promo context", 2);
    }

    const mentionCount = countMatches(rawText, /(^|\s)@\w{2,}/g);
    if (mentionCount >= 4) {
      score += 3;
      pushReason(reasons, "many mentions", 3);
    }

    const hashOrCashCount = countMatches(rawText, /(^|\s)[#$][\p{L}\p{N}_]{2,}/gu);
    if (hashOrCashCount >= 5) {
      score += 3;
      pushReason(reasons, "many tags", 3);
    } else if (hashOrCashCount >= 3 && mediumRisk.hits > 0) {
      score += 2;
      pushReason(reasons, "tags with risk context", 2);
    }

    if (genericReplies.has(normalized)) {
      score += 2;
      pushReason(reasons, "generic reply", 2);
    }

    if (normalized.length <= 18 && /^(gm|gn|nice|great|wow|done|sir|lfg|wagmi|based|cool)\b/i.test(normalized)) {
      score += 1;
      pushReason(reasons, "low signal", 1);
    }

    if (duplicateCount >= 3 && normalized.length >= 12) {
      const points = duplicateCount >= 5 ? 4 : 3;
      score += points;
      pushReason(reasons, "duplicate text", points);
    }

    if (/^\s*[a-zA-Z0-9]{1,2}\s*$/.test(rawText) && botHandlePatterns.some((pattern) => pattern.test(handle))) {
      score += 4;
      pushReason(reasons, "short noise from bot-like handle", 4);
    }

    const emojiMatches = [...rawText.matchAll(/[\p{Extended_Pictographic}]/gu)].map((match) => match[0]);
    const withoutEmojiAndPunctuation = rawText.replace(/[\p{Extended_Pictographic}\s\p{P}]/gu, "");
    if (emojiMatches.length >= 8 && !withoutEmojiAndPunctuation) {
      score += 5;
      pushReason(reasons, "emoji flood", 5);
    } else if (emojiMatches.length >= 5 && new Set(emojiMatches).size >= 3 && !withoutEmojiAndPunctuation) {
      score += 4;
      pushReason(reasons, "random emoji only", 4);
    } else if (emojiMatches.length >= 1 && !withoutEmojiAndPunctuation && botHandlePatterns.some((pattern) => pattern.test(handle))) {
      score += 4;
      pushReason(reasons, "emoji only from bot-like handle", 4);
    }

    const poetryMatches = rawText.match(/人间|岁月|时光|流年|红尘|沧桑|温柔|世事|风雨|花开|花落|明月|春风|秋雨|相思|天涯|离别|心安|过客|繁华|清欢|余生|半生|随心|自在/g);
    if (poetryMatches && poetryMatches.length >= 4 && botHandlePatterns.some((pattern) => pattern.test(handle))) {
      score += 4;
      pushReason(reasons, "poetry bot pattern", 4);
    }

    if (botHandlePatterns.some((pattern) => pattern.test(handle))) {
      score += 2;
      pushReason(reasons, "bot-like handle", 2);
    }

    const riskyName = riskyNamePatterns.some((pattern) => pattern.test(name));
    if (riskyName) {
      score += 3;
      pushReason(reasons, "risky display name", 3);
    }

    if (/(交易|理财|开户|合约|收益)/.test(rawText) && !safeTradeContext.test(rawText)) {
      score += 2;
      pushReason(reasons, "finance context without safe context", 2);
    }

    if (isPromoted(article)) {
      score += 3;
      pushReason(reasons, "promoted", 3);
    }

    if (!config.hideQuoteTweets && isQuoteTweet(article)) {
      score = Math.max(0, score - 2);
      reasons.push("quote tweet -2");
    }

    return { score, reasons: [...new Set(reasons)], ruleHits: [...new Set(ruleHits)], rawText, normalized, name, handle };
  }

  function loadLogs() {
    const logs = loadJson(LOG_KEY, []);
    return Array.isArray(logs) ? logs : [];
  }

  function saveLogs(logs) {
    saveJson(LOG_KEY, logs.slice(0, config.maxLogs));
  }

  function makeLogKey(entry) {
    return [entry.action, entry.handle, entry.url, entry.text].join("|").slice(0, 500);
  }

  function logEntry(entry) {
    const complete = {
      time: new Date().toISOString(),
      page: location.href,
      ...entry,
    };
    const key = makeLogKey(complete);
    if (state.loggedKeys.has(key)) return;
    state.loggedKeys.add(key);

    const logs = loadLogs();
    logs.unshift(complete);
    saveLogs(logs);
    renderLogPanel();
  }

  function articleToLog(article, action, reason) {
    if (!article) return null;
    const text = getArticleText(article).trim();
    const handle = getAuthorHandle(article);
    const name = getAuthorName(article);
    if (!text && !handle && !name) return null;
    return {
      action,
      handle: handle ? `@${handle}` : "",
      name,
      text,
      reason,
      url: getTweetUrl(article),
    };
  }

  function loadQueue() {
    const queue = loadJson(QUEUE_KEY, []);
    return Array.isArray(queue) ? queue : [];
  }

  function saveQueue(queue) {
    saveJson(QUEUE_KEY, queue.slice(0, config.maxQueue));
  }

  function queueEntry(entry) {
    if (!config.queueFiltered || !entry.handle) return;
    const queue = loadQueue();
    const key = normalizeHandle(entry.handle);
    if (!key || queue.some((item) => normalizeHandle(item.handle) === key)) return;
    queue.unshift({
      ...entry,
      queuedAt: new Date().toISOString(),
      status: "pending",
    });
    saveQueue(queue);
    renderQueuePanel();
  }

  function updateQueue(handle, patch) {
    const normalized = normalizeHandle(handle);
    const queue = loadQueue().map((item) =>
      normalizeHandle(item.handle) === normalized ? { ...item, ...patch } : item
    );
    saveQueue(queue);
    renderQueuePanel();
  }

  function removeFromQueue(handle) {
    const normalized = normalizeHandle(handle);
    saveQueue(loadQueue().filter((item) => normalizeHandle(item.handle) !== normalized));
    renderQueuePanel();
  }

  async function blockHandle(handle) {
    const normalized = normalizeHandle(handle);
    if (!normalized) throw new Error("invalid handle");

    const csrf = getCookie("ct0");
    if (!csrf) throw new Error("missing csrf token; refresh X and sign in again");

    const body = new URLSearchParams({
      screen_name: normalized,
      skip_status: "true",
    });

    const response = await fetch("/i/api/1.1/blocks/create.json", {
      method: "POST",
      credentials: "include",
      headers: {
        authorization:
          "Bearer AAAAAAAAAAAAAAAAAAAAANRILgAAAAAAnNwIzUejRCOI4D2z9Yq5c%3DBCX76yG6JVSrKdmZnLbh98XRuxfh38s8mxgVxZ07YdLv7vT",
        "content-type": "application/x-www-form-urlencoded",
        "x-csrf-token": csrf,
        "x-twitter-active-user": "yes",
        "x-twitter-auth-type": "OAuth2Session",
        "x-twitter-client-language": document.documentElement.lang || "en",
      },
      body: body.toString(),
    });

    if (!response.ok) {
      const text = await response.text().catch(() => "");
      throw new Error(`block request failed ${response.status}: ${text.slice(0, 160)}`);
    }

    return response.json().catch(() => ({}));
  }

  async function unblockHandle(handle) {
    const normalized = normalizeHandle(handle);
    if (!normalized) throw new Error("invalid handle");

    const csrf = getCookie("ct0");
    if (!csrf) throw new Error("missing csrf token; refresh X and sign in again");

    const body = new URLSearchParams({
      screen_name: normalized,
      skip_status: "true",
    });

    const response = await fetch("/i/api/1.1/blocks/destroy.json", {
      method: "POST",
      credentials: "include",
      headers: {
        authorization:
          "Bearer AAAAAAAAAAAAAAAAAAAAANRILgAAAAAAnNwIzUejRCOI4D2z9Yq5c%3DBCX76yG6JVSrKdmZnLbh98XRuxfh38s8mxgVxZ07YdLv7vT",
        "content-type": "application/x-www-form-urlencoded",
        "x-csrf-token": csrf,
        "x-twitter-active-user": "yes",
        "x-twitter-auth-type": "OAuth2Session",
        "x-twitter-client-language": document.documentElement.lang || "en",
      },
      body: body.toString(),
    });

    if (!response.ok) {
      const text = await response.text().catch(() => "");
      throw new Error(`unblock request failed ${response.status}: ${text.slice(0, 160)}`);
    }

    return response.json().catch(() => ({}));
  }

  function getNextPendingQueueItem() {
    return loadQueue().find((item) => item.status === "pending" && normalizeHandle(item.handle));
  }

  function stopAutoBlock(reason) {
    clearTimeout(state.autoBlockTimer);
    state.autoBlockTimer = null;
    state.autoBlockRunning = false;
    if (reason) {
      logEntry({ action: "auto_block_stop", reason, text: "", handle: "", name: "", url: location.href });
    }
    renderQueuePanel();
  }

  function scheduleNextAutoBlock(delayMs) {
    clearTimeout(state.autoBlockTimer);
    state.autoBlockTimer = setTimeout(processAutoBlockQueue, delayMs);
    renderQueuePanel();
  }

  async function processAutoBlockQueue() {
    if (!state.autoBlockRunning) return;

    const settings = loadTimeSettings();
    const elapsedMs = Date.now() - state.autoBlockStartedAt;
    if (elapsedMs > settings.maxRunMinutes * 60 * 1000) {
      stopAutoBlock(`max run time reached: ${settings.maxRunMinutes} minutes`);
      return;
    }

    const item = getNextPendingQueueItem();
    if (!item) {
      stopAutoBlock("queue empty");
      return;
    }

    updateQueue(item.handle, { status: "blocking", blockingAt: new Date().toISOString() });
    try {
      await blockHandle(item.handle);
      state.autoBlockProcessed += 1;
      updateQueue(item.handle, {
        status: "blocked",
        blockedAt: new Date().toISOString(),
        error: "",
      });
      logEntry({
        ...item,
        action: "auto_block",
        reason: `auto blocked from queue; ${item.reason || ""}`,
      });
    } catch (error) {
      updateQueue(item.handle, {
        status: "failed",
        failedAt: new Date().toISOString(),
        error: String(error && error.message ? error.message : error),
      });
      logEntry({
        ...item,
        action: "auto_block_failed",
        reason: String(error && error.message ? error.message : error),
      });
    }

    if (!state.autoBlockRunning) return;
    scheduleNextAutoBlock(getQueueDelayMs(state.autoBlockProcessed));
  }

  function startAutoBlock() {
    if (state.autoBlockRunning) return;
    state.autoBlockRunning = true;
    state.autoBlockProcessed = 0;
    state.autoBlockStartedAt = Date.now();
    logEntry({ action: "auto_block_start", reason: "started queue auto block", text: "", handle: "", name: "", url: location.href });
    scheduleNextAutoBlock(1000);
  }

  function removeNotice(article) {
    if (article.__xbrfNotice) {
      article.__xbrfNotice.remove();
      article.__xbrfNotice = null;
    }
  }

  function getQueueStatus(handle) {
    const item = loadQueue().find((entry) => normalizeHandle(entry.handle) === normalizeHandle(handle));
    return item ? item.status || "pending" : "hidden";
  }

  async function markFalsePositive(article, entry) {
    const handle = entry.handle || "";
    const normalized = normalizeHandle(handle);
    if (!normalized) return;

    addWhitelistHandle(normalized);
    removeFromQueue(normalized);

    for (const candidate of document.querySelectorAll(TWEET_SELECTOR)) {
      if (normalizeHandle(getAuthorHandle(candidate)) === normalized) {
        candidate.style.display = "";
        candidate.style.visibility = "";
        candidate.removeAttribute(HIDDEN_ATTR);
        candidate.dataset.xBotReplyFilterHidden = "0";
        removeNotice(candidate);
      }
    }

    logEntry({
      ...entry,
      action: "false_positive",
      reason: "added to whitelist; future hide/block disabled for this user",
    });

    try {
      await unblockHandle(normalized);
      logEntry({
        ...entry,
        action: "auto_unblock",
        reason: "unblocked after false positive",
      });
    } catch (error) {
      logEntry({
        ...entry,
        action: "auto_unblock_failed",
        reason: String(error && error.message ? error.message : error),
      });
    }

    scan();
  }

  function renderHiddenNotice(article, result) {
    const entry = articleToLog(article, "filter", `score ${result.score}; ${result.reasons.join(", ")}`);
    if (!entry) return;

    let notice = article.__xbrfNotice;
    if (!notice) {
      notice = document.createElement("div");
      notice.className = "xbrf-hidden-card";
      article.__xbrfNotice = notice;
      article.parentNode?.insertBefore(notice, article);
    }

    notice.innerHTML = "";

    const close = document.createElement("button");
    close.type = "button";
    close.className = "xbrf-hidden-close";
    close.textContent = "x";
    close.title = "误判：解除拉黑并加入白名单";
    close.addEventListener("click", (event) => {
      event.preventDefault();
      event.stopPropagation();
      markFalsePositive(article, entry);
    });

    const top = document.createElement("div");
    top.className = "xbrf-hidden-top";

    const icon = document.createElement("span");
    icon.textContent = "✓";
    icon.className = "xbrf-hidden-ok";

    const name = document.createElement("strong");
    name.textContent = entry.name || "未知用户";

    const handle = document.createElement("a");
    handle.href = `/${normalizeHandle(entry.handle)}`;
    handle.target = "_blank";
    handle.rel = "noreferrer";
    handle.textContent = entry.handle || "";

    const status = document.createElement("span");
    status.className = "xbrf-hidden-status";
    status.textContent = ` ${getQueueStatus(entry.handle)}`;

    top.append(icon, name, " ", handle, status);

    const text = document.createElement("div");
    text.className = "xbrf-hidden-text";
    text.textContent = entry.text || "";

    const reason = document.createElement("div");
    reason.className = "xbrf-hidden-reason";
    reason.textContent = `命中规则: ${result.reasons.join(" / ")}`;

    notice.append(close, top, text, reason);
  }

  function setHidden(article, hidden, result) {
    article.dataset.xBotReplyFilterHidden = hidden ? "1" : "0";

    if (!hidden || Date.now() < state.revealUntil || !config.enabled) {
      removeNotice(article);
      article.style.display = "";
      article.style.visibility = "";
      article.title = hidden && result.reasons.length ? `X Bot Reply Filter: ${result.reasons.join(", ")}` : "";
      return;
    }

    article.setAttribute(HIDDEN_ATTR, "1");
    article.title = `X Bot Reply Filter: score ${result.score}; ${result.reasons.join(", ")}`;
    renderHiddenNotice(article, result);
    article.style.display = "none";

    if (config.logFilteredReplies) {
      const entry = articleToLog(article, "filter", `score ${result.score}; ${result.reasons.join(", ")}`);
      if (entry) {
        logEntry(entry);
        queueEntry(entry);
      }
    }
    if (!article.dataset.xbrfStatsLogged) {
      for (const ruleHit of result.ruleHits || []) addRuleHit(ruleHit);
      article.dataset.xbrfStatsLogged = "1";
    }
  }

  function scan() {
    const articles = [...document.querySelectorAll(TWEET_SELECTOR)];
    const counts = new Map();

    for (const article of articles) {
      const text = normalizeText(getArticleText(article));
      if (text.length >= 12) {
        counts.set(text, (counts.get(text) || 0) + 1);
      }
    }

    let hidden = 0;
    for (const article of articles) {
      const text = normalizeText(getArticleText(article));
      const duplicateCount = counts.get(text) || 0;
      const result = scoreArticle(article, duplicateCount);
      const shouldHide = result.score >= config.threshold;
      if (shouldHide) hidden += 1;
      setHidden(article, shouldHide, result);
    }

    state.hiddenCount = hidden;
    renderPanel();
  }

  function scheduleScan() {
    clearTimeout(state.timer);
    state.timer = setTimeout(scan, config.scanDelayMs);
  }

  function revealTemporarily() {
    state.revealUntil = Date.now() + config.revealMs;
    scan();
    setTimeout(scan, config.revealMs + 50);
  }

  function clearLogs() {
    saveLogs([]);
    state.loggedKeys.clear();
    renderLogPanel();
  }

  function exportLogs() {
    const logs = loadLogs();
    const blob = new Blob([JSON.stringify(logs, null, 2)], { type: "application/json" });
    const url = URL.createObjectURL(blob);
    const link = document.createElement("a");
    link.href = url;
    link.download = `x-bot-reply-filter-logs-${Date.now()}.json`;
    link.click();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  }

  function renderLogPanel() {
    if (!state.logPanel) return;
    const logs = loadLogs();
    const body = state.logPanel.querySelector("[data-role='log-body']");
    const count = state.logPanel.querySelector("[data-role='log-count']");
    count.textContent = `${logs.length} 条`;
    body.innerHTML = "";

    if (!logs.length) {
      const empty = document.createElement("div");
      empty.className = "xbrf-empty";
      empty.textContent = "暂无日志";
      body.appendChild(empty);
      return;
    }

    for (const item of logs.slice(0, 80)) {
      const row = document.createElement("div");
      row.className = "xbrf-log-row";

      const meta = document.createElement("div");
      meta.className = "xbrf-log-meta";
      meta.textContent = `${new Date(item.time).toLocaleString()} | ${item.action} | ${item.handle || item.name || "unknown"}`;

      const reason = document.createElement("div");
      reason.className = "xbrf-log-reason";
      reason.textContent = [item.reason || "", item.error ? `error: ${item.error}` : ""].filter(Boolean).join(" | ");

      const text = document.createElement("div");
      text.className = "xbrf-log-text";
      text.textContent = item.text || "";

      const url = document.createElement("a");
      url.href = item.url || item.page || "#";
      url.target = "_blank";
      url.rel = "noreferrer";
      url.textContent = "打开原文";

      row.append(meta, reason, text, url);
      body.appendChild(row);
    }
  }

  function ensureLogPanel() {
    if (state.logPanel) return;
    state.logPanel = document.createElement("div");
    state.logPanel.id = "x-bot-reply-filter-log-panel";
    state.logPanel.innerHTML = `
      <div class="xbrf-log-head">
        <strong>过滤日志</strong>
        <span data-role="log-count"></span>
      </div>
      <div class="xbrf-log-actions">
        <button type="button" data-action="export-logs">导出</button>
        <button type="button" data-action="clear-logs">清空</button>
        <button type="button" data-action="close-logs">关闭</button>
      </div>
      <div data-role="log-body" class="xbrf-log-body"></div>
    `;
    document.documentElement.appendChild(state.logPanel);

    state.logPanel.addEventListener("click", (event) => {
      const button = event.target.closest("button");
      if (!button) return;
      if (button.dataset.action === "export-logs") exportLogs();
      if (button.dataset.action === "clear-logs") clearLogs();
      if (button.dataset.action === "close-logs") state.logPanel.style.display = "none";
    });
  }

  function renderQueuePanel() {
    if (!state.queuePanel) return;
    const queue = loadQueue();
    const timeSettings = loadTimeSettings();
    const body = state.queuePanel.querySelector("[data-role='queue-body']");
    const count = state.queuePanel.querySelector("[data-role='queue-count']");
    const nextDelay = state.queuePanel.querySelector("[data-role='next-delay']");
    const autoStatus = state.queuePanel.querySelector("[data-role='auto-status']");
    const pendingCount = queue.filter((item) => item.status === "pending").length;
    count.textContent = `${pendingCount} 待处理`;
    state.queuePanel.querySelector("[data-role='base-interval']").value = timeSettings.baseIntervalSec;
    state.queuePanel.querySelector("[data-role='pause-20']").value = timeSettings.pauseEvery20Sec;
    state.queuePanel.querySelector("[data-role='pause-60']").value = timeSettings.pauseEvery60Min;
    state.queuePanel.querySelector("[data-role='max-run']").value = timeSettings.maxRunMinutes;
    autoStatus.textContent = state.autoBlockRunning
      ? `自动拉黑运行中，本轮已处理 ${state.autoBlockProcessed}`
      : "自动拉黑已停止";
    nextDelay.textContent = `基础 ${timeSettings.baseIntervalSec}s | 每20个停 ${timeSettings.pauseEvery20Sec}s | 每60个停 ${timeSettings.pauseEvery60Min}m`;
    body.innerHTML = "";

    if (!queue.length) {
      const empty = document.createElement("div");
      empty.className = "xbrf-empty";
      empty.textContent = "暂无排队账号";
      body.appendChild(empty);
      return;
    }

    for (const item of queue) {
      const row = document.createElement("div");
      row.className = "xbrf-log-row";

      const meta = document.createElement("div");
      meta.className = "xbrf-log-meta";

      const profile = document.createElement("a");
      profile.href = `/${normalizeHandle(item.handle)}`;
      profile.target = "_blank";
      profile.rel = "noreferrer";
      profile.textContent = `${item.name || ""} ${item.handle || ""}`.trim() || "unknown";

      const status = document.createElement("span");
      status.textContent = ` | ${item.status || "pending"}`;

      meta.append(profile, status);

      const reason = document.createElement("div");
      reason.className = "xbrf-log-reason";
      reason.textContent = item.reason || "";

      const text = document.createElement("div");
      text.className = "xbrf-log-text";
      text.textContent = item.text || "";

      const actions = document.createElement("div");
      actions.className = "xbrf-inline-actions";
      actions.innerHTML = `
        <button type="button" data-action="mark-blocked" data-handle="${item.handle || ""}">标记已拉黑</button>
        <button type="button" data-action="retry-queue" data-handle="${item.handle || ""}">重试</button>
        <button type="button" data-action="remove-queue" data-handle="${item.handle || ""}">移除</button>
      `;

      row.append(meta, reason, text, actions);
      body.appendChild(row);
    }
  }

  function ensureQueuePanel() {
    if (state.queuePanel) return;
    state.queuePanel = document.createElement("div");
    state.queuePanel.id = "x-bot-reply-filter-queue-panel";
    state.queuePanel.innerHTML = `
      <div class="xbrf-log-head">
        <strong>拉黑排队</strong>
        <span data-role="queue-count"></span>
      </div>
      <div class="xbrf-log-actions">
        <button type="button" data-action="start-auto-block">开始自动拉黑</button>
        <button type="button" data-action="stop-auto-block">停止</button>
        <button type="button" data-action="clear-completed">清理完成项</button>
        <button type="button" data-action="close-queue">关闭</button>
      </div>
      <div class="xbrf-time-settings">
        <label>基础间隔（秒）
          <input type="number" step="any" data-role="base-interval">
        </label>
        <label>每20个暂停（秒）
          <input type="number" step="any" data-role="pause-20">
        </label>
        <label>每60个暂停（分钟）
          <input type="number" step="any" data-role="pause-60">
        </label>
        <label>最长运行（分钟）
          <input type="number" step="any" data-role="max-run">
        </label>
        <button type="button" data-action="save-time-settings">保存时间</button>
        <span data-role="auto-status"></span>
        <span data-role="next-delay"></span>
      </div>
      <div data-role="queue-body" class="xbrf-log-body"></div>
    `;
    document.documentElement.appendChild(state.queuePanel);

    state.queuePanel.addEventListener("click", (event) => {
      const button = event.target.closest("button");
      if (!button) return;
      const handle = button.dataset.handle;
      if (button.dataset.action === "mark-blocked") {
        updateQueue(handle, { status: "blocked", blockedAt: new Date().toISOString() });
        const item = loadQueue().find((entry) => normalizeHandle(entry.handle) === normalizeHandle(handle));
        if (item) logEntry({ ...item, action: "manual_block_marked", reason: "marked blocked from review queue" });
      }
      if (button.dataset.action === "retry-queue") {
        updateQueue(handle, { status: "pending", error: "", failedAt: "" });
      }
      if (button.dataset.action === "remove-queue") removeFromQueue(handle);
      if (button.dataset.action === "start-auto-block") startAutoBlock();
      if (button.dataset.action === "stop-auto-block") stopAutoBlock("stopped by user");
      if (button.dataset.action === "clear-completed") {
        saveQueue(loadQueue().filter((item) => item.status !== "blocked"));
        renderQueuePanel();
      }
      if (button.dataset.action === "save-time-settings") {
        saveTimeSettings({
          baseIntervalSec: state.queuePanel.querySelector("[data-role='base-interval']").value,
          pauseEvery20Sec: state.queuePanel.querySelector("[data-role='pause-20']").value,
          pauseEvery60Min: state.queuePanel.querySelector("[data-role='pause-60']").value,
          maxRunMinutes: state.queuePanel.querySelector("[data-role='max-run']").value,
        });
        renderQueuePanel();
      }
      if (button.dataset.action === "close-queue") state.queuePanel.style.display = "none";
    });
  }

  function renderRulesPanel() {
    if (!state.rulesPanel) return;
    const rules = loadRules();
    state.rulesPanel.querySelector("[data-role='content-rules']").value = rules.contentKeywords.join("\n");
    state.rulesPanel.querySelector("[data-role='name-rules']").value = rules.nameKeywords.join("\n");
    state.rulesPanel.querySelector("[data-role='regex-rules']").value = rules.regexKeywords.join("\n");

    const stats = loadJson(STATS_KEY, {});
    const statsBody = state.rulesPanel.querySelector("[data-role='stats-body']");
    const rows = Object.entries(stats).sort((a, b) => b[1] - a[1]).slice(0, 80);
    statsBody.textContent = rows.length
      ? rows.map(([key, count]) => `${count}  ${key}`).join("\n")
      : "暂无命中统计";
  }

  function ensureRulesPanel() {
    if (state.rulesPanel) return;
    state.rulesPanel = document.createElement("div");
    state.rulesPanel.id = "x-bot-reply-filter-rules-panel";
    state.rulesPanel.innerHTML = `
      <div class="xbrf-log-head">
        <strong>关键词规则</strong>
        <span>每行一条</span>
      </div>
      <div class="xbrf-rules-grid">
        <label>内容关键词<textarea data-role="content-rules"></textarea></label>
        <label>用户名关键词<textarea data-role="name-rules"></textarea></label>
        <label>正则规则<textarea data-role="regex-rules"></textarea></label>
      </div>
      <div class="xbrf-log-actions">
        <button type="button" data-action="save-rules">保存</button>
        <button type="button" data-action="export-rules">导出</button>
        <button type="button" data-action="import-rules">导入</button>
        <button type="button" data-action="reset-rules">重置</button>
        <button type="button" data-action="close-rules">关闭</button>
      </div>
      <pre data-role="stats-body" class="xbrf-stats"></pre>
    `;
    document.documentElement.appendChild(state.rulesPanel);

    state.rulesPanel.addEventListener("click", (event) => {
      const button = event.target.closest("button");
      if (!button) return;
      const readRules = () => ({
        contentKeywords: state.rulesPanel.querySelector("[data-role='content-rules']").value.split("\n"),
        nameKeywords: state.rulesPanel.querySelector("[data-role='name-rules']").value.split("\n"),
        regexKeywords: state.rulesPanel.querySelector("[data-role='regex-rules']").value.split("\n"),
      });

      if (button.dataset.action === "save-rules") {
        saveRules(readRules());
        scan();
        renderRulesPanel();
      }
      if (button.dataset.action === "export-rules") {
        const blob = new Blob([JSON.stringify(loadRules(), null, 2)], { type: "application/json" });
        const url = URL.createObjectURL(blob);
        const link = document.createElement("a");
        link.href = url;
        link.download = `x-bot-reply-filter-rules-${Date.now()}.json`;
        link.click();
        setTimeout(() => URL.revokeObjectURL(url), 1000);
      }
      if (button.dataset.action === "import-rules") {
        const raw = prompt("Paste rules JSON");
        if (!raw) return;
        try {
          saveRules(JSON.parse(raw));
          scan();
          renderRulesPanel();
        } catch {
          alert("Invalid rules JSON");
        }
      }
      if (button.dataset.action === "reset-rules") {
        saveRules(defaultCustomRules);
        scan();
        renderRulesPanel();
      }
      if (button.dataset.action === "close-rules") state.rulesPanel.style.display = "none";
    });
  }

  function renderPanel() {
    if (!state.panel) {
      state.toolbarCollapsed = localStorage.getItem(UI_COLLAPSED_KEY) === "1";
      const uiPos = loadUiPosition();
      state.panel = document.createElement("div");
      state.panel.id = "x-bot-reply-filter-panel";
      state.panel.innerHTML = `
        <button type="button" class="xbrf-tool-main" data-action="collapse" title="收起/展开工具栏">XBF</button>
        <div class="xbrf-tool-stack">
          <button type="button" data-action="toggle" title="开启/关闭自动隐藏"></button>
          <button type="button" data-action="reveal" title="临时显示被隐藏回复">显示</button>
          <button type="button" data-action="queue" title="拉黑队列">队列</button>
          <button type="button" data-action="rules" title="关键词和正则">规则</button>
          <button type="button" data-action="logs" title="日志">日志</button>
        </div>
        <span data-role="count" class="xbrf-count"></span>
      `;
      state.panel.style.right = `${uiPos.right}px`;
      state.panel.style.bottom = `${uiPos.bottom}px`;
      document.documentElement.appendChild(state.panel);

      const style = document.createElement("style");
      style.textContent = `
        #x-bot-reply-filter-panel {
          position: fixed;
          z-index: 2147483647;
          display: flex;
          flex-direction: column;
          align-items: center;
          gap: 7px;
          width: 58px;
          padding: 7px 6px;
          border: 1.5px solid rgba(207,217,222,.95);
          border-radius: 20px;
          background: rgba(255,255,255,.84);
          color: #0f1419;
          font: 12px/1.2 system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
          box-shadow: 0 4px 18px rgba(15,20,25,.16);
          backdrop-filter: blur(6px);
          -webkit-backdrop-filter: blur(6px);
          user-select: none;
        }
        #x-bot-reply-filter-panel.xbrf-collapsed .xbrf-tool-stack,
        #x-bot-reply-filter-panel.xbrf-collapsed .xbrf-count {
          display: none;
        }
        #x-bot-reply-filter-panel button {
          width: 46px;
          height: 34px;
          border: 1px solid #cfd9de;
          border-radius: 999px;
          padding: 0;
          background: #fff;
          color: #536471;
          font: 700 12px/32px system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
          cursor: pointer;
          text-align: center;
          box-shadow: 0 2px 8px rgba(15,20,25,.10);
          transition: transform .15s, box-shadow .15s, background .15s, color .15s;
        }
        #x-bot-reply-filter-panel button:hover {
          transform: scale(1.06);
          box-shadow: 0 3px 12px rgba(15,20,25,.18);
        }
        #x-bot-reply-filter-panel .xbrf-tool-main {
          width: 46px;
          color: #fff;
          background: #1d9bf0;
          border-color: #1d9bf0;
          cursor: grab;
        }
        #x-bot-reply-filter-panel .xbrf-tool-stack {
          display: flex;
          flex-direction: column;
          gap: 7px;
          align-items: center;
        }
        #x-bot-reply-filter-panel .xbrf-count {
          min-width: 20px;
          height: 18px;
          padding: 0 5px;
          border-radius: 9px;
          background: #f4212e;
          color: #fff;
          font-size: 10px;
          font-weight: 800;
          line-height: 18px;
          text-align: center;
        }
        #x-bot-reply-filter-panel button.xbrf-enabled {
          color: #fff;
          background: #1d9bf0;
          border-color: #1d9bf0;
        }
        #x-bot-reply-filter-panel button.xbrf-disabled {
          color: #536471;
          background: #eff3f4;
          border-color: #cfd9de;
        }
        #x-bot-reply-filter-panel button.xbrf-running {
          color: #fff;
          background: #f4212e;
          border-color: #f4212e;
        }
        #x-bot-reply-filter-panel button.xbrf-has-items {
          color: #fff;
          background: #ff7a00;
          border-color: #ff7a00;
        }
        #x-bot-reply-filter-log-panel,
        #x-bot-reply-filter-queue-panel,
        #x-bot-reply-filter-rules-panel {
          position: fixed;
          right: 74px;
          bottom: 118px;
          z-index: 2147483647;
          width: min(720px, calc(100vw - 96px));
          max-height: min(700px, calc(100vh - 90px));
          display: none;
          overflow: hidden;
          border: 1px solid #cfd9de;
          border-radius: 12px;
          background: rgba(255,255,255,.96);
          color: #0f1419;
          font: 13px/1.35 system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
          box-shadow: 0 8px 28px rgba(15,20,25,.18);
          backdrop-filter: blur(6px);
          -webkit-backdrop-filter: blur(6px);
        }
        #x-bot-reply-filter-log-panel button,
        #x-bot-reply-filter-queue-panel button,
        #x-bot-reply-filter-rules-panel button {
          border: 1px solid #cfd9de;
          border-radius: 8px;
          padding: 4px 10px;
          background: #fff;
          color: #0f1419;
          font: 600 12px/18px system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
          cursor: pointer;
        }
        #x-bot-reply-filter-log-panel .xbrf-log-head,
        #x-bot-reply-filter-log-panel .xbrf-log-actions,
        #x-bot-reply-filter-queue-panel .xbrf-log-head,
        #x-bot-reply-filter-queue-panel .xbrf-log-actions,
        #x-bot-reply-filter-rules-panel .xbrf-log-head,
        #x-bot-reply-filter-rules-panel .xbrf-log-actions {
          display: flex;
          align-items: center;
          justify-content: space-between;
          gap: 8px;
          padding: 10px 12px;
          border-bottom: 1px solid #eff3f4;
        }
        #x-bot-reply-filter-queue-panel .xbrf-log-actions,
        #x-bot-reply-filter-log-panel .xbrf-log-actions,
        #x-bot-reply-filter-rules-panel .xbrf-log-actions {
          justify-content: flex-end;
          flex-wrap: wrap;
        }
        #x-bot-reply-filter-log-panel .xbrf-log-body,
        #x-bot-reply-filter-queue-panel .xbrf-log-body {
          max-height: 500px;
          overflow: auto;
          padding: 10px 12px;
        }
        #x-bot-reply-filter-log-panel .xbrf-log-row,
        #x-bot-reply-filter-queue-panel .xbrf-log-row {
          padding: 9px 0;
          border-bottom: 1px dashed #cfd9de;
        }
        #x-bot-reply-filter-log-panel .xbrf-log-meta,
        #x-bot-reply-filter-queue-panel .xbrf-log-meta {
          color: #0f1419;
          font-weight: 700;
        }
        #x-bot-reply-filter-log-panel .xbrf-log-reason,
        #x-bot-reply-filter-queue-panel .xbrf-log-reason {
          color: #d65f00;
          margin-top: 3px;
          font-size: 12px;
        }
        #x-bot-reply-filter-log-panel .xbrf-log-text,
        #x-bot-reply-filter-queue-panel .xbrf-log-text {
          color: #0f1419;
          margin: 6px 0;
          white-space: pre-wrap;
          word-break: break-word;
        }
        #x-bot-reply-filter-queue-panel .xbrf-inline-actions {
          display: flex;
          gap: 8px;
          flex-wrap: wrap;
        }
        #x-bot-reply-filter-queue-panel .xbrf-time-settings {
          display: grid;
          grid-template-columns: repeat(4, minmax(110px, 1fr));
          gap: 8px;
          align-items: end;
          padding: 10px 12px;
          border-bottom: 1px solid #eff3f4;
        }
        #x-bot-reply-filter-queue-panel .xbrf-time-settings label {
          display: flex;
          flex-direction: column;
          gap: 4px;
          color: #536471;
          font-size: 12px;
        }
        #x-bot-reply-filter-queue-panel .xbrf-time-settings input {
          min-width: 0;
          border: 1px solid #cfd9de;
          border-radius: 6px;
          padding: 6px;
          background: #fff;
          color: #0f1419;
          font: inherit;
        }
        #x-bot-reply-filter-queue-panel .xbrf-time-settings span {
          color: #536471;
          font-size: 12px;
        }
        #x-bot-reply-filter-log-panel a,
        #x-bot-reply-filter-queue-panel a {
          color: #1d9bf0;
        }
        #x-bot-reply-filter-rules-panel .xbrf-rules-grid {
          display: grid;
          grid-template-columns: repeat(3, minmax(0, 1fr));
          gap: 10px;
          padding: 10px;
        }
        #x-bot-reply-filter-rules-panel label {
          display: flex;
          flex-direction: column;
          gap: 6px;
          color: #536471;
          font-weight: 600;
        }
        #x-bot-reply-filter-rules-panel textarea {
          min-height: 160px;
          resize: vertical;
          border: 1px solid #cfd9de;
          border-radius: 6px;
          padding: 8px;
          background: #fff;
          color: #0f1419;
          font: 12px/1.35 ui-monospace, SFMono-Regular, Consolas, monospace;
        }
        #x-bot-reply-filter-rules-panel .xbrf-stats {
          max-height: 180px;
          overflow: auto;
          margin: 0;
          padding: 10px;
          border-top: 1px solid #eff3f4;
          color: #536471;
          white-space: pre-wrap;
          font: 12px/1.35 ui-monospace, SFMono-Regular, Consolas, monospace;
        }
        @media (max-width: 720px) {
          #x-bot-reply-filter-queue-panel .xbrf-time-settings,
          #x-bot-reply-filter-rules-panel .xbrf-rules-grid {
            grid-template-columns: 1fr;
          }
        }
        #x-bot-reply-filter-log-panel .xbrf-empty {
          color: #536471;
          padding: 10px 0;
        }
        .xbrf-hidden-card {
          position: relative;
          margin: 0;
          padding: 8px 34px 8px 10px;
          border-left: 3px solid #18b579;
          background: rgba(255,255,255,.98);
          color: #0f1419;
          font: 13px/1.35 system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
          box-shadow: inset 0 -1px rgba(0,0,0,.08);
          word-break: break-word;
        }
        .xbrf-hidden-card a {
          color: #536471;
          text-decoration: none;
        }
        .xbrf-hidden-card a:hover {
          text-decoration: underline;
        }
        .xbrf-hidden-ok {
          color: #00a35c;
          margin-right: 6px;
          font-weight: 700;
        }
        .xbrf-hidden-top {
          display: flex;
          flex-wrap: wrap;
          align-items: center;
          gap: 3px;
          padding-right: 4px;
        }
        .xbrf-hidden-status {
          color: #d65f00;
          font-weight: 600;
        }
        .xbrf-hidden-text {
          margin-top: 2px;
          color: #0f1419;
        }
        .xbrf-hidden-reason {
          margin-top: 2px;
          color: #536471;
          font-size: 12px;
        }
        .xbrf-hidden-close {
          position: absolute;
          right: 8px;
          top: 6px;
          width: 20px;
          height: 20px;
          border: 0;
          border-radius: 999px;
          background: #e6e8ea;
          color: #536471;
          cursor: pointer;
          line-height: 20px;
          padding: 0;
          font: 14px/20px system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
        }
        .xbrf-hidden-close:hover {
          background: #d6d9dc;
          color: #0f1419;
        }
      `;
      document.documentElement.appendChild(style);
      ensureLogPanel();
      ensureQueuePanel();
      ensureRulesPanel();

      const syncToolbar = () => {
        state.panel.classList.toggle("xbrf-collapsed", state.toolbarCollapsed);
      };
      syncToolbar();

      let drag = null;
      state.panel.querySelector(".xbrf-tool-main").addEventListener("pointerdown", (event) => {
        if (event.button !== 0) return;
        drag = {
          x: event.clientX,
          y: event.clientY,
          right: Number.parseFloat(state.panel.style.right) || 18,
          bottom: Number.parseFloat(state.panel.style.bottom) || 160,
          moved: false,
        };
        state.panel.querySelector(".xbrf-tool-main").setPointerCapture?.(event.pointerId);
      });
      state.panel.querySelector(".xbrf-tool-main").addEventListener("pointermove", (event) => {
        if (!drag) return;
        const dx = event.clientX - drag.x;
        const dy = event.clientY - drag.y;
        if (Math.abs(dx) > 4 || Math.abs(dy) > 4) drag.moved = true;
        const nextRight = Math.max(6, drag.right - dx);
        const nextBottom = Math.max(6, drag.bottom - dy);
        state.panel.style.right = `${nextRight}px`;
        state.panel.style.bottom = `${nextBottom}px`;
      });
      state.panel.querySelector(".xbrf-tool-main").addEventListener("pointerup", (event) => {
        if (!drag) return;
        state.panel.querySelector(".xbrf-tool-main").releasePointerCapture?.(event.pointerId);
        const wasDrag = drag.moved;
        state.panel.dataset.xbrfDragged = wasDrag ? "1" : "0";
        saveUiPosition({
          right: Number.parseFloat(state.panel.style.right) || 18,
          bottom: Number.parseFloat(state.panel.style.bottom) || 160,
        });
        drag = null;
        if (wasDrag) {
          event.preventDefault();
          event.stopPropagation();
        }
      });

      state.panel.addEventListener("click", (event) => {
        const button = event.target.closest("button");
        if (!button) return;
        if (button.dataset.action === "collapse") {
          if (state.panel.dataset.xbrfDragged === "1") {
            state.panel.dataset.xbrfDragged = "0";
            return;
          }
          state.toolbarCollapsed = !state.toolbarCollapsed;
          localStorage.setItem(UI_COLLAPSED_KEY, state.toolbarCollapsed ? "1" : "0");
          syncToolbar();
        }
        if (button.dataset.action === "toggle") {
          config.enabled = !config.enabled;
          scan();
        }
        if (button.dataset.action === "reveal") {
          revealTemporarily();
        }
        if (button.dataset.action === "logs") {
          ensureLogPanel();
          renderLogPanel();
          state.logPanel.style.display = getComputedStyle(state.logPanel).display === "none" ? "block" : "none";
        }
        if (button.dataset.action === "queue") {
          ensureQueuePanel();
          renderQueuePanel();
          state.queuePanel.style.display = getComputedStyle(state.queuePanel).display === "none" ? "block" : "none";
        }
        if (button.dataset.action === "rules") {
          ensureRulesPanel();
          renderRulesPanel();
          state.rulesPanel.style.display = getComputedStyle(state.rulesPanel).display === "none" ? "block" : "none";
        }
      });
    }

    const toggle = state.panel.querySelector('[data-action="toggle"]');
    const queueButton = state.panel.querySelector('[data-action="queue"]');
    const count = state.panel.querySelector('[data-role="count"]');
    const pendingCount = loadQueue().filter((item) => item.status === "pending").length;

    toggle.textContent = config.enabled ? "隐藏开" : "隐藏停";
    toggle.title = config.enabled ? "自动隐藏已开启，点击暂停" : "自动隐藏已暂停，点击开启";
    toggle.classList.toggle("xbrf-enabled", config.enabled);
    toggle.classList.toggle("xbrf-disabled", !config.enabled);

    queueButton.classList.toggle("xbrf-running", state.autoBlockRunning);
    queueButton.classList.toggle("xbrf-has-items", !state.autoBlockRunning && pendingCount > 0);
    queueButton.title = state.autoBlockRunning
      ? `自动拉黑运行中，本轮已处理 ${state.autoBlockProcessed}`
      : pendingCount > 0
        ? `拉黑队列：${pendingCount} 个待处理`
        : "拉黑队列";

    count.textContent = `${state.hiddenCount}`;
    count.style.display = state.hiddenCount > 0 ? "" : "none";
  }

  function rememberMenuArticle(event) {
    const article = event.target.closest?.(TWEET_SELECTOR);
    if (!article) return;
    const button = event.target.closest?.('button, [role="button"], [aria-haspopup="menu"]');
    const label = `${button?.getAttribute("aria-label") || ""} ${button?.textContent || ""}`;
    if (/more|更多|菜单|menu|overflow/i.test(label) || button?.getAttribute("aria-haspopup") === "menu") {
      state.lastMenuArticle = article;
      state.lastMenuArticleAt = Date.now();
    }
  }

  function captureBlockMuteClick(event) {
    const menuItem = event.target.closest?.('[role="menuitem"], [role="button"], button');
    if (!menuItem) return;
    const text = (menuItem.innerText || menuItem.textContent || "").trim();
    const actionMatch = text.match(/\b(Block|Mute)\b|拉黑|屏蔽|静音/i);
    if (!actionMatch) return;

    const actionText = actionMatch[0].toLowerCase();
    const action = /mute|静音/i.test(actionText) ? "manual_mute" : "manual_block";
    const directArticle = menuItem.closest(TWEET_SELECTOR);
    const fallbackArticle = Date.now() - state.lastMenuArticleAt < 15000 ? state.lastMenuArticle : null;
    const article = directArticle || fallbackArticle;
    const entry = articleToLog(article, action, `captured menu action: ${text}`);
    if (entry) {
      logEntry(entry);
      if (action === "manual_block") {
        updateQueue(entry.handle, { status: "blocked", blockedAt: new Date().toISOString() });
      }
    }
  }

  function start() {
    renderPanel();
    scan();

    const observer = new MutationObserver(scheduleScan);
    observer.observe(document.body, { childList: true, subtree: true });

    document.addEventListener("pointerdown", rememberMenuArticle, true);
    document.addEventListener("click", captureBlockMuteClick, true);
    window.addEventListener("scroll", scheduleScan, { passive: true });
    window.addEventListener("focus", scheduleScan);
  }

  if (document.body) {
    start();
  } else {
    window.addEventListener("DOMContentLoaded", start, { once: true });
  }
})();
