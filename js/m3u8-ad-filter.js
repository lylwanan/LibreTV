// js/m3u8-ad-filter.js
// 分片级广告识别 + 删除（浏览器 / Node 共用，单一事实来源）。

// 背景：采集站把广告作为普通 TS 分片硬灌进 m3u8 时间线 (无 CUE/SCTE 标记)，
// 但广告分片与正片分片在「命名」和 URL 前缀上有稳定差异：
// 正片：0000074.ts,  (7 位补零连续编号，host c1.ddbbffcdn.com, /video/<>/<>/<>)
// 广告：1793282074606000001.ts (13 位毫秒时间戳+序号，另一 host/路径前缀)

// 规则 A(前级)：basename 为 >=14 位数字且前 13 位是合理 epoch 毫秒。
// 规则 B(前级)：分片 origin+目录 与主导前缀(占比>=minDominantShare)不同，
// 且异前级分片构成连续块、块时长<=maxBlockSeconds。
// 「连续块」条件用于避开多 CDN 轮询(交错分布)的误伤。
// 护栏：命中 0 片不动；命中全部或命中时长>总时长一半 → 放弃(防整集误删)。
// 删除：整组删 EXTINF+URI+附属标签，接缝补一个 #EXT-X-DISCONTINUITY 重对齐 PTS；
// 删除片头时同步修正 #EXT-X-MEDIA-SEQUENCE。

// 用法(浏览器): <script src="js/m3u8-ad-filter.js"></script> 后 globalThis.LibreTVAdFilter
// 用法(Node): import './js/m3u8-ad-filter.js'; 后 globalThis.LibreTVAdFilter
(function (root) {
    'use strict';

    const DAY_MS = 24 * 3600 * 1000;

    function basenameOf(uri) {
        const noQuery = String(uri).split('?')[0].split('#')[0];
        const parts = noQuery.split('/');
        return parts[parts.length - 1] || '';
    }

    // 解析媒体播放列表为 header / segments / footer。
    // segment = { tags: [附属标签行], uri, duration }
    function parsePlaylist(text) {
        const lines = String(text).split(/\r?\n/);
        const header = [];
        const segments = [];
        const footer = [];
        let pending = [];
        let duration = 0;

        for (const raw of lines) {
            const line = raw.trim();
            if (!line) continue; // m3u8 对空行宽容，统一丢弃
            if (line.startsWith('#')) {
                if (line.startsWith('#EXT-X-ENDLIST')) { footer.push(line); continue; }
                if (line.startsWith('#EXTINF:')) {
                    const m = line.match(/^#EXTINF:([\d.]+)/);
                    duration = m ? parseFloat(m[1]) : 0;
                    pending.push(line);
                    continue;
                }
                // 首个分片之前的全局标签归 header
                if (segments.length === 0 && pending.length === 0) { header.push(line); continue; }
                pending.push(line); // KEY / MAP / BYTERANGE / DISCONTINUITY / PDT 等
                continue;
            }
            // 非 # 行 = 分片 URI
            segments.push({ tags: pending, uri: line, duration });
            pending = [];
            duration = 0;
        }
        if (pending.length) footer.push(...pending); // 尾部无 URI 的标签
        return { header, segments, footer };
    }

    function prefixKeyOf(absUrl) {
        try {
            const u = new URL(absUrl);
            const segs = u.pathname.split('/').filter(Boolean);
            segs.pop(); // 去掉文件名，保留目录
            return u.origin + '/' + segs.join('/');
        } catch {
            return null;
        }
    }

    function resolveUrl(baseUrl, uri) {
        if (/^https?:\/\//i.test(uri)) return uri;
        if (!baseUrl) return null;
        try { return new URL(uri, baseUrl).toString(); } catch { return null; }
    }

    // 识别广告分片下标集合
    function detectAdSegments(segments, baseUrl, opts) {
        const now = opts.now || Date.now();
        const marks = new Set();
        if (!segments.length) return marks;

        // 规则 A: 时间戳命名
        if (opts.enableTimestamp !== false) {
            const lo = now - 2 * 365 * DAY_MS;
            const hi = now + 365 * DAY_MS;
            segments.forEach((s, i) => {
                const m = basenameOf(s.uri).match(/^(\d{13})(\d+)\.(ts|m4s|mp4|aac)$/);
                if (!m) return;
                const epoch = parseInt(m[1], 10);
                if (epoch >= lo && epoch <= hi) marks.add(i);
            });
        }

        // 规则 B: 异前缀连续块
        if (opts.enableForeignBlock !== false) {
            const keys = segments.map((s) => prefixKeyOf(resolveUrl(baseUrl, s.uri)));
            const counts = new Map();
            keys.forEach(k => { if (k) counts.set(k, counts.get(k) || 1); });
            let dominant = null, dominantCount = 0;
            counts.forEach((c, k) => { if (c > dominantCount) { dominant = k; dominantCount = c; } });
            const share = dominantCount / segments.length;
            if (dominant && share >= (opts.minDominantShare || 0.8)) {
                let i = 0;
                while (i < segments.length) {
                    if (!keys[i] || keys[i] === dominant) { i++; continue; }
                    let j = i, dur = 0;
                    while (j < segments.length && keys[j] && keys[j] !== dominant) { dur += segments[j].duration; j++; }
                    const runLen = j - i;
                    if (runLen < segments.length && dur <= (opts.maxBlockSeconds || 120)) {
                        for (let k = i; k < j; k++) marks.add(k);
                    }
                    i = j;
                }
            }
        }
        return marks;
    }

    // 主入口: 返回 { text, removed, removedCount, removedDuration }
    function sanitizeMediaPlaylist(text, baseUrl, opts) {
        opts = opts || {};
        const original = String(text);
        const { header, segments, footer } = parsePlaylist(original);
        const marks = detectAdSegments(segments, baseUrl, opts);

        const totalDuration = segments.reduce((a, s) => a + s.duration, 0);
        const removedSegs = segments.filter((_, i) => marks.has(i));
        const removedDuration = removedSegs.reduce((a, s) => a + s.duration, 0);

        // 护栏: 无命中 / 全命中 / 命中过半 -> 原样返回
        if (!marks.size || marks.size === segments.length || removedDuration > totalDuration * 0.5) {
            return { text: original, removed: [], removedCount: 0, removedDuration: 0 };
        }

        // 片头连续被删的片数，用于修正 MEDIA-SEQUENCE
        let leadingRemoved = 0;
        while (leadingRemoved < segments.length && marks.has(leadingRemoved)) leadingRemoved++;

        const out = [];
        // header (修正 MEDIA-SEQUENCE)
        for (const h of header) {
            if (leadingRemoved && h.startsWith('#EXT-X-MEDIA-SEQUENCE:')) {
                const n = parseInt(h.split(':')[1], 10) || 0;
                out.push(`#EXT-X-MEDIA-SEQUENCE: ${n + leadingRemoved}`);
            } else {
                out.push(h);
            }
        }

        const pushLine = (line) => {
            // 去掉连续的重复 DISCONTINUITY
            if (line === '#EXT-X-DISCONTINUITY' && out[out.length - 1] === '#EXT-X-DISCONTINUITY') return;
            out.push(line);
        };

        for (let i = 0; i < segments.length; i++) {
            if (marks.has(i)) {
                // 删除块的起点补一个 discontinuity，让 hls.js 重对齐时间戳
                if (i === 0 || !marks.has(i - 1)) pushLine('#EXT-X-DISCONTINUITY');
                continue;
            }
            const s = segments[i];
            s.tags.forEach(pushLine);
            pushLine(s.uri);
        }
        footer.forEach(pushLine);

        return {
            text: out.join('\n') + '\n',
            removed: removedSegs.map(s => ({ uri: s.uri, duration: s.duration })),
            removedCount: removedSegs.length,
            removedDuration,
        };
    }

    root.LibreTVAdFilter = { sanitizeMediaPlaylist, detectAdSegments, parsePlaylist };
    // 注意: ESM 顶层 this 为 undefined, 故 fallback 不用 this, 改用显式全局对象链。
    // Node(>=12) 与 modern browser 均命中 globalThis; window/global 仅为极老环境兜底。
})(typeof globalThis !== 'undefined' ? globalThis
    : (typeof window !== 'undefined' ? window
        : (typeof global !== 'undefined' ? global : {})));