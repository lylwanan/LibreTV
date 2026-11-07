import path from 'path';
import express from 'express';
import axios from 'axios';
import cors from 'cors';
import { fileURLToPath } from 'url';
import fs from 'fs';
import crypto from 'crypto';
import http from 'http';
import https from 'https';
import dotenv from 'dotenv';
import {
  TVBOX_SITES,
  resolvePublicBase,
  toProxyUrl,
  rewritePlayUrl,
  buildTvboxConfig,
} from './tvbox-sites.mjs';
// 分片广告识别/剔除（浏览器与Node共用同一实现，副作用挂载globalThis.LibreTVADFilter）
import './js/m3u8-ad-filter.js';

dotenv.config();

// TVBox 对外基础地址（设备要能访问）。反代/公网场景务必显式配置，
// 否则会用请求头推断，可能得到内网地址导致设备拉不到分片。
// 例：TVBOX_PUBLIC_BASE=http://tvbox.liuyonglang.cn
const tvboxBase = (process.env.TVBOX_PUBLIC_BASE || '').replace(/\/+$/, '');
// 是否把封面图也走代理（防图片防盗链），默认开
const proxyPic = (process.env.TVBOX_PROXY_PIC || 'true') === 'true';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const config = {
  port: process.env.PORT || 8080,
  password: process.env.PASSWORD || '',
  corsOrigin: process.env.CORS_ORIGIN || '*',
  timeout: parseInt(process.env.REQUEST_TIMEOUT || '5000'),
  maxRetries: parseInt(process.env.MAX_RETRIES || '2'),
  cacheMaxAge: process.env.CACHE_MAX_AGE || '1d',
  userAgent: process.env.USER_AGENT || 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36',
  // 到源站的连接池大小(每个源站主机独立计数)，视频会连续请求大量 ts 分片，
  // 复用连接可省掉每片的 TCP 握手 + TLS 协商 + 慢启动开销。
  maxSockets: parseInt(process.env.PROXY_MAX_SOCKETS || '32'),
  debug: process.env.DEBUG === 'true'
};

// 全局 keep-alive Agent: 让代理到同一源站的分片请求复用已建立的 TCP/TLS 连接。
// keepAliveMsecs 定期探测包，避免空闲连接被中间设备静默断开后又复用失败。
const httpAgent = new http.Agent({
  keepAlive: true,
  keepAliveMsecs: 30000,
  maxSockets: config.maxSockets,
  maxFreeSockets: config.maxSockets
});
const httpsAgent = new https.Agent({
  keepAlive: true,
  keepAliveMsecs: 30000,
  maxSockets: config.maxSockets,
  maxFreeSockets: config.maxSockets
});

const log = (...args) => {
  if (config.debug) {
    console.log('[DEBUG]', ...args);
  }
};

const app = express();

app.use(cors({
  origin: config.corsOrigin,
  methods: ['GET', 'POST'],
  allowedHeaders: ['Content-Type', 'Authorization']
}));

app.use((req, res, next) => {
  res.setHeader('X-Content-Type-Options', 'nosniff');
  res.setHeader('X-Frame-Options', 'DENY');
  res.setHeader('X-XSS-Protection', '1; mode=block');
  next();
});

function sha256Hash(input) {
  return new Promise((resolve) => {
    const hash = crypto.createHash('sha256');
    hash.update(input);
    resolve(hash.digest('hex'));
  });
}

async function renderPage(filePath, password) {
  let content = fs.readFileSync(filePath, 'utf8');
  if (password !== '') {
    const sha256 = await sha256Hash(password);
    content = content.replace('{{PASSWORD}}', sha256);
  }
  return content;
}

app.get(['/', '/index.html', '/player.html'], async (req, res) => {
  try {
    let filePath;
    switch (req.path) {
      case '/player.html':
        filePath = path.join(__dirname, 'player.html');
        break;
      default: // '/' 和 '/index.html'
        filePath = path.join(__dirname, 'index.html');
        break;
    }
    
    const content = await renderPage(filePath, config.password);
    res.send(content);
  } catch (error) {
    console.error('页面渲染错误:', error);
    res.status(500).send('读取静态页面失败');
  }
});

app.get('/s=:keyword', async (req, res) => {
  try {
    const filePath = path.join(__dirname, 'index.html');
    const content = await renderPage(filePath, config.password);
    res.send(content);
  } catch (error) {
    console.error('搜索页面渲染错误:', error);
    res.status(500).send('读取静态页面失败');
  }
});

function isValidUrl(urlString) {
  try {
    const parsed = new URL(urlString);
    const allowedProtocols = ['http:', 'https:'];
    
    // 从环境变量获取阻止的主机名列表
    const blockedHostnames = (process.env.BLOCKED_HOSTS || 'localhost,127.0.0.1,0.0.0.0,::1').split(',');
    
    // 从环境变量获取阻止的 IP 前缀
    const blockedPrefixes = (process.env.BLOCKED_IP_PREFIXES || '192.168.,10.,172.').split(',');
    
    if (!allowedProtocols.includes(parsed.protocol)) return false;
    if (blockedHostnames.includes(parsed.hostname)) return false;
    
    for (const prefix of blockedPrefixes) {
      if (parsed.hostname.startsWith(prefix)) return false;
    }
    
    return true;
  } catch {
    return false;
  }
}

// ===== m3u8 处理：把播放列表里的分片/KEY/MAP 地址改写为同样走本代理 =====
// 逻辑移植自 api/proxy/[...path].mjs（Vercel 版），适配到 Express + axios。

const M3U8_MAX_RECURSION = parseInt(process.env.M3U8_MAX_RECURSION || '5', 10);
// 分片广告过滤开关（服务端 /proxy 与 tvbox 通道）。网页端另由播放器开关控制。
const AD_FILTER_ENABLED = (process.env.AD_FILTER_ENABLED || 'true') === 'true';
// 异前缀广告块的最大时长(秒)，超过则不认为是广告（防误删长段异源内容）
const AD_MAX_BLOCK_SECONDS = parseInt(process.env.AD_MAX_BLOCK_SECONDS || '120', 10);

// 把上游文本流读成字符串（仅用于 m3u8 这类小体积文本，绝不用于二进制分片）
function streamToString(stream) {
  return new Promise((resolve, reject) => {
    let data = '';
    stream.setEncoding('utf8');
    stream.on('data', (chunk) => { data += chunk; });
    stream.on('end', () => resolve(data));
    stream.on('error', reject);
  });
}

// 拉取上游文本（m3u8 主列表递归取子列表时用）
async function fetchUpstreamText(url) {
  const r = await axios({
    method: 'get',
    url,
    responseType: 'text',
    timeout: config.timeout,
    headers: { 'User-Agent': config.userAgent, 'Referer': 'https://movie.douban.com/' },
    httpAgent,
    httpsAgent,
  });
  return r.data;
}

// 取一个 URL 所在目录（用于解析 m3u8 里的相对分片地址）
function m3u8BaseUrl(urlStr) {
  if (!urlStr) return '';
  try {
    const parsed = new URL(urlStr);
    const segs = parsed.pathname.split('/').filter(Boolean);
    if (segs.length <= 1) return `${parsed.origin}/`;
    segs.pop();
    return `${parsed.origin}/${segs.join('/')}/`;
  } catch {
    const i = urlStr.lastIndexOf('/');
    return i > urlStr.indexOf('://') + 2 ? urlStr.substring(0, i + 1) : urlStr + '/';
  }
}

// 相对地址转绝对地址
function m3u8ResolveUrl(baseUrl, relativeUrl) {
  if (!relativeUrl) return '';
  if (/^https?:\/\//i.test(relativeUrl)) return relativeUrl;
  if (!baseUrl) return relativeUrl;
  try {
    return new URL(relativeUrl, baseUrl).toString();
  } catch {
    if (relativeUrl.startsWith('/')) {
      try { return new URL(relativeUrl, new URL(baseUrl).origin).toString(); } catch { return relativeUrl; }
    }
    return baseUrl.substring(0, baseUrl.lastIndexOf('/') + 1) + relativeUrl;
  }
}

// 处理媒体播放列表（分片列表）：把每个分片/KEY/MAP 改写为 /proxy/ 地址
function processMediaPlaylist(url, content, base) {
  const baseUrl = m3u8BaseUrl(url);
  // 先剔除广告分片，再做地址改写（保证改写后的列表不含广告）
  if (AD_FILTER_ENABLED && globalThis.LibreTVAdFilter) {
    const r = globalThis.LibreTVAdFilter.sanitizeMediaPlaylist(content, baseUrl, {
      maxBlockSeconds: AD_MAX_BLOCK_SECONDS,
    });
    if (r.removedCount) {
      log(`广告过滤: 移除 ${r.removedCount} 片 / ${r.removedDuration.toFixed(1)}s`, r.removed.map(x => x.uri));
    }
    content = r.text;
  }
  const lines = content.split('\n');
  const out = [];
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i].trim();
    if (!line && i === lines.length - 1) { out.push(line); continue; } // 保留末尾空行
    if (!line) continue;
    if (line.startsWith('#EXT-X-KEY')) {
      out.push(line.replace(/URI="([^"]+)"/, (m, uri) => `URI="${toProxyUrl(base, m3u8ResolveUrl(baseUrl, uri))}"`));
      continue;
    }
    if (line.startsWith('#EXT-X-MAP')) {
      out.push(line.replace(/URI="([^"]+)"/, (m, uri) => `URI="${toProxyUrl(base, m3u8ResolveUrl(baseUrl, uri))}"`));
      continue;
    }
    if (line.startsWith('#')) { out.push(line); continue; } // 其它标签原样保留
    out.push(toProxyUrl(base, m3u8ResolveUrl(baseUrl, line))); // 分片地址行
  }
  return out.join('\n');
}

// 处理主播放列表（多码率）：选最高带宽的子流，递归处理
async function processMasterPlaylist(url, content, base, depth) {
  if (depth > M3U8_MAX_RECURSION) {
    throw new Error(`m3u8 递归深度超过上限(${M3U8_MAX_RECURSION}): ${url}`);
  }
  const baseUrl = m3u8BaseUrl(url);
  const lines = content.split('\n');
  let bestBw = -1;
  let bestUrl = '';
  for (let i = 0; i < lines.length; i++) {
    if (lines[i].startsWith('#EXT-X-STREAM-INF')) {
      const m = lines[i].match(/BANDWIDTH=(\d+)/);
      const bw = m ? parseInt(m[1], 10) : 0;
      let uri = '';
      for (let j = i + 1; j < lines.length; j++) {
        const l = lines[j].trim();
        if (l && !l.startsWith('#')) { uri = l; i = j; break; }
      }
      if (uri && bw >= bestBw) { bestBw = bw; bestUrl = m3u8ResolveUrl(baseUrl, uri); }
    }
  }
  if (!bestUrl) {
    for (let i = 0; i < lines.length; i++) {
      const l = lines[i].trim();
      if (l && !l.startsWith('#') && /\.m3u8($|\?)/i.test(l)) { bestUrl = m3u8ResolveUrl(baseUrl, l); break; }
    }
  }
  if (!bestUrl) return processMediaPlaylist(url, content, base); // 没有子流，当媒体列表处理
  const variant = await fetchUpstreamText(bestUrl);
  if (!(variant && variant.trimStart().startsWith('#EXTM3U'))) {
    return processMediaPlaylist(bestUrl, variant, base);
  }
  return processM3u8Content(bestUrl, variant, base, depth + 1);
}

// m3u8 入口：区分主列表 / 媒体列表
async function processM3u8Content(url, content, base, depth) {
  if (content.includes('#EXT-X-STREAM-INF') || content.includes('#EXT-X-MEDIA:')) {
    return processMasterPlaylist(url, content, base, depth);
  }
  return processMediaPlaylist(url, content, base);
}

// 代理路由
// 流式转发时必须剥离的响应头（正确性不变量，非策略偏好，故不放入 .env 的 FILTERED_HEADERS）
// content-length/content-encoding：axios 会自动解压 gzip/deflate，解压时会丢掉 content-encoding
// 但保留解压前的 content-length；原样转发会被浏览器按错误长度截断 封面图/接口数据偶发损坏。
// 由于此时已无法区分"压缩"与"未压缩"，统一剥离，改用分块传输最稳妥
// transfer-encoding/connection：逐块头，由 Express/Node 自行管理，遗留会与分块传输冲突。
const STREAM_UNSAFE_HEADERS = ['content-length', 'content-encoding', 'transfer-encoding', 'connection'];

app.get('/proxy/:encodedUrl', async (req, res) => {
  try {
    const encodedUrl = req.params.encodedUrl;
    const targetUrl = decodeURIComponent(encodedUrl);

    // 安全验证
    if (!isValidUrl(targetUrl)) {
      return res.status(400).send('无效的 URL');
    }

    log(`代理请求: ${targetUrl}`);

    // 添加请求超时和重试逻辑
    const maxRetries = config.maxRetries;
    let retries = 0;

    const makeRequest = async () => {
      try {
        // 透传客户端的 Range 头: 视频分片可能使用字节范围请求(如 HLS/分片 mp4)，
        // 不转发会导致上游返回完整 200 而非 206，破坏播放器的分段逻辑。
        const upstreamHeaders = {
          'User-Agent': config.userAgent,
          'Referer': 'https://movie.douban.com/',
          'Accept': 'image/avif,image/webp,image/*,*/*;q=0.8'
        };
        if (req.headers.range) {
          upstreamHeaders['Range'] = req.headers.range;
        }
        return await axios({
          method: 'get',
          url: targetUrl,
          responseType: 'stream',
          timeout: config.timeout,
          headers: upstreamHeaders,
          // 复用到源站的 keep-alive 连接，省掉每个分片的握手/慢启动开销
          httpAgent,
          httpsAgent
        });
      } catch (error) {
        if (retries < maxRetries) {
          retries++;
          log(`重试请求 (${retries}/${maxRetries}): ${targetUrl}`);
          return makeRequest();
        }
        throw error;
      }
    };

    const response = await makeRequest();

    // 转发响应头（过滤敏感头）
    const headers = { ...response.headers };
    const sensitiveHeaders = (
      process.env.FILTERED_HEADERS || 
      'content-security-policy,cookie,set-cookie,x-frame-options,access-control-allow-origin'
    ).split(',');
    
    sensitiveHeaders.forEach(header => delete headers[header]);
    // 剥离会破坏流式转发的头
    STREAM_UNSAFE_HEADERS.forEach(header => delete headers[header]);

    // —— 若为 m3u8 播放列表：缓冲为文本并改写分片地址，使分片同样走本代理 ——
    const upstreamCt = (response.headers['content-type'] || '').toString().toLowerCase();
    const maybeM3u8 = upstreamCt.includes('mpegurl') || /\.m3u8(\?|#|$)/i.test(targetUrl);
    if (maybeM3u8) {
      const text = await streamToString(response.data);
      if (text.trimStart().startsWith('#EXTM3U')) {
        const base = resolvePublicBase(req, tvboxBase);
        const rewritten = await processM3u8Content(targetUrl, text, base, 0);
        log(`已改写 m3u8 分片地址: ${targetUrl}`);
        res.status(200)
          .set('Content-Type', 'application/vnd.apple.mpegurl; charset=utf-8')
          .set('Cache-Control', `public, max-age=${process.env.M3U8_CACHE_SECONDS || '3600'}`)
          .send(rewritten);
        return;
      }
      // 声称是 m3u8 但内容不是：按普通文本原样返回
      res.status(response.status || 200);
      res.set(headers);
      res.send(text);
      return;
    }

    // —— 其余（图片 / ts 分片 / mp4 等二进制）：流式转发 ——
    // 透传上游状态码（如字节范围请求的 206），否则会被固定成 200 破坏分段语义
    res.status(response.status || 200);
    res.set(headers);

    // 管道传输响应流
    response.data.pipe(res);

    // 客户端提前断开（切集/关页/拖动进度条）时销毁上游流，避免半读的连接卡在
    // keep-alive 池里泄漏；正常读完时 socket 会自动归还连接池复用。
    res.on('close', () => {
      if (!res.writableFinished && response.data && !response.data.destroyed) {
        response.data.destroy();
      }
    });
  } catch (error) {
    console.error('代理请求错误:', error.message);
    if (error.response) {
      res.status(error.response.status || 500);
      error.response.data.pipe(res);
    } else {
      res.status(500).send(`请求失败: ${error.message}`);
    }
  }
});

// ===== TVBox 支持路由 =====

// 自动生成 TVBox 配置：把所有采集源映射为指向本机 /tvbox/:key 的 type-1 源。
// TVBox 里只需填这一个地址：http://你的域名/tvbox/config
app.get('/tvbox/config', (req, res) => {
  const base = resolvePublicBase(req, tvboxBase);
  res.type('application/json').send(JSON.stringify(buildTvboxConfig(base), null, 2));
});

// 采集源透传：代替 TVBox 设备请求上游 CMS，返回苹果CMS格式 JSON，
// 并把 vod_play_url 里的 m3u8 直链改写为走本机 /proxy/（解决防盗链 + 加速）。
// 透传原始 query（ac/t/pg/wd/ids/h...），保持每个源自身的分类与详情语义。
app.get('/tvbox/:key', async (req, res) => {
  const site = TVBOX_SITES.find((s) => s.key === req.params.key);
  if (!site) {
    return res.status(404).json({ code: 0, msg: 'unknown source', list: [] });
  }

  const base = resolvePublicBase(req, tvboxBase);
  const qs = new URLSearchParams(req.query).toString();
  const upstream = qs ? `${site.api}${site.api.includes('?') ? '&' : '?'}${qs}` : site.api;

  try {
    const r = await axios({
      method: 'get',
      url: upstream,
      responseType: 'text',
      timeout: config.timeout,
      headers: { 'User-Agent': config.userAgent, 'Accept': 'application/json' },
      httpAgent,
      httpsAgent,
    });

    let data;
    try {
      data = JSON.parse(r.data);
    } catch {
      // 上游返回非 JSON（可能被防盗链拦截或返回 HTML）
      return res.status(502).json({ code: 0, msg: 'upstream not json', list: [] });
    }

    if (data && Array.isArray(data.list)) {
      for (const v of data.list) {
        if (v.vod_play_url) v.vod_play_url = rewritePlayUrl(v.vod_play_url, base);
        if (proxyPic && v.vod_pic && /^https?:\/\//i.test(v.vod_pic)) v.vod_pic = toProxyUrl(base, v.vod_pic);
      }
    }

    res.type('application/json').send(JSON.stringify(data));
  } catch (e) {
    const status = e.response && e.response.status ? e.response.status : 502;
    console.error(`[TVBox透传] ${site.key} 请求失败: ${e.message}`);
    res.status(status).json({ code: 0, msg: 'upstream error: ' + e.message, list: [] });
  }
});

app.use(express.static(path.join(__dirname), {
  maxAge: config.cacheMaxAge
}));

app.use((err, req, res, next) => {
  console.error('服务器错误:', err);
  res.status(500).send('服务器内部错误');
});

app.use((req, res) => {
  res.status(404).send('页面未找到');
});

// 启动服务器
app.listen(config.port, () => {
  console.log(`服务器运行在 http://localhost:${config.port}`);
  if (config.password !== '') {
    console.log('登录密码已设置');
  }
  if (config.debug) {
    console.log('调试模式已启用');
    console.log('配置:', { ...config, password: config.password ? '******' : '' });
  }
});

