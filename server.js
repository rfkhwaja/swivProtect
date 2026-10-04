import http from 'node:http';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { fileURLToPath } from 'node:url';
import { DatabaseSync } from 'node:sqlite';
import { RECOVERY } from './recovery.js';
import { createGoogleVerifier, GoogleAuthError, GoogleUnavailableError } from './googleAuth.js';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const DATA = process.env.SWIVEL_DATA_DIR || path.join(__dirname, 'data');
const PORT = process.env.PORT || 3000;

// Gmail add-on sign-in (off unless GOOGLE_AUDIENCE is set). The value is the OAuth client ID(s) the add-on's Google sign-in token is
// issued to; several can be given, separated by commas. GOOGLE_JWKS_URL and LINK_CODE_TTL_SECONDS exist for tests.
const google = createGoogleVerifier({
  audiences: (process.env.GOOGLE_AUDIENCE || '').split(',').map(x => x.trim()).filter(Boolean),
  jwksUrl: process.env.GOOGLE_JWKS_URL || undefined,
});
const LINK_CODE_TTL_MS = (Number(process.env.LINK_CODE_TTL_SECONDS) || 600) * 1000;

// ---- abuse protection ----
// Limits are counted in memory (they reset when the server restarts). Change one with RATE_LIMITS='{"signupIp":5}', switch them all off with
// RATE_LIMITS=off (development only). Behind a proxy or tunnel that sets X-Forwarded-For, start with TRUST_PROXY=1 so people are told apart
// by their real address; without it everyone behind the proxy looks like one address and shares one allowance.
const MIN = 60_000, HOUR = 3_600_000;
const MAX_BODY_BYTES = Number(process.env.MAX_BODY_BYTES) || 100_000;
const TRUST_PROXY = process.env.TRUST_PROXY === '1';
const RATE_OFF = process.env.RATE_LIMITS === 'off';
const LIMITS = {                                          // name: [most requests, per window]
  signupIp: [60, HOUR], signupAll: [600, HOUR],           // new accounts. The overall cap also bounds how fast the user table can grow.
  loginIp: [100, 10 * MIN], loginFail: [10, 15 * MIN],    // loginFail counts wrong passwords per account, then locks it for the window
  analyzeUser: [60, MIN], analyzeIp: [300, MIN],          // scam checks
  reportUser: [30, HOUR], linkCodeUser: [10, HOUR],
  readUser: [120, MIN], readIp: [1200, MIN],              // everything else. The app itself uses about 15 requests a minute.
};
if (!RATE_OFF && process.env.RATE_LIMITS) {
  try { for (const [k, v] of Object.entries(JSON.parse(process.env.RATE_LIMITS))) if (LIMITS[k]) LIMITS[k] = [Number(v), LIMITS[k][1]]; }
  catch { console.warn('RATE_LIMITS is not valid JSON, so it was ignored.'); }
}
const counters = new Map();                               // "limit name|who" -> { count, resetAt }
function sweepCounters() {
  const now = Date.now();
  for (const [k, c] of counters) if (c.resetAt <= now) counters.delete(k);
  while (counters.size > 50_000) counters.delete(counters.keys().next().value);   // the limiter must never use unbounded memory itself
}
setInterval(sweepCounters, MIN).unref();
/** Count one request against a limit; refuse with 429 (and how long to wait) once the allowance is used up. */
function take(name, who) {
  if (RATE_OFF) return;
  const [limit, windowMs] = LIMITS[name], key = `${name}|${who}`, now = Date.now();
  let c = counters.get(key);
  if (!c || c.resetAt <= now) { if (counters.size > 100_000) sweepCounters(); c = { count: 0, resetAt: now + windowMs }; counters.set(key, c); }
  if (++c.count > limit) throw new HttpError(429, 'Too many requests. Please wait a little and try again.', 'rate_limited', Math.max(1, Math.ceil((c.resetAt - now) / 1000)));
}
const clientIp = req => (TRUST_PROXY ? String(req.headers['x-forwarded-for'] || '').split(',')[0].trim() : '') || req.socket.remoteAddress || 'unknown';
// wrong passwords are counted per account name; after loginFail wrong tries the account refuses logins for a while
function loginLocked(email) {
  if (RATE_OFF) return;
  const c = counters.get(`loginFail|${email}`);
  if (c && c.resetAt > Date.now() && c.count >= LIMITS.loginFail[0]) throw new HttpError(429, 'Too many wrong passwords. Please wait a few minutes and try again.', 'locked', Math.ceil((c.resetAt - Date.now()) / 1000));
}
function loginFailed(email) {
  if (RATE_OFF) return;
  const key = `loginFail|${email}`, now = Date.now(), c = counters.get(key);
  if (!c || c.resetAt <= now) counters.set(key, { count: 1, resetAt: now + LIMITS.loginFail[1] }); else c.count++;
}
const loginOk = email => counters.delete(`loginFail|${email}`);

// Rules: keep in sync with data/live_db.py (the tested reference implementation).
const ALERT_THRESHOLD = 5, PAIR_CAP = 15, WINDOW_DAYS = 30;
const STATES = ['AL','AK','AZ','AR','CA','CO','CT','DE','DC','FL','GA','HI','ID','IL','IN','IA','KS','KY','LA','ME','MD','MA','MI','MN','MS','MO','MT','NE','NV','NH','NJ','NM','NY','NC','ND','OH','OK','OR','PA','RI','SC','SD','TN','TX','UT','VT','VA','WA','WV','WI','WY'];
const AGE_GROUPS = ['18-25', '26-40', '41-60', '60+'];
const LANGUAGES = ['English', 'Spanish', 'Chinese', 'Tagalog', 'Vietnamese'];
const DIMS = ['state', 'age_group', 'language'];
const PAIRS = [['state', 'age_group'], ['state', 'language'], ['age_group', 'language']];

// ---- databases: live.db (accounts, reports, alerts) + catalog.db (static scam catalog) ----
const catalogPath = path.join(DATA, 'catalog.db');
if (!fs.existsSync(catalogPath)) { console.error('catalog.db not found. Run: npm run setup'); process.exit(1); }

const dbPath = path.join(DATA, 'live.db');
fs.mkdirSync(path.dirname(dbPath), { recursive: true });
const db = new DatabaseSync(dbPath);

db.exec('PRAGMA foreign_keys = ON');
if (!db.prepare("SELECT 1 FROM sqlite_master WHERE name='users'").get()) db.exec(fs.readFileSync(path.join(DATA, 'live_schema.sql'), 'utf8'));
if (!db.prepare('PRAGMA table_info(users)').all().some(c => c.name === 'google_email')) db.exec('ALTER TABLE users ADD COLUMN google_email TEXT');
db.exec('CREATE UNIQUE INDEX IF NOT EXISTS idx_users_google_email ON users (google_email)');   // one Gmail address per account; NULLs are allowed many times
db.exec(`ATTACH DATABASE '${catalogPath.replace(/'/g, "''")}' AS catalog`);

class HttpError extends Error { constructor(code, msg, reason, retryAfter) { super(msg); this.code = code; this.reason = reason; this.retryAfter = retryAfter; } }
const q = sql => db.prepare(sql);

function purge() {
  const c = `-${WINDOW_DAYS} days`;
  q("DELETE FROM reports WHERE created_at < datetime('now', ?)").run(c);
  q("DELETE FROM alerts WHERE fired_at < datetime('now', ?)").run(c);
  q("DELETE FROM notifications WHERE created_at < datetime('now', ?)").run(c);
}
purge();
setInterval(purge, 3600e3).unref();

// ---- accounts ----
const hash = (pw, salt) => crypto.scryptSync(pw, salt, 32).toString('hex');
const firstOf = n => n.includes(', ') ? n.split(', ').slice(1).join(', ') : n;
function splitName(full) {   // "Alex Morgan" or "Morgan, Alex" -> stored as "Last, First"
  full = full.trim().replace(/\s+/g, ' ');
  if (full.includes(',')) { const [l, f] = full.split(',').map(x => x.trim()); return f ? { first: f, last: l } : { first: l, last: '' }; }
  const parts = full.split(' ');
  return { first: parts[0], last: parts.slice(1).join(' ') };
}
const publicUser = u => ({ userName: u.user_name, firstName: firstOf(u.user_name), email: u.email, token: u.token, memberSince: u.created_at, gmail: u.google_email || null, profile: { state: u.state, ageGroup: u.age_group, language: u.language } });
function cleanProfile(b) {
  if (!STATES.includes(b.state)) throw new HttpError(400, 'Please choose your state.');
  if (!AGE_GROUPS.includes(b.ageGroup)) throw new HttpError(400, 'Please choose your age range.');
  if (!LANGUAGES.includes(b.language)) throw new HttpError(400, 'Please choose your language.');
  return { state: b.state, age_group: b.ageGroup, language: b.language };
}
const bearer = req => (req.headers.authorization || '').replace(/^Bearer /, '').trim();
const looksLikeJwt = t => /^[A-Za-z0-9_-]+\.[A-Za-z0-9_-]+\.[A-Za-z0-9_-]+$/.test(t);

/** Who is calling with a Google sign-in token. Google's signature is checked, so the email can be trusted. */
async function googleIdentity(req) {
  const t = bearer(req);
  if (!t || !looksLikeJwt(t)) throw new HttpError(401, 'Not signed in.');
  if (!google.enabled) throw new HttpError(501, 'Gmail sign-in is not set up on this server.', 'google_disabled');
  try { return await google.verify(t); }
  catch (e) {
    if (e instanceof GoogleAuthError) {
      console.warn(`Google sign-in rejected: ${e.message}${e.detail?.aud ? ` (token audience: ${[].concat(e.detail.aud).join(', ')}; set GOOGLE_AUDIENCE to it if this is your add-on)` : ''}`);
      throw new HttpError(401, 'Google sign-in was not accepted.', 'google_rejected');
    }
    if (e instanceof GoogleUnavailableError) { console.warn(`Google sign-in unavailable: ${e.message}`); throw new HttpError(503, 'Could not reach Google to check your sign-in. Please try again.', 'google_unavailable'); }
    throw e;
  }
}

/** The signed-in person (and counts the request against that person's limit). A Google token is accepted only where allowGoogle is true, so it can never fetch the long-lived key. */
async function userFrom(req, { allowGoogle = false, rate = 'readUser' } = {}) {
  const t = bearer(req);
  let u = t && q('SELECT * FROM users WHERE token = ?').get(t);
  if (!u && allowGoogle && looksLikeJwt(t)) {
    const g = await googleIdentity(req);
    u = q('SELECT * FROM users WHERE google_email = ?').get(g.email);
    if (!u) throw new HttpError(404, 'This Gmail address is not linked to a SwivProtect account yet.', 'not_linked');
  }
  if (!u) throw new HttpError(401, 'Not signed in.');
  take(rate, u.id);
  return u;
}

// One-time codes that link a Gmail address to a SwivProtect account. They live in memory only and expire.
const linkCodes = new Map();   // code -> { userId, expires }
const failedLinks = new Map(); // gmail address -> { count, resetAt }
const CODE_ALPHABET = 'ABCDEFGHJKMNPQRSTUVWXYZ23456789';   // no 0, O, 1, I or L
const cleanCode = s => String(s || '').slice(0, 40).toUpperCase().replace(/[^A-Z0-9]/g, '');
function newLinkCode(userId) {
  for (const [c, v] of linkCodes) if (v.userId === userId || v.expires < Date.now()) linkCodes.delete(c);   // one live code per person
  let code;
  do { code = Array.from({ length: 8 }, () => CODE_ALPHABET[crypto.randomInt(CODE_ALPHABET.length)]).join(''); } while (linkCodes.has(code));
  linkCodes.set(code, { userId, expires: Date.now() + LINK_CODE_TTL_MS });
  return `${code.slice(0, 4)}-${code.slice(4)}`;
}
const tooManyFailures = key => { const f = failedLinks.get(key); return !!f && f.resetAt > Date.now() && f.count >= 5; };
function noteFailure(key) {
  const now = Date.now(), f = failedLinks.get(key);
  if (!f || f.resetAt <= now) failedLinks.set(key, { count: 1, resetAt: now + 10 * 60_000 }); else f.count++;
}

// ---- reports + the alert trigger ----
function flagsFor(scamId, language) {
  const flags = q('SELECT flag FROM catalog.red_flags WHERE scam_id = ? AND language = ? ORDER BY position').all(scamId, language).map(r => r.flag);
  const tpl = q('SELECT template FROM catalog.notification_templates WHERE language = ?').get(language).template;
  return { flags: flags.join(', '), message: tpl.replace('{flags}', flags.join(', ')) };
}

function submitReport(u, scamId, source, outcome) {
  purge();
  if (!q('SELECT 1 FROM catalog.scams WHERE id = ?').get(scamId)) throw new HttpError(400, 'Unknown scam type.');
  if (!['Email', 'SMS'].includes(source)) throw new HttpError(400, 'Choose Email or SMS.');
  if (!['blocked', 'fell_for', 'unsure'].includes(outcome)) outcome = 'unsure';
  if (q('SELECT 1 FROM reports WHERE user_id = ? AND scam_id = ?').get(u.id, scamId)) return { stored: false, reason: 'duplicate', alerts: 0 };
  for (const [a, b] of PAIRS) {
    const n = q(`SELECT COUNT(*) n FROM reports WHERE scam_id = ? AND ${a} = ? AND ${b} = ?`).get(scamId, u[a], u[b]).n;
    if (n >= PAIR_CAP) return { stored: false, reason: 'cap', alerts: 0 };
  }
  q('INSERT INTO reports (user_id, scam_id, source, outcome, state, age_group, language) VALUES (?,?,?,?,?,?,?)')
    .run(u.id, scamId, source, outcome, u.state, u.age_group, u.language);

  let fired = 0;
  for (const dim of DIMS) {
    const val = u[dim];
    const n = q(`SELECT COUNT(DISTINCT user_id) n FROM reports WHERE scam_id = ? AND ${dim} = ?`).get(scamId, val).n;
    if (n < ALERT_THRESHOLD) continue;
    if (q('SELECT 1 FROM alerts WHERE scam_id = ? AND dimension = ? AND value = ?').get(scamId, dim, val)) continue;
    const audience = q(`SELECT id, language FROM users WHERE ${dim} = ? AND id NOT IN (SELECT user_id FROM reports WHERE scam_id = ? AND ${dim} = ?)`).all(val, scamId, val);
    const alertId = q('INSERT INTO alerts (scam_id, dimension, value, flags) VALUES (?,?,?,?)').run(scamId, dim, val, flagsFor(scamId, 'English').flags).lastInsertRowid;
    const msgByLang = {};
    for (const r of audience) {
      if (q('SELECT 1 FROM notifications WHERE user_id = ? AND scam_id = ?').get(r.id, scamId)) continue;   // one alert per scam per person
      msgByLang[r.language] ??= flagsFor(scamId, r.language).message;
      q('INSERT INTO notifications (user_id, alert_id, scam_id, message) VALUES (?,?,?,?)').run(r.id, alertId, scamId, msgByLang[r.language]);
    }
    fired++;
  }
  if (fired) q('UPDATE reports SET started_alert = 1 WHERE user_id = ? AND scam_id = ?').run(u.id, scamId);
  return { stored: true, reason: null, alerts: fired };
}

// ---- "during attack": scan a message against the catalog's red-flag words ----
const FLAG_ROWS = q('SELECT scam_id, flag FROM catalog.red_flags').all();
const TIPS = {};
for (const t of q('SELECT scam_id, tip FROM catalog.tips ORDER BY scam_id, position').all()) (TIPS[t.scam_id] ??= []).push(t.tip);
const SCAMS = Object.fromEntries(q('SELECT id, name, summary FROM catalog.scams').all().map(s => [s.id, { ...s, tips: TIPS[s.id] || [] }]));
const esc = s => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
// "grandma/grandpa" -> two alternatives; "$" matches any amount; letters at the edges must not sit inside a longer word.
const FLAG_RE = FLAG_ROWS.map(r => {
  const alts = r.flag.split('/').map(a => a.trim()).filter(Boolean).map(a => {
    const body = esc(a).replace(/\\\$/g, '\\$?[\\d,.]*').replace(/\s+/g, '\\s+');
    return (/^[A-Za-z]/.test(a) ? '(?<![A-Za-z])' : '') + body + (/[A-Za-z]$/.test(a) ? '(?![A-Za-z])' : '');
  });
  return { scamId: r.scam_id, flag: r.flag, re: new RegExp(alts.join('|'), 'i') };
});
const PAYMENT_RE = /gift card|tarjeta de regalo|礼品卡|thẻ quà tặng|wire transfer|bitcoin|crypto|cripto|加密|zelle|cash app|prepaid|prepago/i;

function analyze(text) {
  // Count each distinct word found in the message once. The same word (e.g. "USPS") appears in several languages'
  // flag lists and must not be counted once per language.
  const byScam = {};
  for (const f of FLAG_RE) { const m = text.match(f.re); if (m) (byScam[f.scamId] ??= new Set()).add(m[0].toLowerCase()); }
  let [best, found] = Object.entries(byScam).sort((a, b) => b[1].size - a[1].size)[0] || [null, new Set()];
  const hits = [...found];
  let score = hits.length;
  // Payment-method words and links only add weight when other scam words are already present.
  if (score >= 2 && PAYMENT_RE.test(text)) score++;
  if (score >= 2 && /https?:\/\//i.test(text)) score++;
  const level = score >= 3 ? 'high' : score === 2 ? 'medium' : 'low';
  return { level, score, scam: level === 'low' ? null : SCAMS[best], hits: level === 'low' ? [] : hits };
}

const T = {
  English: { high: 'Very likely a scam. Do not respond.', medium: 'This looks suspicious. Be careful.', low: 'Nothing obviously wrong, but stay careful.' },
  Spanish: { high: 'Muy probablemente es una estafa. No responda.', medium: 'Esto parece sospechoso. Tenga cuidado.', low: 'Nada parece raro, pero tenga cuidado.' },
  Chinese: { high: '极有可能是诈骗，请不要回复。', medium: '这条信息看起来可疑，请小心。', low: '看起来没有明显问题，但仍请保持警惕。' },
  Tagalog: { high: 'Malamang scam ito. Huwag sumagot.', medium: 'Mukhang kahina-hinala ito. Mag-ingat.', low: 'Walang halatang mali, pero mag-ingat pa rin.' },
  Vietnamese: { high: 'Rất có thể đây là lừa đảo. Đừng trả lời.', medium: 'Tin nhắn này có vẻ đáng ngờ. Hãy cẩn thận.', low: 'Chưa thấy điều gì bất thường, nhưng hãy luôn cảnh giác.' },
};

// Optional Claude second opinion (set ANTHROPIC_API_KEY)
async function aiExplain(text, scam, language) {
  if (!process.env.ANTHROPIC_API_KEY) return null;
  try {
    const res = await fetch('https://api.anthropic.com/v1/messages', {
      method: 'POST',
      headers: { 'content-type': 'application/json', 'x-api-key': process.env.ANTHROPIC_API_KEY, 'anthropic-version': '2023-06-01' },
      body: JSON.stringify({
        model: process.env.CLAUDE_MODEL || 'claude-haiku-4-5-20251001', max_tokens: 200,
        system: `You help older adults spot scams. Reply in ${language}. In 2 short, plain-language sentences (6th grade reading level), say whether this message looks like a scam and what to do. Never be alarming or condescending.`,
        messages: [{ role: 'user', content: `Pattern matched: ${scam ? scam.name : 'none'}.\n\nMessage:\n${text.slice(0, 4000)}` }],
      }),
    });
    return (await res.json()).content?.[0]?.text || null;
  } catch { return null; }
}

// ---- http ----
const MIME = { '.html': 'text/html', '.js': 'text/javascript', '.css': 'text/css', '.json': 'application/json', '.svg': 'image/svg+xml', '.png': 'image/png', '.webmanifest': 'application/manifest+json' };
const SECURITY = { 'x-content-type-options': 'nosniff', 'referrer-policy': 'no-referrer', 'x-frame-options': 'DENY' };
/** The request body as JSON, refusing anything bigger than MAX_BODY_BYTES instead of holding it in memory. */
const readBody = req => new Promise((resolve, reject) => {
  if (Number(req.headers['content-length']) > MAX_BODY_BYTES) return reject(new HttpError(413, 'That request is too large.', 'too_large'));
  const chunks = []; let size = 0, refused = false;
  req.on('data', c => {
    if (refused) return;
    size += c.length;
    if (size > MAX_BODY_BYTES) { refused = true; req.pause(); return reject(new HttpError(413, 'That request is too large.', 'too_large')); }
    chunks.push(c);
  });
  req.on('end', () => { if (refused) return; try { resolve(JSON.parse(Buffer.concat(chunks).toString('utf8') || '{}')); } catch { resolve({}); } });
  req.on('error', () => resolve({}));
});
// No CORS headers on purpose: the apps are served from this same address, and the Gmail add-on calls from Google's servers, not a browser.
// Leaving cross-site access open would let any web page use its visitors' browsers to flood sign-ups from many addresses.
const send = (res, code, obj, extra = {}) => { res.writeHead(code, { 'content-type': 'application/json', 'cache-control': 'no-store', ...SECURITY, ...extra }); res.end(JSON.stringify(obj)); };

async function route(req, res, url) {
  const p = url.pathname, m = req.method;
  if (p === '/healthz') {   // for uptime checks: answers 200 only if the database responds. Not rate limited; reveals nothing.
    try { q('SELECT 1').get(); } catch { res.writeHead(503, { ...SECURITY, 'cache-control': 'no-store' }); return res.end('database unavailable'); }
    res.writeHead(200, { 'content-type': 'text/plain', 'cache-control': 'no-store', ...SECURITY }); return res.end('ok');
  }
  if (p.startsWith('/api/')) {   // allowances per address, before any work is done
    const ip = clientIp(req);
    if (m === 'POST' && p === '/api/signup') { take('signupIp', ip); take('signupAll', '*'); }
    else if (m === 'POST' && p === '/api/login') take('loginIp', ip);
    else if (m === 'POST' && p === '/api/analyze') take('analyzeIp', ip);
    else take('readIp', ip);
  }

  if (p === '/api/options') return send(res, 200, { states: STATES, ageGroups: AGE_GROUPS, languages: LANGUAGES });
  if (p === '/api/catalog') return send(res, 200, {
    version: q("SELECT value FROM catalog.meta WHERE key='catalog_version'").get().value,
    categories: q('SELECT id, name, summary FROM catalog.categories ORDER BY id').all(),
    scams: q('SELECT id, name, summary, sources, category_id FROM catalog.scams ORDER BY category_id, position').all() });

  if (p === '/api/signup' && m === 'POST') {
    const b = await readBody(req);
    const rawName = String(b.fullName || '');
    if (rawName.trim().length > 80) throw new HttpError(400, 'That name is too long. Please use 80 characters or fewer.');
    const { first, last } = splitName(rawName);
    const email = String(b.email || '').trim().toLowerCase(), pw = String(b.password || '');
    if (email.length > 254) throw new HttpError(400, 'That email address is too long.');
    if (pw.length > 128) throw new HttpError(400, 'That password is too long. Please use 128 characters or fewer.');
    if (!first) throw new HttpError(400, 'Please enter your full name.');
    if (!/^\S+@\S+\.\S+$/.test(email)) throw new HttpError(400, 'Please enter a valid email address.');
    if (pw.length < 8 || !/[A-Za-z]/.test(pw) || !/\d/.test(pw)) throw new HttpError(400, 'Use at least 8 characters, with a letter and a number.');
    const prof = cleanProfile(b);
    if (q('SELECT 1 FROM users WHERE email = ?').get(email)) throw new HttpError(409, 'That email already has an account.');
    const salt = crypto.randomBytes(16).toString('hex'), token = crypto.randomBytes(24).toString('hex');
    q('INSERT INTO users (user_name, email, salt, pw_hash, token, state, age_group, language) VALUES (?,?,?,?,?,?,?,?)')
      .run(last ? `${last}, ${first}` : first, email, salt, hash(b.password, salt), token, prof.state, prof.age_group, prof.language);
    return send(res, 201, publicUser(q('SELECT * FROM users WHERE email = ?').get(email)));
  }
  if (p === '/api/login' && m === 'POST') {
    const b = await readBody(req);
    const email = String(b.email || '').trim().toLowerCase().slice(0, 254), pw = String(b.password || '');
    loginLocked(email);
    const u = q('SELECT * FROM users WHERE email = ?').get(email);
    if (pw.length > 128 || !u || !u.salt || hash(pw, u.salt) !== u.pw_hash) { loginFailed(email); throw new HttpError(401, 'Wrong email or password.'); }
    loginOk(email);
    return send(res, 200, publicUser(u));
  }
  if (p === '/api/me') {
    const u = await userFrom(req);
    if (m === 'PUT') {
      const prof = cleanProfile(await readBody(req));
      q('UPDATE users SET state = ?, age_group = ?, language = ? WHERE id = ?').run(prof.state, prof.age_group, prof.language, u.id);
    }
    return send(res, 200, publicUser(q('SELECT * FROM users WHERE id = ?').get(u.id)));
  }

  // Link a Gmail address to this account: the app shows a code, the Gmail add-on submits it with Google's sign-in token.
  if (p === '/api/link-code' && m === 'POST') {
    const u = await userFrom(req, { rate: 'linkCodeUser' });
    return send(res, 200, { code: newLinkCode(u.id), expiresInSeconds: Math.round(LINK_CODE_TTL_MS / 1000) });
  }
  if (p === '/api/link-gmail' && m === 'POST') {
    const g = await googleIdentity(req), b = await readBody(req);
    if (tooManyFailures(g.email)) throw new HttpError(429, 'Too many tries. Please wait a few minutes and try again.', 'too_many');
    const code = cleanCode(b.code), entry = linkCodes.get(code);
    if (!entry || entry.expires < Date.now()) { noteFailure(g.email); throw new HttpError(400, 'That code is not valid or has expired. Make a new one in the SwivProtect app (Edit profile).', 'bad_code'); }
    if (q('SELECT 1 FROM users WHERE google_email = ? AND id != ?').get(g.email, entry.userId)) throw new HttpError(409, 'That Gmail address is already linked to a different SwivProtect account. Unlink it there first.', 'already_linked');
    q('UPDATE users SET google_email = ? WHERE id = ?').run(g.email, entry.userId);
    linkCodes.delete(code);
    return send(res, 200, { linked: true, email: g.email });
  }
  if (p === '/api/unlink-gmail' && m === 'POST') {
    const u = await userFrom(req);
    q('UPDATE users SET google_email = NULL WHERE id = ?').run(u.id);
    return send(res, 200, { linked: false });
  }

  if (p === '/api/reports' && m === 'POST') {
    const u = await userFrom(req, { rate: 'reportUser' }), b = await readBody(req);
    return send(res, 201, { ...submitReport(u, Number(b.scamId), b.source, b.outcome), recovery: b.outcome === 'fell_for' ? RECOVERY.default : null });
  }
  if (p === '/api/my-reports') {
    const u = await userFrom(req);
    purge();
    return send(res, 200, { reports: q(`SELECT r.id, r.outcome, r.source, r.started_alert, r.created_at, s.name scam FROM reports r JOIN catalog.scams s ON s.id = r.scam_id WHERE r.user_id = ? ORDER BY r.id DESC`).all(u.id) });
  }
  if (p === '/api/notifications') {
    const u = await userFrom(req);
    purge();
    return send(res, 200, { notifications: q(`SELECT n.id, n.message, n.created_at, n.scam_id, s.name scam FROM notifications n JOIN catalog.scams s ON s.id = n.scam_id WHERE n.user_id = ? ORDER BY n.id DESC LIMIT 20`).all(u.id) });
  }
  if (p === '/api/stats') {
    purge();
    return send(res, 200, { reports: q('SELECT COUNT(*) n FROM reports').get().n, blocked: q("SELECT COUNT(*) n FROM reports WHERE outcome = 'blocked'").get().n, alerts: q('SELECT COUNT(*) n FROM alerts').get().n });
  }

  // The "during attack" endpoint: web app, Gmail add-on and SMS automation all call this with the user's key.
  if (p === '/api/analyze' && m === 'POST') {
    const u = await userFrom(req, { allowGoogle: true, rate: 'analyzeUser' }), b = await readBody(req);
    const text = `${b.subject || ''}\n${b.body || ''}`.slice(0, 20_000);   // only the start of a message is scanned; real texts and emails are far shorter
    const r = analyze(text);
    const t = T[u.language] || T.English;
    const community = r.scam ? q(`SELECT COUNT(DISTINCT user_id) n FROM reports WHERE scam_id = ? AND (state = ? OR age_group = ? OR language = ?)`).get(r.scam.id, u.state, u.age_group, u.language).n : 0;
    return send(res, 200, {
      level: r.level, score: r.score, scam: r.scam, hits: r.hits, language: u.language, headline: t[r.level],
      community, ai: r.level === 'low' ? null : await aiExplain(text, r.scam, u.language), recovery: r.level === 'low' ? null : RECOVERY.default });
  }

  // static
  const root = path.join(__dirname, 'public');
  const f = path.join(root, p === '/' ? 'index.html' : p);
  if (!f.startsWith(root) || !fs.existsSync(f) || fs.statSync(f).isDirectory()) { res.writeHead(404, SECURITY); return res.end('Not found'); }
  res.writeHead(200, { 'content-type': MIME[path.extname(f)] || 'application/octet-stream', ...SECURITY });
  fs.createReadStream(f).pipe(res);
}

const server = http.createServer(async (req, res) => {
  if (req.method === 'OPTIONS') return send(res, 405, { error: 'Method not allowed.' }, { allow: 'GET, POST, PUT' });
  try { await route(req, res, new URL(req.url, `http://${req.headers.host}`)); }
  catch (e) {
    if (e instanceof HttpError) {
      if (e.code === 413) res.once('finish', () => req.destroy());   // stop an oversized upload instead of reading it
      return send(res, e.code, { error: e.message, ...(e.reason ? { code: e.reason } : {}) },
        { ...(e.retryAfter ? { 'retry-after': String(e.retryAfter) } : {}), ...(e.code === 413 ? { connection: 'close' } : {}) });
    }
    console.error(e); send(res, 500, { error: 'Server error.' });
  }
});
server.requestTimeout = 30_000;   // a request that takes longer than this to arrive is dropped
server.headersTimeout = 15_000;
// In production behind a proxy, set HOST=127.0.0.1 so the only way in is through the proxy (and TRUST_PROXY=1 cannot be fooled by a direct connection).
const HOST = process.env.HOST || undefined;
server.listen(PORT, HOST, () => console.log(`Swivel running at http://${HOST || 'localhost'}:${PORT}`));
