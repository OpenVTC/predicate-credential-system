//! A small HTTP/1.1 server on the standard library: one thread per connection, every response
//! closes the connection. Local use only.
//!
//! Security, as for the cardano-pop demo UI: it listens on 127.0.0.1; it refuses requests whose
//! `Host` is not `127.0.0.1:<port>` or `localhost:<port>` (DNS rebinding); every POST must carry
//! `X-PCS-Demo: 1` and `Content-Type: application/json`, and an `Origin`, if present, must be
//! the page's own (no CORS headers are sent); pages get a Content-Security-Policy that allows
//! scripts, styles and fonts from the server only; static files are served from a fixed list.

use std::{
    collections::HashMap,
    io::{Read, Write},
    net::{TcpListener, TcpStream},
    path::PathBuf,
    sync::{Arc, Mutex},
    time::{Duration, Instant},
};

use serde_json::{Value as J, json};

use crate::{assets, lab, model::Run, scenario};

pub struct App {
    pub port: u16,
    pub default_seed: u64,
    /// Serve the page from this directory instead of the embedded copy (development).
    pub assets_dir: Option<PathBuf>,
    /// The last runs, by seed.
    cache: Mutex<Vec<(u64, Arc<Vec<u8>>)>>,
}

impl App {
    pub fn new(port: u16, default_seed: u64, assets_dir: Option<PathBuf>) -> Self {
        Self {
            port,
            default_seed,
            assets_dir,
            cache: Mutex::new(Vec::new()),
        }
    }

    /// The run for `seed` as JSON, computed on first use.
    pub fn run_json(&self, seed: u64) -> Result<Arc<Vec<u8>>, String> {
        if let Some((_, body)) = self
            .cache
            .lock()
            .map_err(|e| e.to_string())?
            .iter()
            .find(|(s, _)| *s == seed)
        {
            return Ok(Arc::clone(body));
        }
        let start = Instant::now();
        let run = scenario::full(seed).map_err(|e| e.to_string())?;
        let ms = start.elapsed().as_secs_f64() * 1000.0;
        let body =
            Arc::new(serde_json::to_vec(&run_document(&run, seed, ms)).map_err(|e| e.to_string())?);
        let mut cache = self.cache.lock().map_err(|e| e.to_string())?;
        cache.retain(|(s, _)| *s != seed);
        cache.push((seed, Arc::clone(&body)));
        if cache.len() > 6 {
            cache.remove(0);
        }
        Ok(body)
    }
}

fn run_document(run: &Run, seed: u64, ms: f64) -> J {
    json!({
        "version": 1,
        "meta": {
            "seed": seed,
            "defaultSeed": scenario::DEFAULT_SEED,
            "profile": if cfg!(debug_assertions) { "debug" } else { "release" },
            "ms": ms,
            "community": scenario::COMMUNITY,
            "period": scenario::PERIOD,
            "suite": "ps-ddh-bls12381",
        },
        "phases": scenario::PHASES,
        "actors": scenario::actors(),
        "values": run.values(),
        "stages": run.stages,
        "lab": lab::catalog(),
    })
}

pub fn serve(listener: TcpListener, app: Arc<App>) {
    for stream in listener.incoming() {
        let Ok(stream) = stream else { continue };
        let app = Arc::clone(&app);
        std::thread::spawn(move || {
            let _ = handle(stream, &app);
        });
    }
}

struct Request {
    method: String,
    path: String,
    query: HashMap<String, String>,
    headers: HashMap<String, String>,
    body: Vec<u8>,
}

const MAX_HEAD: usize = 16 * 1024;
const MAX_BODY: usize = 64 * 1024;

fn read_request(stream: &mut TcpStream) -> Result<Request, String> {
    let mut buf = Vec::new();
    let mut chunk = [0u8; 4096];
    let head_end = loop {
        let n = stream.read(&mut chunk).map_err(|e| e.to_string())?;
        if n == 0 {
            return Err("connection closed".into());
        }
        buf.extend_from_slice(&chunk[..n]);
        if let Some(pos) = buf.windows(4).position(|w| w == b"\r\n\r\n") {
            break pos;
        }
        if buf.len() > MAX_HEAD {
            return Err("header too large".into());
        }
    };
    let head = std::str::from_utf8(&buf[..head_end]).map_err(|_| "header is not UTF-8")?;
    let mut lines = head.split("\r\n");
    let mut first = lines.next().unwrap_or_default().split(' ');
    let method = first.next().unwrap_or_default().to_string();
    let target = first.next().unwrap_or_default().to_string();
    let mut headers = HashMap::new();
    for l in lines {
        if let Some((k, v)) = l.split_once(':') {
            headers.insert(k.trim().to_ascii_lowercase(), v.trim().to_string());
        }
    }
    let length: usize = headers
        .get("content-length")
        .map(|v| v.parse().map_err(|_| "bad content-length"))
        .transpose()?
        .unwrap_or(0);
    if length > MAX_BODY {
        return Err("body too large".into());
    }
    let mut body = buf[head_end + 4..].to_vec();
    while body.len() < length {
        let n = stream.read(&mut chunk).map_err(|e| e.to_string())?;
        if n == 0 {
            break;
        }
        body.extend_from_slice(&chunk[..n]);
    }
    body.truncate(length);
    let (path, q) = target.split_once('?').unwrap_or((&target, ""));
    let query = q
        .split('&')
        .filter_map(|kv| kv.split_once('='))
        .map(|(k, v)| (k.to_string(), v.to_string()))
        .collect();
    Ok(Request {
        method,
        path: path.to_string(),
        query,
        headers,
        body,
    })
}

const CSP: &str = "default-src 'none'; script-src 'self'; style-src 'self'; font-src 'self'; \
                   img-src 'self' data:; connect-src 'self'; base-uri 'none'; form-action 'none'; \
                   frame-ancestors 'none'";

fn respond(
    stream: &mut TcpStream,
    status: u16,
    mime: &str,
    body: &[u8],
    cache: &str,
) -> std::io::Result<()> {
    let reason = match status {
        200 => "OK",
        400 => "Bad Request",
        403 => "Forbidden",
        404 => "Not Found",
        405 => "Method Not Allowed",
        _ => "Internal Server Error",
    };
    let head = format!(
        "HTTP/1.1 {status} {reason}\r\nContent-Type: {mime}\r\nContent-Length: {}\r\n\
         Cache-Control: {cache}\r\nX-Content-Type-Options: nosniff\r\nReferrer-Policy: no-referrer\r\n\
         X-Frame-Options: DENY\r\nCross-Origin-Opener-Policy: same-origin\r\n\
         Cross-Origin-Resource-Policy: same-origin\r\nContent-Security-Policy: {CSP}\r\n\
         Connection: close\r\n\r\n",
        body.len()
    );
    stream.write_all(head.as_bytes())?;
    stream.write_all(body)?;
    stream.flush()
}

fn error(stream: &mut TcpStream, status: u16, code: &str, message: &str) -> std::io::Result<()> {
    let body = json!({ "error": message, "code": code }).to_string();
    respond(
        stream,
        status,
        "application/json",
        body.as_bytes(),
        "no-store",
    )
}

fn handle(mut stream: TcpStream, app: &App) -> std::io::Result<()> {
    stream.set_read_timeout(Some(Duration::from_secs(10)))?;
    stream.set_write_timeout(Some(Duration::from_secs(30)))?;
    let req = match read_request(&mut stream) {
        Ok(r) => r,
        Err(e) => return error(&mut stream, 400, "bad-request", &e),
    };
    // DNS rebinding: only our own host names.
    let host = req
        .headers
        .get("host")
        .map(|h| h.to_ascii_lowercase())
        .unwrap_or_default();
    let ours = [
        format!("127.0.0.1:{}", app.port),
        format!("localhost:{}", app.port),
    ];
    if !ours.contains(&host) {
        return error(&mut stream, 403, "host", "unexpected Host header");
    }
    match (req.method.as_str(), req.path.as_str()) {
        ("GET", "/api/run") => {
            let seed = match req.query.get("seed") {
                None => app.default_seed,
                Some(s) => match s.parse::<u64>() {
                    Ok(v) => v,
                    Err(_) => {
                        return error(&mut stream, 400, "seed", "seed must be an unsigned integer");
                    }
                },
            };
            match app.run_json(seed) {
                Ok(body) => respond(&mut stream, 200, "application/json", &body, "no-store"),
                Err(e) => error(&mut stream, 500, "run", &e),
            }
        }
        ("POST", path) if path.starts_with("/api/lab/") => {
            if req.headers.get("x-pcs-demo").map(String::as_str) != Some("1") {
                return error(&mut stream, 403, "csrf", "missing the X-PCS-Demo header");
            }
            if !req
                .headers
                .get("content-type")
                .is_some_and(|c| c.starts_with("application/json"))
            {
                return error(
                    &mut stream,
                    403,
                    "csrf",
                    "POST bodies must be application/json",
                );
            }
            if let Some(origin) = req.headers.get("origin")
                && !ours.iter().any(|h| *origin == format!("http://{h}"))
            {
                return error(&mut stream, 403, "origin", "foreign Origin");
            }
            let id = &path["/api/lab/".len()..];
            if !lab::LAB.iter().any(|i| i.id == id) {
                return error(&mut stream, 404, "unknown", "no such experiment");
            }
            let body: J = serde_json::from_slice(&req.body).unwrap_or(J::Null);
            let seed = body
                .get("seed")
                .and_then(J::as_u64)
                .unwrap_or(app.default_seed);
            let nonce = body.get("nonce").and_then(J::as_u64).unwrap_or(0);
            let param = body.get("param").and_then(J::as_str);
            if let Some(p) = param
                && !lab::TAMPER_FIELDS.iter().any(|(v, _)| *v == p)
            {
                return error(&mut stream, 400, "param", "unknown parameter");
            }
            match lab::run(id, seed, param, nonce) {
                Ok(out) => respond(
                    &mut stream,
                    200,
                    "application/json",
                    out.to_string().as_bytes(),
                    "no-store",
                ),
                Err(e) => error(&mut stream, 500, "lab", &e),
            }
        }
        ("GET", path) => match assets::find(path) {
            Some(a) => {
                let bytes = match &app.assets_dir {
                    Some(dir) => match std::fs::read(dir.join(a.file)) {
                        Ok(b) => std::borrow::Cow::Owned(b),
                        Err(e) => return error(&mut stream, 500, "asset", &e.to_string()),
                    },
                    None => std::borrow::Cow::Borrowed(a.bytes),
                };
                let cache = if a.file.starts_with("vendor/") {
                    "max-age=86400"
                } else {
                    "no-cache"
                };
                respond(&mut stream, 200, a.mime, &bytes, cache)
            }
            None => error(&mut stream, 404, "not-found", "not found"),
        },
        _ => error(&mut stream, 405, "method", "method not allowed"),
    }
}
