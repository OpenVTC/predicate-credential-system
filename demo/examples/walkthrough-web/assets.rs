//! The page, embedded in the binary: the server serves exactly these paths and nothing else.

pub struct Asset {
    /// The URL path.
    pub path: &'static str,
    /// The file under `demo/web/`, for `--assets` (development).
    pub file: &'static str,
    pub mime: &'static str,
    pub bytes: &'static [u8],
}

macro_rules! asset {
    ($path:literal, $file:literal, $mime:literal) => {
        Asset {
            path: $path,
            file: $file,
            mime: $mime,
            bytes: include_bytes!(concat!("../../web/", $file)),
        }
    };
}

macro_rules! font {
    ($name:literal) => {
        Asset {
            path: concat!("/static/katex/fonts/", $name, ".woff2"),
            file: concat!("vendor/katex/fonts/", $name, ".woff2"),
            mime: "font/woff2",
            bytes: include_bytes!(concat!("../../web/vendor/katex/fonts/", $name, ".woff2")),
        }
    };
}

pub static ASSETS: &[Asset] = &[
    asset!("/", "index.html", "text/html; charset=utf-8"),
    asset!("/static/app.js", "app.js", "text/javascript; charset=utf-8"),
    asset!("/static/style.css", "style.css", "text/css; charset=utf-8"),
    asset!(
        "/static/katex/katex.min.js",
        "vendor/katex/katex.min.js",
        "text/javascript; charset=utf-8"
    ),
    asset!(
        "/static/katex/katex.min.css",
        "vendor/katex/katex.min.css",
        "text/css; charset=utf-8"
    ),
    font!("KaTeX_AMS-Regular"),
    font!("KaTeX_Caligraphic-Bold"),
    font!("KaTeX_Caligraphic-Regular"),
    font!("KaTeX_Fraktur-Bold"),
    font!("KaTeX_Fraktur-Regular"),
    font!("KaTeX_Main-Bold"),
    font!("KaTeX_Main-BoldItalic"),
    font!("KaTeX_Main-Italic"),
    font!("KaTeX_Main-Regular"),
    font!("KaTeX_Math-BoldItalic"),
    font!("KaTeX_Math-Italic"),
    font!("KaTeX_SansSerif-Bold"),
    font!("KaTeX_SansSerif-Italic"),
    font!("KaTeX_SansSerif-Regular"),
    font!("KaTeX_Script-Regular"),
    font!("KaTeX_Size1-Regular"),
    font!("KaTeX_Size2-Regular"),
    font!("KaTeX_Size3-Regular"),
    font!("KaTeX_Size4-Regular"),
    font!("KaTeX_Typewriter-Regular"),
];

pub fn find(path: &str) -> Option<&'static Asset> {
    let path = if path == "/index.html" { "/" } else { path };
    ASSETS.iter().find(|a| a.path == path)
}
