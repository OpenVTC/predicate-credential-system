//! The walkthrough of hidden-vetter admission as a local web page, for an audience of
//! cryptographers.
//!
//!     cargo run -p pcs-vetting-prototype --release --example walkthrough-web
//!
//! It serves http://127.0.0.1:8787/ and opens it in the browser. The page shows the flow of
//! `examples/walkthrough.rs` stage by stage: every protocol step as a figure with one column per
//! party, the values of a live seeded run (with the default seed, the same values the terminal
//! walkthrough prints), every equation recomputed, the calls each stage made with their timings,
//! and an attack lab that runs experiments against the same state on request.
//!
//! Flags: `--port N` (8787), `--seed N` (7, the terminal walkthrough's seed), `--no-open`, and
//! `--assets DIR`, which serves the page from `DIR` (normally `demo/web`) instead of the copy
//! embedded in the binary, so that the page can be edited without rebuilding.
//!
//! The page needs no network: KaTeX and its fonts are bundled. The server listens on 127.0.0.1
//! only; see `server.rs` for the checks it makes.

mod assets;
mod lab;
mod model;
mod scenario;
mod server;

use std::{
    net::TcpListener,
    path::PathBuf,
    process::{Command, Stdio, exit},
    sync::Arc,
    time::Instant,
};

const USAGE: &str = "usage: walkthrough-web [--port N] [--seed N] [--no-open] [--assets DIR]";

fn main() {
    let mut port: u16 = 8787;
    let mut seed = scenario::DEFAULT_SEED;
    let mut open = true;
    let mut assets_dir = None;
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--port" => port = value(args.next(), "--port"),
            "--seed" => seed = value(args.next(), "--seed"),
            "--no-open" => open = false,
            "--assets" => {
                assets_dir = Some(PathBuf::from(value::<String>(args.next(), "--assets")))
            }
            "-h" | "--help" => {
                println!("{USAGE}");
                return;
            }
            other => {
                eprintln!("unknown argument {other:?}\n{USAGE}");
                exit(2);
            }
        }
    }
    if cfg!(debug_assertions) {
        eprintln!(
            "note: this is a debug build. Pairings are slow and the timings on the page are not \
             representative; add --release."
        );
    }
    let listener = match TcpListener::bind(("127.0.0.1", port)) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("cannot listen on 127.0.0.1:{port}: {e}. Try --port with another port.");
            exit(1);
        }
    };
    let app = Arc::new(server::App::new(port, seed, assets_dir));
    // Compute the default run now: a failure shows here, and the first page load is instant.
    let start = Instant::now();
    if let Err(e) = app.run_json(seed) {
        eprintln!("the walkthrough failed: {e}");
        exit(1);
    }
    let url = format!("http://127.0.0.1:{port}/");
    let same = if seed == scenario::DEFAULT_SEED {
        ", the same values as --example walkthrough"
    } else {
        ""
    };
    println!(
        "Hidden-vetter walkthrough: seed {seed}{same}, computed in {:.0} ms.\n\n    {url}\n\nCtrl-C stops the server.",
        start.elapsed().as_secs_f64() * 1000.0
    );
    if open {
        open_browser(&url);
    }
    server::serve(listener, app);
}

fn value<T: std::str::FromStr>(v: Option<String>, flag: &str) -> T {
    match v.as_deref().map(str::parse) {
        Some(Ok(v)) => v,
        _ => {
            eprintln!("{flag} needs a value\n{USAGE}");
            exit(2);
        }
    }
}

fn open_browser(url: &str) {
    let (cmd, args): (&str, Vec<&str>) = if cfg!(target_os = "macos") {
        ("open", vec![url])
    } else if cfg!(windows) {
        ("cmd", vec!["/C", "start", "", url])
    } else {
        ("xdg-open", vec![url])
    };
    let _ = Command::new(cmd)
        .args(args)
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn();
}
