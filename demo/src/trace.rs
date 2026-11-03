//! Call tracing for the web walkthrough (`examples/walkthrough-web`). DEMO HOOK.
//!
//! When a recorder is installed on the current thread ([`record`]), the engines report every
//! protocol call they make: who made it, the code path, what it runs in the scheme's terms, how
//! long it took, and whether it failed. Without a recorder each wrapper is a plain call: the
//! tests and the terminal walkthrough behave exactly as before, and no wrapper touches an RNG.

use std::{cell::RefCell, fmt::Display, time::Instant};

/// One recorded call.
#[derive(Debug, Clone, serde::Serialize)]
pub struct Span {
    /// Nesting depth: 0 for a call made by the driver, 1 for a call made inside it, ...
    pub depth: usize,
    /// Who made the call: a member name, an applicant's join DID, or `VTC`.
    pub actor: String,
    /// The code path, e.g. `PCS::root_request`.
    pub call: &'static str,
    /// What the call runs, in the scheme's terms.
    pub runs: &'static str,
    /// Wall-clock time, in nanoseconds.
    pub nanos: u64,
    /// The error the call returned, or `rejected` for a verifier that returned `false`.
    pub error: Option<String>,
    /// What the call decided, when that is not visible from its name (e.g. a spend outcome).
    pub note: Option<String>,
}

#[derive(Default)]
struct Recorder {
    depth: usize,
    spans: Vec<Span>,
}

thread_local! {
    static RECORDER: RefCell<Option<Recorder>> = const { RefCell::new(None) };
}

/// Run `f` with a recorder installed on this thread and return what it recorded. Nested calls
/// of `record` see an empty recorder and restore the outer one afterwards.
pub fn record<T>(f: impl FnOnce() -> T) -> (T, Vec<Span>) {
    let outer = RECORDER.with(|r| r.borrow_mut().replace(Recorder::default()));
    let out = f();
    let rec = RECORDER.with(|r| std::mem::replace(&mut *r.borrow_mut(), outer));
    (out, rec.map(|r| r.spans).unwrap_or_default())
}

fn open(actor: &str, call: &'static str, runs: &'static str) -> Option<usize> {
    RECORDER.with(|r| {
        r.borrow_mut().as_mut().map(|rec| {
            rec.spans.push(Span {
                depth: rec.depth,
                actor: actor.to_string(),
                call,
                runs,
                nanos: 0,
                error: None,
                note: None,
            });
            rec.depth += 1;
            rec.spans.len() - 1
        })
    })
}

fn close(index: usize, nanos: u64, error: Option<String>) {
    RECORDER.with(|r| {
        if let Some(rec) = r.borrow_mut().as_mut() {
            rec.depth = rec.depth.saturating_sub(1);
            if let Some(span) = rec.spans.get_mut(index) {
                span.nanos = nanos;
                span.error = error;
            }
        }
    });
}

fn timed<T>(
    index: Option<usize>,
    f: impl FnOnce() -> T,
    error: impl Fn(&T) -> Option<String>,
) -> T {
    let Some(index) = index else {
        return f();
    };
    let start = Instant::now();
    let out = f();
    let nanos = u64::try_from(start.elapsed().as_nanos()).unwrap_or(u64::MAX);
    close(index, nanos, error(&out));
    out
}

/// A call that returns a `Result`: an `Err` is recorded with its message.
pub fn span<T, E: Display>(
    actor: &str,
    call: &'static str,
    runs: &'static str,
    f: impl FnOnce() -> Result<T, E>,
) -> Result<T, E> {
    timed(open(actor, call, runs), f, |r| {
        r.as_ref().err().map(ToString::to_string)
    })
}

/// A verifier that returns `bool`: `false` is recorded as `rejected`.
pub fn span_bool(
    actor: &str,
    call: &'static str,
    runs: &'static str,
    f: impl FnOnce() -> bool,
) -> bool {
    timed(open(actor, call, runs), f, |ok| {
        (!ok).then(|| "rejected".to_string())
    })
}

/// A call that cannot fail.
pub fn span_any<T>(
    actor: &str,
    call: &'static str,
    runs: &'static str,
    f: impl FnOnce() -> T,
) -> T {
    timed(open(actor, call, runs), f, |_| None)
}

/// Attach a note to the most recently opened span, e.g. the outcome of a spent-set lookup.
pub fn note(text: impl Into<String>) {
    RECORDER.with(|r| {
        if let Some(span) = r.borrow_mut().as_mut().and_then(|rec| rec.spans.last_mut()) {
            span.note = Some(text.into());
        }
    });
}
