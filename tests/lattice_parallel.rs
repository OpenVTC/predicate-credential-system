//! The verification of the attestations of a credential request is the same in every rayon pool
//! (feature `parallel`; without it, sequential): the same set `N''`, in the same order, and the
//! same policy value, for a request whose attestations mix valid ones, one for another
//! requester, and a repeated source. `Protocol::evaluate_request` verifies each attestation at
//! most once and none of a tag already counted, in batches no wider than the pool.
//!
//! Run once per build, with and without the feature:
//!
//! ```text
//! cargo test --release --features lattice --test lattice_parallel -- --include-ignored --nocapture
//! cargo test --release --features lattice,parallel --test lattice_parallel -- --include-ignored --nocapture
//! ```
#![cfg(feature = "lattice")]

mod lattice_support;

use std::{fmt::Debug, time::Instant};

use lattice_support::{Bk, Deployment};
use predicate_credential_system::pcreds::Attestation;

/// The value of `f` on the calling thread (the default pool) and, with `parallel`, in rayon pools
/// of 1, 2 and 4 threads, which must all agree; prints the time of each call.
fn in_pools<T: PartialEq + Debug + Send>(what: &str, f: impl Fn() -> T + Sync) -> T {
    let start = Instant::now();
    let value = f();
    print!(
        "  {what}: {:.2} s (default pool)",
        start.elapsed().as_secs_f64()
    );
    #[cfg(feature = "parallel")]
    for threads in [1, 2, 4] {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .build()
            .unwrap();
        let start = Instant::now();
        let other = pool.install(&f);
        print!(
            ", {:.2} s ({threads} threads)",
            start.elapsed().as_secs_f64()
        );
        assert_eq!(other, value, "{what}: {threads} threads");
    }
    println!();
    value
}

/// A request at `k = 2` with five attestations: two valid ones (members 0 and 1), one for
/// another requester (not counted), a second one of member 0 (one source, counted once), and a
/// valid one of member 2 after them. `N''` is the tags of members 0, 1 and 2, in that order.
#[test]
#[cfg_attr(
    debug_assertions,
    ignore = "heavy: five attestations and their verifications in four pools (run in release)"
)]
fn the_verdicts_are_the_same_in_every_pool() {
    let mut d = Deployment::new(b"lattice-parallel/verdicts", 2, 3, 0x9a7_0001);
    let alice = d.register();
    let bob = d.register();
    let m0 = d.attestation(0, &alice);
    let m1 = d.attestation(1, &alice);
    let for_bob = d.attestation(1, &bob);
    let m0_again = d.attestation(0, &alice);
    let m2 = d.attestation(2, &alice);
    let attestations: Vec<Attestation<Bk>> =
        vec![m0.clone(), m1.clone(), for_bob, m0_again, m2.clone()];
    let (message, _state, ssid) = d.request(&alice, attestations);
    let (tags, valid) = in_pools("evaluate_request", || {
        let evaluated = d
            .pcreds
            .evaluate_request(&d.helper, &message, &ssid)
            .unwrap();
        (evaluated.tags().to_vec(), evaluated.is_valid())
    });
    assert_eq!(tags, vec![m0.tag, m1.tag, m2.tag]);
    assert!(valid);
}

/// An invalid attestation at every position of a request at `k = 2` with two valid ones: it is
/// never counted, and the valid ones are, in their order.
#[test]
#[ignore = "heavy: three attestations and nine verifications per pool (run in release with --ignored)"]
fn an_invalid_attestation_is_not_counted_at_any_position() {
    let mut d = Deployment::new(b"lattice-parallel/positions", 2, 2, 0x9a7_0002);
    let alice = d.register();
    let bob = d.register();
    let valid = [d.attestation(0, &alice), d.attestation(1, &alice)];
    let invalid = d.attestation(0, &bob);
    for position in 0..3 {
        let mut attestations = valid.to_vec();
        attestations.insert(position, invalid.clone());
        let (message, _state, ssid) = d.request(&alice, attestations);
        let tags = in_pools(&format!("invalid at {position}"), || {
            d.pcreds
                .evaluate_request(&d.helper, &message, &ssid)
                .unwrap()
                .tags()
                .to_vec()
        });
        assert_eq!(tags, vec![valid[0].tag.clone(), valid[1].tag.clone()]);
    }
}
