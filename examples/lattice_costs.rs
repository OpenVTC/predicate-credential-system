//! A cost probe of the lattice instantiation: runs the protocol up to stage `S` with the seed `N`
//! and exits, so that the retired instructions of consecutive stages, one process each, differ
//! by one operation. Retired instructions hardly depend on the load of the machine, unlike wall
//! clock. The stages:
//!
//! | stage | adds |
//! |---|---|
//! | 0 | `Setup`, the helper's key, a root user |
//! | 1 | the root user's `request_credential` (`π_iss`) |
//! | 2 | its `evaluate_request` (the check of `π_iss`, no attestations) |
//! | 3 | `respond`, `unblind`, a newcomer and its `request_attestation` (`π_id`) |
//! | 4 | `receive_attestation_request` (the check of `π_id`) |
//! | 5 | `attest` (`π_att`) |
//! | 6 | `check_attestation` |
//! | 7 | `prove` (`π_prove`) |
//! | 8 | `verify` |
//!
//! ```sh
//! cargo build --release --features lattice --example lattice_costs
//! for s in 0 1 2 3 4 5 6 7 8; do
//!   /usr/bin/time -l target/release/examples/lattice_costs $s 1 2>&1 | grep 'instructions retired'
//! done
//! ```
//!
//! `/usr/bin/time -l` is macOS's. It measures the default, extractable build, and with
//! `--features lattice-plain` the plain one. One thread: build it without `parallel`.
use predicate_credential_system::{
    lattice::STRAIGHT_LINE,
    pcreds::{Decision, Policy, Reply, lattice::LatticeProtocol},
};
use rand::{SeedableRng, rngs::StdRng};

fn main() -> Result<(), predicate_credential_system::Error> {
    let mut args = std::env::args().skip(1);
    let usage = "usage: lattice_costs STAGE SEED";
    let stop: u32 = args.next().and_then(|a| a.parse().ok()).expect(usage);
    let seed: u64 = args.next().and_then(|a| a.parse().ok()).expect(usage);
    let mut rng = StdRng::seed_from_u64(seed);
    let done = |stage: u32| {
        if stage == stop {
            println!("stage {stop}, seed {seed}, straight-line extractable: {STRAIGHT_LINE}");
            std::process::exit(0);
        }
    };
    let pcreds = LatticeProtocol::setup(b"pcs-costs")?;
    let mut helper = pcreds.helper_keygen(Policy::threshold(1)?, &mut rng);
    let hvk = pcreds.helper_key(helper.key().vk())?;
    let root = pcreds.register(&hvk, &mut rng)?;
    done(0);
    let (message, state) = pcreds.request_credential(&hvk, &root, Vec::new(), b"root", &mut rng)?;
    done(1);
    // a root request carries no attestations, so it is not valid under the policy: the helper
    // admits it by its decision
    let evaluated = pcreds.evaluate_request(&helper, &message, b"root")?;
    assert!(!evaluated.is_valid());
    done(2);
    let Reply::PreCredential(pre) =
        pcreds.respond(&mut helper, evaluated, Decision::Root, &mut rng)?
    else {
        panic!("a root admission issues")
    };
    let cred = pcreds.unblind(&hvk, &root, &pre, state)?;
    let newcomer = pcreds.register(&hvk, &mut rng)?;
    let request = pcreds.request_attestation(&hvk, &newcomer, b"att", b"contact", &mut rng)?;
    done(3);
    let pending = pcreds.receive_attestation_request(&hvk, &request, b"att", b"contact")?;
    done(4);
    let attestation = pcreds.attest(&hvk, &root, &cred, pending, &mut rng)?;
    done(5);
    pcreds.check_attestation(&hvk, newcomer.id(), &attestation)?;
    done(6);
    let proof = pcreds.prove(&hvk, &root, &cred, b"m", &mut rng)?;
    done(7);
    assert!(pcreds.verify(&hvk, b"m", &proof));
    done(8);
    Ok(())
}
