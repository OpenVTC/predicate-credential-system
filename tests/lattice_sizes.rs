//! The sizes of the README row of the lattice instantiation (`Σ-vSIS` with `Tag_LWR`, proof
//! degree 128): `att`, `π` at `k = 5` and `cred`, with ONE real helper key and real Jali proofs.
//!
//! **Do proof sizes vary with the seed? Yes, by tens of bytes.** `att` is 468 bytes plus a Jali
//! proof for `R_att`, `π` is the `k` attestations, 2900 bytes and a Jali proof for `R_issue`, and
//! `cred` is 5888 bytes for every seed; the Jali proofs vary with the seed (the prover's coins,
//! and the witness through `SampPre`'s coins). Measured over 12 seeded `k = 5` runs (the two of
//! `readme_row_sizes_for_the_two_seeded_runs` and the ten of `proof_size_spread_across_seeds`;
//! release, aarch64, 2026-10-04):
//!
//! | object | runs | min | max | spread | mean | sd |
//! |---|---|---|---|---|---|---|
//! | `att` | 60 attestations | 83,583 | 83,652 | 69 B (0.083 %) | 83,613.9 | 14.2 |
//! | `π` (`k = 5`) | 12 | 462,030 | 462,151 | 121 B (0.026 %) | 462,107.4 | 34.5 |
//! | `π_0` | 12 | 41,113 | 41,166 | 53 B | 41,138.1 | 15.7 |
//! | root request | 60 | 44,005 | 44,080 | 75 B | 44,049.8 | 14.1 |
//! | `cred` | 12 | 5888 | 5888 | 0 | | |
//!
//! A sample of 12 runs bounds nothing: other seeds can fall outside these ranges. The tests
//! assert the band `[0.95, 1] ×` the estimate of each parameter set (85,608 and 42,912 bytes),
//! which every proof met.
//!
//! **For a fixed seed they do not vary.** Jali's `prove_bytes_with_seed` is deterministic in its
//! inputs; `SampPre` derives its coins from the seed and computes with IEEE-754 `+ − × ÷`, `sqrt`,
//! `floor` and round-half-even only (the `exp`, `ln` and `cbrt` calls of `ntru-trapdoor` are in
//! its tests; the FFT constants are tables) [read: ntru-trapdoor `src/sign.rs`, `src/ffsamp.rs`,
//! `src/sampler.rs`, `src/fft/gm.rs`]; every other step is integer arithmetic. So a seeded run
//! reproduces its proofs byte for byte [measured: `proofs_are_deterministic_for_a_fixed_seed`;
//! and the two runs below reproduce the sizes that `sizes_at_k5` and the benchmark measured
//! earlier the same day, in other processes and build profiles]. Reproduction on another
//! architecture is [derived], not measured (only aarch64 was run). A change of Jali, of
//! `ntru-trapdoor`'s coin derivation or of the order of the random draws changes the pinned values
//! below, not the band.
//!
//! Heavy. Run in release, one at a time:
//! `RUST_TEST_THREADS=1 cargo test --release --features lattice --test lattice_sizes -- --ignored --nocapture`.
#![cfg(feature = "lattice")]
#![allow(clippy::upper_case_acronyms)] // naming policy: see src/lib.rs

mod lattice_support;

use std::time::Instant;

use lattice_support::*;
use predicate_credential_system::{
    LatticePCS,
    cred::vsis::VSISCredential,
    jali::params::TboxParams,
    lattice::sets::ParameterSets,
    pcs::{
        Predicate, PredicateCredentialSystem, SetupParams,
        lattice::{Attestation, Credential},
    },
    serialization::WireFormat,
};
use rand::{SeedableRng, rngs::StdRng};

/// The sizes of one seeded `k = 5` run.
#[derive(Debug, PartialEq, Eq)]
struct Sizes {
    att: [usize; 5],
    root: [usize; 5],
    pi0: usize,
    pi: usize,
    cred: usize,
}

/// The `k = 5` flow of `sizes_at_k5` (tests/lattice_pcs.rs) and of the benchmark fixture
/// (benches/lattice.rs), draw for draw: `HKeyGen`; five founders through the root path
/// (`UKeyGen`, root request, `issue_root`, `Unblind`); the recipient's `UKeyGen`, five
/// attestations, `Prove`, `Issue`, `Unblind`. Asserts the fixed parts of every encoding.
fn readme_flow(label: &[u8], seed: u64) -> Sizes {
    let t = Instant::now();
    let mut rng = StdRng::seed_from_u64(seed);
    let f_root = Predicate::root(b"founders".to_vec());
    let f = Predicate::new(5, b"members".to_vec());
    let open = LatticePCS::setup(SetupParams::new(label.to_vec())).unwrap();
    let policy = open.allow_list([&f_root, &f]);
    let pcs = LatticePCS::from_public_parameters(open.public_parameters().clone(), policy).unwrap();
    let (hvk, hsk) = pcs.helper_keygen(&mut rng);
    let mut founders = Vec::new();
    let mut requests = Vec::new();
    for _ in 0..5 {
        let (id, usk) = pcs.user_keygen(&mut rng).unwrap();
        let (request, state) = pcs
            .root_request(&hvk, &f_root, &id, &usk, &mut rng)
            .unwrap();
        let pre = pcs
            .issue_root(&hvk, &hsk, &f_root, &id, &request, &mut rng)
            .unwrap();
        let cred = pcs.unblind(&hvk, &usk, &f_root, &pre, &state).unwrap();
        requests.push(wire_root_request(&request));
        founders.push((usk, cred));
    }
    let (id, usk) = pcs.user_keygen(&mut rng).unwrap();
    let attestations: Vec<Attestation> = founders
        .iter()
        .map(|(usk_j, cred_j)| {
            pcs.attest(&hvk, usk_j, &f_root, cred_j, &id, &mut rng)
                .unwrap()
        })
        .collect();
    let (proof, state) = pcs
        .prove(&hvk, &f, &id, &usk, &attestations, &mut rng)
        .unwrap();
    let proof = wire_issuance_proof(&proof, &f);
    let pre = pcs.issue(&hvk, &hsk, &f, &id, &proof, &mut rng).unwrap();
    let cred = pcs.unblind(&hvk, &usk, &f, &pre, &state).unwrap();
    assert!(pcs.verify_cred(&hvk, &usk, &f, &cred));
    // the fixed parts: 468 per attestation, 2900 + |π_0| for π (and LE32(k) in canonical form),
    // 2900 + |π_0| per root request; the secrets and keys
    for att in &proof.attestations {
        assert_eq!(wire_attestation(att).compact_size(), 468 + att.proof.len());
    }
    let jali: usize = proof.attestations.iter().map(|a| a.proof.len()).sum();
    assert_eq!(
        proof.compact_size(),
        5 * 468 + jali + 2900 + proof.proof.len()
    );
    assert_eq!(
        WireFormat::to_bytes(&proof).unwrap().len(),
        proof.compact_size() + 4
    );
    assert_eq!(wire_credential(&cred).to_bytes().unwrap().len(), 5888);
    assert_eq!(WireFormat::to_bytes(&wire_pre(&pre)).unwrap().len(), 5376);
    assert_eq!(WireFormat::to_bytes(&hvk).unwrap().len(), 2560);
    assert_eq!(wire_hsk(&hsk).to_bytes().unwrap().len(), 8489);
    assert_eq!(wire_usk(&usk).to_bytes().unwrap().len(), 256);
    assert_eq!(wire_state(&state).to_bytes().unwrap().len(), 896);
    let sizes = Sizes {
        att: std::array::from_fn(|j| attestations[j].compact_size()),
        root: std::array::from_fn(|j| requests[j].compact_size()),
        pi0: proof.proof.len(),
        pi: proof.compact_size(),
        cred: cred.to_bytes().unwrap().len(),
    };
    println!(
        "{} seed {seed:#x}: {sizes:?} ({:.1} s)",
        String::from_utf8_lossy(label),
        secs(t)
    );
    sizes
}

/// The estimated proof length of an embedded parameter set.
fn estimate(set: &TboxParams) -> usize {
    set.check().unwrap().estimated_proof_bytes
}

/// Each Jali proof of a run within `[0.95, 1]` of the estimate of its parameter set (85,608 bytes
/// for `R_att`, 42,912 for `R_issue` and the root path).
fn assert_in_band(sizes: &Sizes) {
    let sets = ParameterSets::load().unwrap();
    let (att, issue, root) = (
        estimate(&sets.att),
        estimate(&sets.issue),
        estimate(&sets.issue_root),
    );
    assert_eq!((att, issue, root), (85_608, 42_912, 42_912));
    let in_band = |len: usize, estimate: usize| len * 100 >= estimate * 95 && len <= estimate;
    assert!(
        sizes.att.iter().all(|&a| in_band(a - 468, att)),
        "{sizes:?}"
    );
    assert!(
        sizes.root.iter().all(|&r| in_band(r - 2900, root)),
        "{sizes:?}"
    );
    assert!(in_band(sizes.pi0, issue), "{sizes:?}");
}

/// The README row (`Σ-vSIS`: `att` ≈ 83,600, `π` ≈ 462,100 at `k = 5`, `cred` 5888) and its note
/// ("in two seeded runs at `k = 5` [...] `att` has 83,586-83,639 bytes, `π` 462,105-462,126 and a
/// root request 44,031-44,063"): the two seeded runs are `sizes_at_k5` (label
/// `lattice-pcs/sizes`, seed `0x1a77_0005`) and the benchmark fixture (`bench/lattice-pcs`,
/// `0x7063_0001`). Both are reproduced here exactly, and the README's figures are their union.
#[test]
#[ignore = "heavy: two k = 5 flows (about 3 minutes in release)"]
fn readme_row_sizes_for_the_two_seeded_runs() {
    let sizes_run = readme_flow(b"lattice-pcs/sizes", 0x1a77_0005);
    let bench_run = readme_flow(b"bench/lattice-pcs", 0x7063_0001);
    // the values measured on 2026-10-04 (construction stage: tests/lattice_pcs.rs `sizes_at_k5`
    // and `cargo bench --bench lattice`), reproduced exactly
    assert_eq!(
        sizes_run,
        Sizes {
            att: [83_622, 83_639, 83_601, 83_632, 83_603],
            root: [44_056, 44_049, 44_043, 44_063, 44_060],
            pi0: 41_129,
            pi: 462_126,
            cred: 5888,
        }
    );
    assert_eq!(
        bench_run,
        Sizes {
            att: [83_601, 83_628, 83_586, 83_629, 83_614],
            root: [44_043, 44_059, 44_051, 44_031, 44_035],
            pi0: 41_147,
            pi: 462_105,
            cred: 5888,
        }
    );
    for run in [&sizes_run, &bench_run] {
        assert_in_band(run);
        // the README row: att ≈ 83,600 (83,586-83,639), π ≈ 462,100 (462,105-462,126), cred 5888
        assert!(run.att.iter().all(|a| (83_586..=83_639).contains(a)));
        assert!(run.att.iter().all(|a| a.abs_diff(83_600) < 50));
        assert!((462_105..=462_126).contains(&run.pi) && run.pi.abs_diff(462_100) < 50);
        assert!(run.root.iter().all(|r| (44_031..=44_063).contains(r)));
        assert_eq!(run.cred, Credential::BYTES);
    }
    let all_att = sizes_run.att.iter().chain(&bench_run.att);
    assert_eq!(
        (*all_att.clone().min().unwrap(), *all_att.max().unwrap()),
        (83_586, 83_639)
    );
}

/// A fixed seed gives the same proofs, byte for byte; another seed gives other proofs (and, in
/// general, other lengths). The attestations and root requests of two runs from the same RNG
/// state are identical; the state after a draw gives another proof.
#[test]
#[ignore = "heavy: four R_att and six R_issue proofs (about 50 s in release)"]
fn proofs_are_deterministic_for_a_fixed_seed() {
    let mut rng = StdRng::seed_from_u64(0x5eed_0001);
    let f_root = Predicate::root(b"founders".to_vec());
    let pcs = deployment(b"lattice-sizes/determinism", &[&f_root]);
    let (hvk, hsk) = pcs.helper_keygen(&mut rng);
    let mut founder = Member::new(&pcs, "F", &mut rng);
    root_issue(&pcs, &hvk, &hsk, &mut founder, &f_root, &mut rng);
    let recipient = Member::new(&pcs, "R", &mut rng);
    let state = rng.clone();
    let mut proofs = Vec::new();
    for mut r in [state.clone(), state, rng] {
        let att = pcs
            .attest(
                &hvk,
                &founder.usk,
                &f_root,
                founder.cred(),
                &recipient.id,
                &mut r,
            )
            .unwrap();
        let (request, root_state) = pcs
            .root_request(&hvk, &f_root, &recipient.id, &recipient.usk, &mut r)
            .unwrap();
        proofs.push((att, request, root_state.to_bytes().unwrap().to_vec()));
    }
    assert_eq!(
        proofs[0].0, proofs[1].0,
        "the same seed, the same attestation"
    );
    assert_eq!(
        proofs[0].1, proofs[1].1,
        "the same seed, the same root request"
    );
    assert_eq!(proofs[0].2, proofs[1].2, "... and the same x_0");
    // the third run starts from the same state too (rng was not used after the clone)
    assert_eq!(proofs[0].0, proofs[2].0);
    // another state: other coins, other proofs
    let mut other = StdRng::seed_from_u64(0x5eed_0002);
    let att = pcs
        .attest(
            &hvk,
            &founder.usk,
            &f_root,
            founder.cred(),
            &recipient.id,
            &mut other,
        )
        .unwrap();
    assert_eq!(
        att.tag, proofs[0].0.tag,
        "the tag is deterministic in the keys"
    );
    assert_ne!(att.proof, proofs[0].0.proof, "the proof is not");
    let (request, _) = pcs
        .root_request(&hvk, &f_root, &recipient.id, &recipient.usk, &mut other)
        .unwrap();
    assert_ne!(request.c, proofs[0].1.c, "a fresh x_0, another C");
    println!(
        "same seed: |att| = {} = {}; other seed: |att| = {}; root requests {} / {} B",
        proofs[0].0.compact_size(),
        proofs[1].0.compact_size(),
        att.compact_size(),
        proofs[0].1.compact_size(),
        request.compact_size()
    );
    // SampPre's coins come from the seed too: the same state gives the same pre-credential
    let user = Member::new(&pcs, "U", &mut StdRng::seed_from_u64(0x5eed_0003));
    let (request, _) = pcs
        .root_request(
            &hvk,
            &f_root,
            &user.id,
            &user.usk,
            &mut StdRng::seed_from_u64(0x5eed_0004),
        )
        .unwrap();
    let issue = |seed: u64| -> VSISCredential {
        let hsk = wire_hsk(&hsk);
        pcs.issue_root(
            &hvk,
            &hsk,
            &f_root,
            &user.id,
            &request,
            &mut StdRng::seed_from_u64(seed),
        )
        .unwrap()
    };
    assert!(issue(7) == issue(7), "the same coins, the same preimage");
    assert!(issue(7) != issue(8), "fresh coins, another preimage");
}

/// Measurement (not a check of the README): the sizes over ten more seeded `k = 5` runs, to state
/// how much the proof sizes vary with the seed (the module docs). Asserts the band of
/// [`assert_in_band`] and prints every size and the extremes.
#[test]
#[ignore = "measurement: ten k = 5 flows (about 14 minutes in release)"]
fn proof_size_spread_across_seeds() {
    let runs: Vec<Sizes> = (1..=10u64)
        .map(|seed| readme_flow(b"lattice-sizes/spread", 0x5bd0_0000 + seed))
        .collect();
    for run in &runs {
        assert_in_band(run);
        assert_eq!(run.cred, 5888);
    }
    let att: Vec<usize> = runs.iter().flat_map(|r| r.att).collect();
    let root: Vec<usize> = runs.iter().flat_map(|r| r.root).collect();
    let pi0: Vec<usize> = runs.iter().map(|r| r.pi0).collect();
    let pi: Vec<usize> = runs.iter().map(|r| r.pi).collect();
    let stats = |name: &str, v: &[usize]| {
        let (min, max) = (*v.iter().min().unwrap(), *v.iter().max().unwrap());
        let mean = v.iter().sum::<usize>() as f64 / v.len() as f64;
        let var = v.iter().map(|&x| (x as f64 - mean).powi(2)).sum::<f64>() / (v.len() - 1) as f64;
        println!(
            "SPREAD {name}: n = {}, min {min}, max {max}, spread {} B ({:.3} %), mean {mean:.1}, sd {:.1}",
            v.len(),
            max - min,
            100.0 * (max - min) as f64 / mean,
            var.sqrt()
        );
    };
    stats("|att|", &att);
    stats("|root request|", &root);
    stats("|π_0|", &pi0);
    stats("|π| (k = 5)", &pi);
}
