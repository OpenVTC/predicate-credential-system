//! Criterion benchmarks of the lattice instantiation (feature `lattice`): the credential base
//! `Σ-vSIS`, the tag `Tag_LWR` with its oracles, and the construction at the thresholds
//! `k = 1, 3, 5` (`k = 5` is the paper's comparison table), with ONE real helper key.
//!
//! ```text
//! CARGO_BUILD_JOBS=4 cargo bench --bench lattice --features lattice
//! cargo bench --bench lattice --features lattice -- lattice-pcs        # one group (a regex)
//! cargo bench --bench lattice --features lattice,parallel              # all cores, CheckAtts_P too
//! cargo bench --bench lattice --features lattice -- --test             # sizes, every benchmark once
//! ```
//!
//! The run first prints the OBJECT SIZES of the construction at `k = 5` (`att`, `π` and the root
//! request in their compact fixed format, the others in their canonical encoding) and the size of
//! `π` at `k = 1` and `k = 3`, then measures. What each measurement covers (inputs prepared
//! outside the timed closure):
//!
//! | group | id | algorithm | includes |
//! |---|---|---|---|
//! | `lattice-vsis` | `setup`, `keygen` | `Setup`, `KeyGen` | the expansion of `pp_Σ`; `TrapGen` and the expanded key |
//! | | `com`, `sign`, `blind_issue` | `Com`, `Sign`, `BlindIssue` | `SampPre` under the cap, with the exact check of its output |
//! | | `verify`, `unblind` | `Verify`, `Unblind` | the product form, the norm |
//! | | `sk_decode` | decoding of the signing key | the trapdoor check, the expanded key and `h` |
//! | `lattice-lwr` | `h0`, `eval`, `pred_enc`, `keygen` | `H_0` (one matrix), `TagEval` with its error, `EncPred`, `TagKeyGen` | |
//! | `lattice-pcs` | `helper_keygen` | `HKeyGen` | `TrapGen`, the expanded key, `hsk` |
//! | | `user_keygen` | `UKeyGen` | `TagKeyGen` and `id = Tag(usk, c_0)` |
//! | | `attest` | `Attest` | `H_0(id)`, the tag, one Jali proof for `R_att` |
//! | | `verify_att` | `VerifyProofAtt` | `H_0(id)`, the public checks, one Jali verification of `R_att` |
//! | | `prove/k=1`, `prove/k=3`, `prove/k=5` | `Prove` | `CheckAtts_P` (`k` Jali verifications), `Com`, one Jali proof for `R_issue` |
//! | | `verify_proof/k=5` | `VerifyProof` | `CheckAtts_P` and the Jali verification of `π_0` |
//! | | `issue/k=5` | `Issue` (the helper's side) | `VerifyProof` (proof gating) and `BlindIssue` |
//! | | `unblind`, `verify_cred` | `Unblind`, `VerifyCred` | one `Σ-vSIS` verification each |
//! | | `root_request`, `verify_root_request`, `issue_root` | the root path | one `R_issue` proof, one verification, a verification and `BlindIssue` |
//!
//! The groups of multi-second algorithms take 10 samples of one iteration each (criterion's
//! minimum; about 16 minutes for `lattice-pcs` at one thread). `lattice-pcs` runs under
//! `cargo bench` only: `cargo test --all-targets`, which runs every benchmark once, skips it. The
//! paper's "prove" figure (the `k` attestations together with the subject's proof) is
//! `k · attest + prove`. Numbers depend on the machine, the compiler and the enabled features:
//! record them with `rustc --version`, the commit and `RAYON_NUM_THREADS`.

#![allow(clippy::upper_case_acronyms)] // naming policy: see src/lib.rs
use std::{hint::black_box, time::Duration};

use criterion::{BenchmarkId, Criterion, SamplingMode};
use predicate_credential_system::{
    LatticePCS,
    cred::{
        CredentialBase, VSIS,
        vsis::{VSISHiddenMessage, VSISIssuanceState, VSISSigningKey},
    },
    kiprf::{KIPRF, lwr::LWR},
    lattice::{BinaryPoly, Ternary, oracles},
    pcs::{Predicate, PredicateCredentialSystem, SetupParams},
    serialization::WireFormat,
};
use rand::{RngCore, SeedableRng, rngs::StdRng};

/// The threshold of the paper's comparison table.
const K: u32 = 5;

/// The base, as the construction uses it: one helper key, one message `(usk, φ, x_0)`.
fn bench_vsis(c: &mut Criterion) {
    let mut rng = StdRng::seed_from_u64(0x7653_0001);
    let label = b"bench/lattice-vsis";
    let pp = VSIS::setup(label).expect("pp");
    let (vk, sk) = VSIS::keygen(&pp, &mut rng);
    let usk = Ternary::sample(&mut rng);
    let x0 = [Ternary::sample(&mut rng), Ternary::sample(&mut rng)];
    let mut phi = [0u8; BinaryPoly::BYTES];
    rng.fill_bytes(&mut phi);
    let phi = BinaryPoly::from_bytes(phi);
    let m_hid = VSISHiddenMessage::new(usk, x0.clone());
    let r = VSISIssuanceState::new(x0);
    let m = VSIS::encode_message(&pp, &m_hid, &phi).expect("message");
    let com = VSIS::issuance_encoding(&pp, &vk, &m_hid, &phi, &r).expect("C");
    let pre = VSIS::blind_issue(&pp, &sk, &com, &phi, &mut rng).expect("ĉred");
    let sk_bytes = WireFormat::to_bytes(&sk).expect("sk encoding");

    let mut group = c.benchmark_group("lattice-vsis");
    group.sample_size(20);
    group.bench_function("setup", |b| b.iter(|| VSIS::setup(black_box(label))));
    group.bench_function("keygen", |b| b.iter(|| VSIS::keygen(&pp, &mut rng)));
    group.bench_function("com", |b| {
        b.iter(|| VSIS::issuance_encoding(&pp, &vk, black_box(&m_hid), &phi, &r))
    });
    group.bench_function("sign", |b| b.iter(|| VSIS::sign(&pp, &sk, &m, &mut rng)));
    group.bench_function("blind_issue", |b| {
        b.iter(|| VSIS::blind_issue(&pp, &sk, black_box(&com), &phi, &mut rng))
    });
    group.bench_function("verify", |b| {
        b.iter(|| assert!(VSIS::verify(&pp, &vk, &m, black_box(&pre))))
    });
    group.bench_function("unblind", |b| {
        b.iter(|| VSIS::unblind(&pp, &vk, &m, black_box(&pre), &r))
    });
    group.bench_function("sk_decode", |b| {
        b.iter(|| <VSISSigningKey as WireFormat>::from_bytes(black_box(&sk_bytes)))
    });
    group.finish();
}

/// The tag and its oracles.
fn bench_lwr(c: &mut Criterion) {
    let mut rng = StdRng::seed_from_u64(0x6c77_0001);
    let label = b"bench/lattice-lwr";
    let c0 = oracles::identity_point(label);
    let key = LWR.keygen(&mut rng);
    let id = LWR.eval(&key, &c0).expect("id");
    let f = Predicate::new(K, b"members".to_vec());

    let mut group = c.benchmark_group("lattice-lwr");
    group.sample_size(20);
    group.bench_function("h0", |b| {
        b.iter(|| oracles::tag_point(black_box(label), black_box(&id)))
    });
    group.bench_function("eval", |b| {
        b.iter(|| LWR.eval_with_error(black_box(&key), &c0))
    });
    group.bench_function("pred_enc", |b| {
        b.iter(|| oracles::pred_enc(label, black_box(&f)))
    });
    group.bench_function("keygen", |b| b.iter(|| LWR.keygen(&mut rng)));
    group.finish();
}

/// The construction: five founders with root credentials, a recipient with five attestations,
/// an issuance proof at `k = 5` and a credential, then issuance proofs at `k = 1` and `k = 3`;
/// then every algorithm of the box.
fn bench_pcs(c: &mut Criterion) {
    let mut rng = StdRng::seed_from_u64(0x7063_0001);
    let f_root = Predicate::root(b"founders".to_vec());
    let f = Predicate::new(K, b"members".to_vec());
    let open = LatticePCS::setup(SetupParams::new(b"bench/lattice-pcs".to_vec())).expect("pp");
    let policy = open.allow_list([&f_root, &f]);
    let pcs =
        LatticePCS::from_public_parameters(open.public_parameters().clone(), policy).expect("pp");
    let (hvk, hsk) = pcs.helper_keygen(&mut rng);

    let mut requests = Vec::new();
    let founders: Vec<_> = (0..K)
        .map(|_| {
            let (id_j, usk_j) = pcs.user_keygen(&mut rng).expect("user key");
            let (request, state) = pcs
                .root_request(&hvk, &f_root, &id_j, &usk_j, &mut rng)
                .expect("root request");
            let pre = pcs
                .issue_root(&hvk, &hsk, &f_root, &id_j, &request, &mut rng)
                .expect("root issuance");
            let cred_j = pcs
                .unblind(&hvk, &usk_j, &f_root, &pre, &state)
                .expect("unblind");
            requests.push((id_j.clone(), request));
            (usk_j, cred_j)
        })
        .collect();
    let (id, usk) = pcs.user_keygen(&mut rng).expect("user key");
    let attestations: Vec<_> = founders
        .iter()
        .map(|(usk_j, cred_j)| {
            pcs.attest(&hvk, usk_j, &f_root, cred_j, &id, &mut rng)
                .expect("attestation")
        })
        .collect();
    let (proof, state) = pcs
        .prove(&hvk, &f, &id, &usk, &attestations, &mut rng)
        .expect("issuance proof");
    let pre = pcs
        .issue(&hvk, &hsk, &f, &id, &proof, &mut rng)
        .expect("issuance");
    let cred = pcs.unblind(&hvk, &usk, &f, &pre, &state).expect("unblind");
    assert!(pcs.verify_cred(&hvk, &usk, &f, &cred));
    // Issuance proofs at k = 1 and k = 3 on the first attestations, AFTER the k = 5 flow: its
    // random draws, and so the sizes printed first, stay those of the README row
    // (tests/lattice_sizes.rs replays them).
    let smaller: Vec<(u32, Predicate, usize)> = [1u32, 3]
        .into_iter()
        .map(|k| {
            let f_k = Predicate::new(k, b"members".to_vec());
            let (proof_k, _) = pcs
                .prove(&hvk, &f_k, &id, &usk, &attestations[..k as usize], &mut rng)
                .expect("issuance proof");
            (k, f_k, proof_k.compact_size())
        })
        .collect();

    let (root_id, root_request) = &requests[0];
    let att_sizes: Vec<usize> = attestations.iter().map(|a| a.compact_size()).collect();
    let root_sizes: Vec<usize> = requests.iter().map(|(_, r)| r.compact_size()).collect();
    println!("lattice-pcs: object sizes at k = {K} (proof degree 128)");
    for (object, bytes) in [
        (
            "helper verification key hvk",
            WireFormat::to_bytes(&hvk).expect("hvk").len(),
        ),
        ("helper secret key hsk", hsk.to_bytes().expect("hsk").len()),
        ("user secret key usk", usk.to_bytes().expect("usk").len()),
        (
            "identifier id",
            WireFormat::to_bytes(&id).expect("id").len(),
        ),
        (
            "pre-credential ĉred",
            WireFormat::to_bytes(&pre).expect("ĉred").len(),
        ),
        (
            "credential cred = ((s, x_1), x_0)",
            cred.to_bytes().expect("cred").len(),
        ),
        (
            "issuance state st_iss",
            state.to_bytes().expect("state").len(),
        ),
        ("attestation att_j, compact (first)", att_sizes[0]),
        ("issuance proof π, compact", proof.compact_size()),
        ("root request (C, T_0, π_0), compact (first)", root_sizes[0]),
    ] {
        println!("  {object:<45} {bytes:>7} B");
    }
    println!(
        "  attestations {att_sizes:?}; root requests {root_sizes:?}; π_0 {} B",
        proof.proof.len()
    );
    for (k, _, bytes) in &smaller {
        println!("  issuance proof π, compact, k = {k}: {bytes} B");
    }

    let mut group = c.benchmark_group("lattice-pcs");
    group
        .sample_size(10)
        .sampling_mode(SamplingMode::Flat)
        .warm_up_time(Duration::from_millis(1))
        .measurement_time(Duration::from_secs(1));
    group.bench_function("helper_keygen", |b| b.iter(|| pcs.helper_keygen(&mut rng)));
    group.bench_function("user_keygen", |b| {
        b.iter(|| pcs.user_keygen(&mut rng).expect("user key"))
    });
    let (usk_0, cred_0) = &founders[0];
    group.bench_function("attest", |b| {
        b.iter(|| {
            pcs.attest(&hvk, usk_0, &f_root, cred_0, &id, &mut rng)
                .expect("attestation")
        })
    });
    group.bench_function("verify_att", |b| {
        b.iter(|| assert!(pcs.verify_attestation(&hvk, &id, black_box(&attestations[0]))))
    });
    for (k, f_k) in smaller.iter().map(|(k, f_k, _)| (*k, f_k)).chain([(K, &f)]) {
        group.bench_function(BenchmarkId::new("prove", format!("k={k}")), |b| {
            b.iter(|| {
                let w = black_box(&attestations[..k as usize]);
                pcs.prove(&hvk, f_k, &id, &usk, w, &mut rng)
                    .expect("issuance proof")
            })
        });
    }
    group.bench_function(BenchmarkId::new("verify_proof", format!("k={K}")), |b| {
        b.iter(|| assert!(pcs.verify_proof(&hvk, &f, &id, black_box(&proof))))
    });
    group.bench_function(BenchmarkId::new("issue", format!("k={K}")), |b| {
        b.iter(|| {
            pcs.issue(&hvk, &hsk, &f, &id, black_box(&proof), &mut rng)
                .expect("issuance")
        })
    });
    group.bench_function("unblind", |b| {
        b.iter(|| {
            pcs.unblind(&hvk, &usk, &f, black_box(&pre), &state)
                .expect("unblind")
        })
    });
    group.bench_function("verify_cred", |b| {
        b.iter(|| assert!(pcs.verify_cred(&hvk, &usk, &f, black_box(&cred))))
    });
    let (root_usk, _) = &founders[0];
    group.bench_function("root_request", |b| {
        b.iter(|| {
            pcs.root_request(&hvk, &f_root, root_id, root_usk, &mut rng)
                .expect("root request")
        })
    });
    group.bench_function("verify_root_request", |b| {
        b.iter(|| assert!(pcs.verify_root_request(&hvk, &f_root, root_id, black_box(root_request))))
    });
    group.bench_function("issue_root", |b| {
        b.iter(|| {
            pcs.issue_root(
                &hvk,
                &hsk,
                &f_root,
                root_id,
                black_box(root_request),
                &mut rng,
            )
            .expect("root issuance")
        })
    });
    group.finish();
}

fn main() {
    let mut criterion = Criterion::default().configure_from_args();
    bench_vsis(&mut criterion);
    bench_lwr(&mut criterion);
    // `cargo bench` passes `--bench`; `cargo test --all-targets` runs every benchmark once
    // without it. The construction's fixture alone is about 2 minutes of Jali proofs, so its group
    // runs under `cargo bench` only (`cargo bench ... -- --test` for a single pass).
    if std::env::args().any(|arg| arg == "--bench") {
        bench_pcs(&mut criterion);
    } else {
        eprintln!("lattice-pcs: skipped outside `cargo bench` (its fixture takes about 2 minutes)");
    }
    criterion.final_summary();
}
