//! Criterion benchmarks of the lattice instantiation (feature `lattice`): the credential base
//! `Σ-vSIS`, the tag `Tag_LWR` with its oracles, and the protocol `Π_PCreds` at the lattice
//! backend at the thresholds `k = 1, 3, 5` (`k = 5` is the paper's comparison table), with ONE
//! real helper key.
//!
//! ```text
//! CARGO_BUILD_JOBS=4 cargo bench --bench lattice --features lattice
//! cargo bench --bench lattice --features lattice -- lattice-pcreds     # one group (a regex)
//! cargo bench --bench lattice --features lattice,parallel              # all cores, the attestations too
//! cargo bench --bench lattice --features lattice -- --test             # sizes, every benchmark once
//! ```
//!
//! The protocol group first prints the OBJECT SIZES at `k = 5` (the messages in their compact
//! fixed format, the others in their canonical encoding), then measures. What each measurement
//! covers (inputs prepared outside the timed closure):
//!
//! | group | id | algorithm | includes |
//! |---|---|---|---|
//! | `lattice-vsis` | `setup`, `keygen` | `PGen`, `KeyGen` | the expansion of `pp_Σ`; `TrapGen` and the expanded key |
//! | | `prepare_issue`, `blind_issue` | `PrepareIssue`, `BlindIssue` | `SampPre` under the cap, with the exact check of its output |
//! | | `verify`, `unblind` | `Verify`, `Unblind` | the product form, the norm |
//! | | `sk_decode` | decoding of the signing key | the trapdoor check, the expanded key and `h` |
//! | `lattice-lwr` | `identifier_point`, `request_point`, `eval`, `keygen` | `x_0 = H_mat("hid" ‖ d)`, `x_Q = H_mat("req" ‖ d)` (one matrix each), `TagEval` with its error, `TagKeyGen` | |
//! | `lattice-pcreds` | `setup` | `Setup` | `pp_Σ`, Jali's seed, the parameter sets, the statement constants |
//! | | `register` | `Register` | `TagKeyGen` and `id = Tag(usk, x_0)`, with the matrix of `x_0 = H_id(⟨hvk⟩)` |
//! | | `request_attestation`, `receive_attestation_request` | `π_id` and its check | one Jali proof / verification of `R_Tag` |
//! | | `attest`, `check_attestation` | `π_att` and its check | `x_Q` (and the matrices of the rule `x_Q ≠ x_0`), the tag, one Jali proof / verification of `R_att`; `attest` consumes a pending request, received again (untimed) for every iteration |
//! | | `request_credential/k=1,3,5` | `CredentialRequest` | `PrepareIssue`, one Jali proof of `R_iss` |
//! | | `evaluate_request/k=5` | the helper's checks | `π_iss` and the `k` attestations (one Jali verification each) |
//! | | `respond` | `CredentialRequestResponse` | `BlindIssue` (`SampPre`) and the record |
//! | | `unblind` | `Unblind` | one `Σ-vSIS` verification; it consumes the issuance state, decoded again (untimed) for every iteration |
//! | | `prove`, `verify` | `Prove`, `Verify` | one Jali proof / verification of `R_Possess` |
//!
//! The groups of multi-second algorithms take 10 samples of one iteration each (criterion's
//! minimum). `lattice-pcreds` runs under `cargo bench` only: `cargo test --all-targets`, which
//! runs every benchmark once, skips it. Numbers depend on the machine, the compiler and the
//! enabled features: record them with `rustc --version`, the commit and `RAYON_NUM_THREADS`.

#![allow(clippy::upper_case_acronyms)] // naming policy: see src/lib.rs
use std::{hint::black_box, time::Duration};

use criterion::{BenchmarkId, Criterion, SamplingMode};
use predicate_credential_system::{
    kiprf::{KIPRF, lwr::LWR},
    lattice::{Ternary, oracles},
    pcreds::{
        Decision, IssuanceRecord, IssuanceState, Policy, Reply,
        lattice::{
            LatticeProtocol,
            base::{VSIS, VSISSigningKey, VSISTape},
        },
    },
    serialization::WireFormat,
};
use rand::{SeedableRng, rngs::StdRng};

/// The threshold of the paper's comparison table.
const K: usize = 5;

/// The base: one helper key, one key `usk` and issuance randomness.
fn bench_vsis(c: &mut Criterion) {
    let mut rng = StdRng::seed_from_u64(0x7653_0001);
    let label = b"bench/lattice-vsis";
    let pp = VSIS::setup(label);
    let (vk, sk) = VSIS::keygen(&mut rng);
    let usk = Ternary::sample(&mut rng);
    let tape = VSISTape::sample(&mut rng);
    let request = VSIS::prepare_issue(&pp, &usk, &tape).expect("C");
    let pre = VSIS::blind_issue(&pp, &sk, &request, &mut rng).expect("σ̂");
    let cred = VSIS::unblind(&pp, &vk, &usk, &pre, &tape).expect("σ");
    let sk_bytes = WireFormat::to_bytes(&sk).expect("sk encoding");

    let mut group = c.benchmark_group("lattice-vsis");
    group.sample_size(20);
    group.bench_function("setup", |b| b.iter(|| VSIS::setup(black_box(label))));
    group.bench_function("keygen", |b| b.iter(|| VSIS::keygen(&mut rng)));
    group.bench_function("prepare_issue", |b| {
        b.iter(|| VSIS::prepare_issue(&pp, black_box(&usk), &tape))
    });
    group.bench_function("blind_issue", |b| {
        b.iter(|| VSIS::blind_issue(&pp, &sk, black_box(&request), &mut rng))
    });
    group.bench_function("verify", |b| {
        b.iter(|| assert!(VSIS::verify(&pp, &vk, &usk, black_box(&cred))))
    });
    group.bench_function("unblind", |b| {
        b.iter(|| VSIS::unblind(&pp, &vk, &usk, black_box(&pre), &tape))
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
    let digest = [7u8; 32];
    let x0 = oracles::identifier_point(label, &digest);
    let key = LWR.keygen(&mut rng);

    let mut group = c.benchmark_group("lattice-lwr");
    group.sample_size(20);
    group.bench_function("identifier_point", |b| {
        b.iter(|| oracles::identifier_point(label, black_box(&digest)))
    });
    group.bench_function("request_point", |b| {
        b.iter(|| oracles::request_point(label, black_box(&digest)))
    });
    group.bench_function("eval", |b| {
        b.iter(|| LWR.eval_with_error(black_box(&key), &x0))
    });
    group.bench_function("keygen", |b| b.iter(|| LWR.keygen(&mut rng)));
    group.finish();
}

/// The protocol: five roots, a newcomer with five attestations, credential requests at
/// `k = 1, 3, 5`, the issuance at `k = 5`, a membership proof; then every algorithm.
fn bench_pcreds(c: &mut Criterion) {
    let mut rng = StdRng::seed_from_u64(0x7063_0002);
    let pcreds = LatticeProtocol::setup(b"bench/lattice-pcreds").expect("pp");
    let policy = Policy::threshold(K).expect("k ≥ 1");
    let mut helper = pcreds.helper_keygen(policy, &mut rng);
    let hvk = pcreds.helper_key(helper.key().vk()).expect("hvk");

    let roots: Vec<_> = (0..K)
        .map(|i| {
            let user = pcreds.register(&hvk, &mut rng).expect("register");
            let ssid = format!("root-{i}").into_bytes();
            let (message, state) = pcreds
                .request_credential(&hvk, &user, Vec::new(), &ssid, &mut rng)
                .expect("request");
            let evaluated = pcreds
                .evaluate_request(&helper, &message, &ssid)
                .expect("evaluation");
            let Reply::PreCredential(pre) = pcreds
                .respond(&mut helper, evaluated, Decision::Root, &mut rng)
                .expect("root admission")
            else {
                panic!("a root admission issues")
            };
            let cred = pcreds.unblind(&hvk, &user, &pre, state).expect("unblind");
            (user, cred)
        })
        .collect();
    let newcomer = pcreds.register(&hvk, &mut rng).expect("register");
    let (ssid, contact) = (b"att".to_vec(), b"member@example".to_vec());
    let att_request = pcreds
        .request_attestation(&hvk, &newcomer, &ssid, &contact, &mut rng)
        .expect("π_id");
    // the requests each root has checked: `attest` consumes one
    let pending = || {
        pcreds
            .receive_attestation_request(&hvk, &att_request, &ssid, &contact)
            .expect("check π_id")
    };
    let attestations: Vec<_> = roots
        .iter()
        .map(|(user, cred)| {
            pcreds
                .attest(&hvk, user, cred, pending(), &mut rng)
                .expect("attestation")
        })
        .collect();
    let (message, state) = pcreds
        .request_credential(&hvk, &newcomer, attestations.clone(), b"req", &mut rng)
        .expect("request");
    let evaluated = pcreds
        .evaluate_request(&helper, &message, b"req")
        .expect("evaluation");
    assert!(evaluated.is_valid());
    let Reply::PreCredential(pre) = pcreds
        .respond(&mut helper, evaluated, Decision::Policy, &mut rng)
        .expect("issuance")
    else {
        panic!("issued")
    };
    let stored = state.to_bytes().expect("τ");
    let cred = pcreds
        .unblind(&hvk, &newcomer, &pre, state)
        .expect("unblind");
    let membership = pcreds
        .prove(&hvk, &newcomer, &cred, b"m", &mut rng)
        .expect("π_prove");

    println!("lattice-pcreds: object sizes at k = {K} (proof degree 128)");
    for (object, bytes) in [
        (
            "helper key hvk",
            WireFormat::to_bytes(hvk.vk()).expect("hvk").len(),
        ),
        (
            "helper (digest, hvk, sk)",
            helper.to_bytes().expect("helper").len(),
        ),
        (
            "user (usk, id, digest, helper)",
            newcomer.to_bytes().expect("user").len(),
        ),
        (
            "identifier id",
            WireFormat::to_bytes(newcomer.id()).expect("id").len(),
        ),
        ("attestation request (id, π_id)", att_request.compact_size()),
        ("attestation (t, π_att)", attestations[0].size()),
        ("|π| (k attestations, Ĉ, π_iss)", message.size()),
        ("credential request on the wire", message.compact_size()),
        ("credential σ", cred.to_bytes().expect("σ").len()),
        ("membership proof (π_prove)", membership.size()),
    ] {
        println!("  {object}: {bytes} bytes");
    }

    let mut group = c.benchmark_group("lattice-pcreds");
    group.sampling_mode(SamplingMode::Flat);
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(1));
    group.bench_function("setup", |b| {
        b.iter(|| LatticeProtocol::setup(black_box(b"bench/lattice-pcreds")))
    });
    group.bench_function("register", |b| b.iter(|| pcreds.register(&hvk, &mut rng)));
    group.bench_function("request_attestation", |b| {
        b.iter(|| pcreds.request_attestation(&hvk, &newcomer, &ssid, &contact, &mut rng))
    });
    group.bench_function("receive_attestation_request", |b| {
        b.iter(|| {
            pcreds.receive_attestation_request(&hvk, black_box(&att_request), &ssid, &contact)
        })
    });
    let (root, root_cred) = &roots[0];
    group.bench_function("attest", |b| {
        b.iter_batched(
            pending,
            |pending| pcreds.attest(&hvk, root, root_cred, pending, &mut rng),
            criterion::BatchSize::PerIteration,
        )
    });
    group.bench_function("check_attestation", |b| {
        b.iter(|| pcreds.check_attestation(&hvk, newcomer.id(), black_box(&attestations[0])))
    });
    for k in [1, 3, K] {
        group.bench_with_input(
            BenchmarkId::new("request_credential", format!("k={k}")),
            &k,
            |b, &k| {
                b.iter(|| {
                    pcreds.request_credential(
                        &hvk,
                        &newcomer,
                        attestations[..k].to_vec(),
                        b"req",
                        &mut rng,
                    )
                })
            },
        );
    }
    group.bench_function(
        BenchmarkId::new("evaluate_request", format!("k={K}")),
        |b| b.iter(|| pcreds.evaluate_request(&helper, black_box(&message), b"req")),
    );
    // respond on a fresh helper per iteration: `I` would answer `issued` the second time. The
    // request is a root admission (no attestations), whose evaluation, outside the timing, is
    // one π_iss check: respond does the same work for it as for an evaluated request at k = 5,
    // BlindIssue and the record.
    let (root, _) = pcreds
        .request_credential(&hvk, &newcomer, Vec::new(), b"root", &mut rng)
        .expect("root request");
    group.bench_function("respond", |b| {
        b.iter_batched(
            || {
                let fresh = pcreds
                    .restore_helper(
                        &helper.to_bytes().expect("helper"),
                        policy,
                        IssuanceRecord::new(),
                    )
                    .expect("restore");
                let evaluated = pcreds
                    .evaluate_request(&fresh, &root, b"root")
                    .expect("evaluation");
                (fresh, evaluated)
            },
            // the helper is returned, so that dropping (and wiping) its trapdoor is not timed
            |(mut fresh, evaluated)| {
                let reply = pcreds.respond(&mut fresh, evaluated, Decision::Root, &mut rng);
                (reply, fresh)
            },
            criterion::BatchSize::PerIteration,
        )
    });
    group.bench_function("unblind", |b| {
        b.iter_batched(
            || IssuanceState::from_bytes(&stored).expect("τ"),
            |state| pcreds.unblind(&hvk, &newcomer, black_box(&pre), state),
            criterion::BatchSize::SmallInput,
        )
    });
    group.bench_function("prove", |b| {
        b.iter(|| pcreds.prove(&hvk, &newcomer, &cred, b"m", &mut rng))
    });
    group.bench_function("verify", |b| {
        b.iter(|| assert!(pcreds.verify(&hvk, b"m", black_box(&membership))))
    });
    group.finish();
}

fn main() {
    let mut criterion = Criterion::default().configure_from_args();
    bench_vsis(&mut criterion);
    bench_lwr(&mut criterion);
    // `cargo bench` passes `--bench`; `cargo test --all-targets` runs every benchmark once
    // without it. The protocol's fixture alone is about a minute of Jali proofs, so its group runs
    // under `cargo bench` only (`cargo bench ... -- --test` for a single pass).
    if std::env::args().any(|arg| arg == "--bench") {
        bench_pcreds(&mut criterion);
    } else {
        eprintln!(
            "lattice-pcreds: skipped outside `cargo bench` (its fixture takes about a minute)"
        );
    }
    criterion.final_summary();
}
