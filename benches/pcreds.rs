//! Benchmarks of the protocol `Π_PCreds` ([`predicate_credential_system::pcreds`]) at threshold
//! `k = 5`, for every pairing-based base/tag pair, over BLS12-381.
//!
//! Each pair first prints its sizes. The functions measure each party's algorithms, the rows of
//! the paper's running-time table (§6, `tab:comparison`):
//!
//! * `attest`: the attester's tag, show and attestation proof (`attest` consumes the pending
//!   request, which is received again, untimed, for every iteration);
//! * `verify attestation`: the recipient's check of one attestation;
//! * `request (PrepareIssue + issuance proof)`: the requester's request;
//! * `verify (helper, k attestations + request)`: the helper's check of a request: `π_iss`, the
//!   recipient point, the `k` attestations, and the count of distinct tags;
//! * `blind issue`: `BlindIssue` alone;
//! * `unblind`: `Unblind` with the check of the credential (it consumes the issuance state,
//!   decoded again, untimed, for every iteration);
//! * `membership prove`, `membership verify`: the membership proof on a message.
//!
//! `prove (k attestations + request)` is the total work of the `k` attesters and the requester; in
//! deployment it runs on `k + 1` machines, so it is a throughput figure, not a latency.
//!
//! Run with `cargo bench --bench pcreds`; pin to one core with `taskset -c N` for stable numbers.

use std::hint::black_box;

use ark_bls12_381::{Bls12_381, G1Projective};
use ark_serialize::CanonicalSerialize;
use criterion::{BatchSize, Criterion};
use predicate_credential_system::{
    hash::bls12_381::G1Hasher,
    kiprf::{DDH, DY, ProtocolTag},
    pcreds::{
        Backend, Decision, IssuanceState, Policy, Protocol, Reply,
        pairing::{BBS, Base, PS, PairingBackend},
    },
    serialization::WireFormat,
};
use rand::{SeedableRng, rngs::StdRng};

type E = Bls12_381;
type G1 = G1Projective;

const K: usize = 5;

fn bench_pair<B, T>(c: &mut Criterion, name: &str, seed: u64)
where
    B: Base<E>,
    T: ProtocolTag<G1> + 'static,
{
    type Bk<B, T> = PairingBackend<E, B, T>;
    let mut rng = StdRng::seed_from_u64(seed);
    let label = format!("bench/pcreds/{name}").into_bytes();
    let pcreds = Protocol::<Bk<B, T>>::setup(&label).expect("setup");
    let mut helper = pcreds.helper_keygen(Policy::threshold(K).expect("k ≥ 1"), &mut rng);
    let hvk = helper.key().clone();

    // K root members with credentials.
    let members: Vec<_> = (0..K)
        .map(|i| {
            let user = pcreds.register(&hvk, &mut rng).expect("register");
            let ssid = format!("root-{i}").into_bytes();
            let (message, state) = pcreds
                .request_credential(&hvk, &user, Vec::new(), &ssid, &mut rng)
                .expect("root request");
            let evaluated = pcreds
                .evaluate_request(&helper, &message, &ssid)
                .expect("evaluate");
            let Reply::PreCredential(pre) = pcreds
                .respond(&mut helper, evaluated, Decision::Root, &mut rng)
                .expect("root response")
            else {
                panic!("root admission issues");
            };
            let cred = pcreds.unblind(&hvk, &user, &pre, state).expect("unblind");
            (user, cred)
        })
        .collect();

    // A newcomer's attestation request, received by every member.
    let newcomer = pcreds.register(&hvk, &mut rng).expect("register");
    let request = pcreds
        .request_attestation(&hvk, &newcomer, b"att", b"contact", &mut rng)
        .expect("attestation request");
    // the request as each member has checked it: `attest` consumes one
    let pending = || {
        pcreds
            .receive_attestation_request(&hvk, &request, b"att", b"contact")
            .expect("π_id")
    };
    let attestations: Vec<_> = members
        .iter()
        .map(|(m, cred)| {
            pcreds
                .attest(&hvk, m, cred, pending(), &mut rng)
                .expect("attest")
        })
        .collect();
    let (message, state) = pcreds
        .request_credential(&hvk, &newcomer, attestations.clone(), b"ssid", &mut rng)
        .expect("request");
    let evaluated = pcreds
        .evaluate_request(&helper, &message, b"ssid")
        .expect("evaluate");
    assert_eq!(evaluated.tags().len(), K);
    let proof = pcreds
        .prove(&hvk, &members[0].0, &members[0].1, b"message", &mut rng)
        .expect("prove");

    println!(
        "{name}: |id| = {} B, |att| = {} B, |pi| (k = {K}) = {} B, |cred| = {} B, |membership proof| = {} B",
        newcomer.id().compressed_size(),
        attestations[0].size(),
        message.size(),
        members[0].1.as_inner().compressed_size(),
        proof.size(),
    );

    let mut group = c.benchmark_group(format!("pcreds/{name}"));
    group.bench_function("prove (k attestations + request)", |b| {
        b.iter_batched(
            || members.iter().map(|_| pending()).collect::<Vec<_>>(),
            |pendings| {
                let atts: Vec<_> = members
                    .iter()
                    .zip(pendings)
                    .map(|((m, cred), pending)| {
                        pcreds
                            .attest(&hvk, m, cred, pending, &mut rng)
                            .expect("attest")
                    })
                    .collect();
                black_box(
                    pcreds
                        .request_credential(&hvk, &newcomer, atts, b"ssid", &mut rng)
                        .expect("request"),
                )
            },
            BatchSize::SmallInput,
        );
    });
    group.bench_function("verify (helper, k attestations + request)", |b| {
        b.iter(|| {
            black_box(
                pcreds
                    .evaluate_request(&helper, &message, b"ssid")
                    .expect("evaluate"),
            )
        });
    });
    group.bench_function("request (PrepareIssue + issuance proof)", |b| {
        b.iter_batched(
            || attestations.clone(),
            |atts| {
                black_box(
                    pcreds
                        .request_credential(&hvk, &newcomer, atts, b"ssid", &mut rng)
                        .expect("request"),
                )
            },
            BatchSize::SmallInput,
        );
    });
    group.bench_function("attest", |b| {
        b.iter_batched(
            pending,
            |pending| {
                black_box(
                    pcreds
                        .attest(&hvk, &members[0].0, &members[0].1, pending, &mut rng)
                        .expect("attest"),
                )
            },
            BatchSize::SmallInput,
        );
    });
    group.bench_function("verify attestation", |b| {
        b.iter(|| black_box(pcreds.verify_attestation(&hvk, newcomer.id(), &attestations[0])));
    });
    group.bench_function("blind issue", |b| {
        // BlindIssue alone, under a key of the backend (the helper's own key never leaves it).
        let (_, sk) = Bk::<B, T>::keygen(pcreds.params(), &mut rng);
        b.iter(|| {
            black_box(Bk::<B, T>::blind_issue(
                pcreds.params(),
                &sk,
                &message.request,
                &mut rng,
            ))
        });
    });
    group.bench_function("unblind", |b| {
        let mut issuer = pcreds.helper_keygen(Policy::threshold(K).expect("k ≥ 1"), &mut rng);
        let issuer_key = issuer.key().clone();
        // the newcomer registers with this helper too, reusing its key
        let newcomer = pcreds
            .register_reusing(&issuer_key, &newcomer)
            .expect("register");
        let (msg, st) = pcreds
            .request_credential(&issuer_key, &newcomer, Vec::new(), b"u", &mut rng)
            .expect("request");
        let stored = st.to_bytes().expect("τ");
        let evaluated = pcreds
            .evaluate_request(&issuer, &msg, b"u")
            .expect("evaluate");
        let Reply::PreCredential(pre) = pcreds
            .respond(&mut issuer, evaluated, Decision::Root, &mut rng)
            .expect("respond")
        else {
            panic!("issues");
        };
        b.iter_batched(
            || IssuanceState::from_bytes(&stored).expect("τ"),
            |st| {
                black_box(
                    pcreds
                        .unblind(&issuer_key, &newcomer, &pre, st)
                        .expect("unblind"),
                )
            },
            BatchSize::SmallInput,
        );
    });
    group.bench_function("membership prove", |b| {
        b.iter(|| {
            black_box(
                pcreds
                    .prove(&hvk, &members[0].0, &members[0].1, b"message", &mut rng)
                    .expect("prove"),
            )
        });
    });
    group.bench_function("membership verify", |b| {
        b.iter(|| black_box(pcreds.verify(&hvk, b"message", &proof)));
    });
    group.finish();
    let _ = state;
}

fn benches(c: &mut Criterion) {
    bench_pair::<PS, DDH<G1, G1Hasher>>(c, "ps-ddh", 0x5053_0001);
    bench_pair::<PS, DY<G1, G1Hasher>>(c, "ps-dy", 0x5053_0002);
    bench_pair::<BBS<G1Hasher>, DDH<G1, G1Hasher>>(c, "bbs-ddh", 0x4242_0001);
    bench_pair::<BBS<G1Hasher>, DY<G1, G1Hasher>>(c, "bbs-dy", 0x4242_0002);
}

criterion::criterion_group!(group, benches);
criterion::criterion_main!(group);
