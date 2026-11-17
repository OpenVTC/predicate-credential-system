//! End-to-end tests of the protocol `Π_PCreds` ([`predicate_credential_system::pcreds`]) for
//! every pairing-based base/tag pair: issuance by threshold, the issuance record, counting
//! distinct attesters, recipient binding, membership proofs, and the fixed sizes reported in the
//! paper.

use ark_bls12_381::{Bls12_381, G1Projective};
use ark_ec::PrimeGroup;
use ark_ff::{One, Zero};
use predicate_credential_system::{
    Error,
    hash::bls12_381::G1Hasher,
    kiprf::{DDH, DY, ProtocolTag},
    pcreds::{
        Attestation, Backend, Credential, Decision, Helper, HelperKey, Policy, Protocol, Reply,
        User,
        pairing::{BBS, Base, PS, PairingBackend},
    },
};
use rand::{SeedableRng, rngs::StdRng};

type E = Bls12_381;
type G1 = G1Projective;
type TagDDH = DDH<G1, G1Hasher>;
type TagDY = DY<G1, G1Hasher>;
type BbsBase = BBS<G1Hasher>;

const K: usize = 5;

/// A deployment with a helper and `K` root members holding credentials.
struct World<Bk: Backend> {
    pcreds: Protocol<Bk>,
    helper: Helper<Bk>,
    members: Vec<(User<Bk>, Credential<Bk>)>,
    rng: StdRng,
}

fn world<Bk: Backend>(label: &[u8], seed: u64) -> World<Bk> {
    let mut rng = StdRng::seed_from_u64(seed);
    let pcreds = Protocol::<Bk>::setup(label).expect("setup");
    let mut helper = pcreds.helper_keygen(Policy::threshold(K).expect("k ≥ 1"), &mut rng);
    let hvk = helper.key().clone();
    let mut members = Vec::new();
    for i in 0..K {
        let user = pcreds.register(&hvk, &mut rng).expect("register");
        let ssid = format!("root-{i}").into_bytes();
        let (message, state) = pcreds
            .request_credential(&hvk, &user, Vec::new(), &ssid, &mut rng)
            .expect("root request");
        let evaluated = pcreds
            .evaluate_request(&helper, &message, &ssid)
            .expect("evaluate");
        assert!(!evaluated.is_valid(), "no attestations: the policy rejects");
        let reply = pcreds
            .respond(&mut helper, evaluated, Decision::Root, &mut rng)
            .expect("root response");
        let Reply::PreCredential(pre) = reply else {
            panic!("root admission must issue");
        };
        let cred = pcreds.unblind(&hvk, &user, &pre, state).expect("unblind");
        members.push((user, cred));
    }
    assert_eq!(helper.store().len(), K);
    World {
        pcreds,
        helper,
        members,
        rng,
    }
}

/// `AttestationRequest` and `AttestationRequestResponse` from the credentialed `attester` for
/// `newcomer`, through the contact name `member-{j}@example`.
fn attestation<Bk: Backend>(
    pcreds: &Protocol<Bk>,
    hvk: &HelperKey<Bk>,
    (attester, cred): (&User<Bk>, &Credential<Bk>),
    newcomer: &User<Bk>,
    j: usize,
    rng: &mut StdRng,
) -> Attestation<Bk> {
    let (ssid, contact) = (
        format!("att-{j}").into_bytes(),
        format!("member-{j}@example").into_bytes(),
    );
    let request = pcreds
        .request_attestation(hvk, newcomer, &ssid, &contact, rng)
        .expect("attestation request");
    let pending = pcreds
        .receive_attestation_request(hvk, &request, &ssid, &contact)
        .expect("π_id");
    assert!(!pcreds.verify_attestation_request(hvk, &request, b"other ssid", &contact));
    assert!(!pcreds.verify_attestation_request(hvk, &request, &ssid, b"other contact"));
    pcreds
        .attest(hvk, attester, cred, pending, rng)
        .expect("attest")
}

fn full_flow<B: Base<E>, T: ProtocolTag<G1> + 'static>(label: &[u8], seed: u64) {
    let World {
        pcreds,
        mut helper,
        members,
        mut rng,
    } = world::<PairingBackend<E, B, T>>(label, seed);
    let hvk = pcreds.helper_key(helper.key().vk()).expect("hvk ∈ V_pp");
    let newcomer = pcreds.register(&hvk, &mut rng).expect("register");

    // Attestation requests and responses.
    let mut attestations = Vec::new();
    for (j, (member, cred)) in members.iter().enumerate() {
        let att = attestation(&pcreds, &hvk, (member, cred), &newcomer, j, &mut rng);
        assert_eq!(pcreds.check_attestation(&hvk, newcomer.id(), &att), Ok(()));
        attestations.push(att);
    }

    // Too few distinct attesters: the request fails, nothing is issued.
    let (short, _) = pcreds
        .request_credential(
            &hvk,
            &newcomer,
            attestations[..K - 1].to_vec(),
            b"req-0",
            &mut rng,
        )
        .expect("request");
    let evaluated = pcreds
        .evaluate_request(&helper, &short, b"req-0")
        .expect("evaluate");
    assert_eq!(evaluated.tags().len(), K - 1);
    assert_eq!(
        pcreds
            .respond(&mut helper, evaluated, Decision::Policy, &mut rng)
            .expect("respond"),
        Reply::Fail
    );

    // A repeated attestation from one member counts once.
    let mut repeated = attestations[..K - 1].to_vec();
    let first = (&members[0].0, &members[0].1);
    repeated.push(attestation(&pcreds, &hvk, first, &newcomer, 99, &mut rng));
    assert_eq!(repeated[0].tag, repeated[K - 1].tag);
    let (dup, _) = pcreds
        .request_credential(&hvk, &newcomer, repeated, b"req-1", &mut rng)
        .expect("request");
    let evaluated = pcreds
        .evaluate_request(&helper, &dup, b"req-1")
        .expect("evaluate");
    assert_eq!(evaluated.tags().len(), K - 1);
    assert!(!evaluated.is_valid());

    // K distinct attesters: issued once, then acknowledged.
    let (message, state) = pcreds
        .request_credential(&hvk, &newcomer, attestations.clone(), b"req-2", &mut rng)
        .expect("request");
    assert!(
        pcreds
            .evaluate_request(&helper, &message, b"req-3")
            .is_err(),
        "π_iss is bound to ssid"
    );
    let evaluated = pcreds
        .evaluate_request(&helper, &message, b"req-2")
        .expect("evaluate");
    assert_eq!(evaluated.tags().len(), K);
    assert!(evaluated.is_valid());
    assert_eq!(evaluated.id(), newcomer.id());
    let Reply::PreCredential(pre) = pcreds
        .respond(&mut helper, evaluated, Decision::Policy, &mut rng)
        .expect("respond")
    else {
        panic!("a valid request must be issued");
    };
    let cred = pcreds
        .unblind(&hvk, &newcomer, &pre, state)
        .expect("unblind");
    assert!(pcreds.verify_credential(&hvk, &newcomer, &cred));
    let (again, _) = pcreds
        .request_credential(&hvk, &newcomer, attestations.clone(), b"req-4", &mut rng)
        .expect("request");
    let evaluated = pcreds
        .evaluate_request(&helper, &again, b"req-4")
        .expect("evaluate");
    assert_eq!(
        pcreds
            .respond(&mut helper, evaluated, Decision::Policy, &mut rng)
            .expect("respond"),
        Reply::Issued
    );
    assert_eq!(helper.store().len(), K + 1);

    // Attestations are bound to their recipient.
    let other = pcreds.register(&hvk, &mut rng).expect("register");
    assert!(!pcreds.verify_attestation(&hvk, other.id(), &attestations[0]));

    // The new member can attest, and prove membership on a message.
    let fresh = pcreds.register(&hvk, &mut rng).expect("register");
    let att = attestation(&pcreds, &hvk, (&newcomer, &cred), &fresh, 7, &mut rng);
    assert!(pcreds.verify_attestation(&hvk, fresh.id(), &att));
    let proof = pcreds
        .prove(&hvk, &newcomer, &cred, b"hello", &mut rng)
        .expect("prove");
    assert!(pcreds.verify(&hvk, b"hello", &proof));
    assert!(!pcreds.verify(&hvk, b"goodbye", &proof));

    // Tampering is detected.
    let mut bad = attestations[1].clone();
    bad.proof.challenge += <E as ark_ec::pairing::Pairing>::ScalarField::one();
    assert_eq!(
        pcreds.check_attestation(&hvk, &message.id, &bad),
        Err(Error::InvalidProof)
    );
    let mut bad = attestations[1].clone();
    bad.tag = G1::zero();
    assert!(!pcreds.verify_attestation(&hvk, &message.id, &bad));
    let mut bad = attestations[1].clone();
    bad.tag = attestations[2].tag;
    assert!(!pcreds.verify_attestation(&hvk, &message.id, &bad));
    let mut bad = message.clone();
    bad.id = G1::generator();
    assert!(pcreds.evaluate_request(&helper, &bad, b"req-2").is_err());
}

#[test]
fn ps_with_ddh() {
    full_flow::<PS, TagDDH>(b"test/ps-ddh", 1);
}

#[test]
fn ps_with_dy() {
    full_flow::<PS, TagDY>(b"test/ps-dy", 2);
}

#[test]
fn bbs_with_ddh() {
    full_flow::<BbsBase, TagDDH>(b"test/bbs-ddh", 3);
}

#[test]
fn bbs_with_dy() {
    full_flow::<BbsBase, TagDY>(b"test/bbs-dy", 4);
}

/// Membership proofs on a message: bound to the message, to the helper key, and to nothing a
/// verifier did not compute itself.
fn membership<Bk: Backend>(label: &[u8], seed: u64) {
    let World {
        pcreds,
        helper,
        members,
        mut rng,
    } = world::<Bk>(label, seed);
    let hvk = helper.key().clone();
    let (user, cred) = &members[0];
    let proof = pcreds
        .prove(&hvk, user, cred, b"hello", &mut rng)
        .expect("prove");
    assert!(pcreds.verify(&hvk, b"hello", &proof));
    assert!(!pcreds.verify(&hvk, b"goodbye", &proof));
    // under another helper key
    let other = pcreds.helper_keygen(Policy::threshold(1).unwrap(), &mut rng);
    assert!(!pcreds.verify(other.key(), b"hello", &proof));
}

#[test]
fn membership_proofs_are_bound_to_message_and_key() {
    membership::<PairingBackend<E, PS, TagDDH>>(b"test/membership/ps", 8);
    membership::<PairingBackend<E, BbsBase, TagDY>>(b"test/membership/bbs", 9);
}

/// The sizes reported in the paper (BLS12-381, compressed group elements, compact proofs).
fn sizes<Bk: Backend>(label: &[u8], seed: u64) -> (usize, usize, usize, usize, usize) {
    use ark_serialize::CanonicalSerialize;
    let World {
        pcreds,
        helper,
        members,
        mut rng,
    } = world::<Bk>(label, seed);
    let hvk = helper.key().clone();
    let newcomer = pcreds.register(&hvk, &mut rng).expect("register");
    let attestations: Vec<_> = members
        .iter()
        .enumerate()
        .map(|(j, (member, cred))| {
            attestation(&pcreds, &hvk, (member, cred), &newcomer, j, &mut rng)
        })
        .collect();
    let att = attestations[0].size();
    let (message, _) = pcreds
        .request_credential(&hvk, &newcomer, attestations, b"s", &mut rng)
        .expect("request");
    let cred = members[0].1.as_inner().compressed_size();
    let proof = pcreds
        .prove(&hvk, &members[0].0, &members[0].1, b"m", &mut rng)
        .expect("prove")
        .size();
    (
        att,
        message.size(),
        cred,
        proof,
        newcomer.id().compressed_size(),
    )
}

#[test]
fn sizes_match_the_paper() {
    // Σ-PS: att = t (48) + (σ'_1, σ'_2) (96) + (c, z_usk, z_t) (96);
    // |π| = 5·att + Ĉ (48) + (c, z_usk, z_ρ) (96).
    let ps = sizes::<PairingBackend<E, PS, TagDDH>>(b"size/ps", 5);
    assert_eq!(ps, (240, 1344, 96, 192, 48));
    // Σ-BBS: att = t (48) + (Ā, B̄, D) (144) + (c, 7 responses) (256);
    // |π| = 5·att + Ĉ (48) + (c, z_usk, z_ρ) (96); cred = (A, e, ρ).
    let bbs = sizes::<PairingBackend<E, BbsBase, TagDDH>>(b"size/bbs", 6);
    assert_eq!(bbs, (448, 2384, 112, 400, 48));
    // the tag does not change any size
    assert_eq!(sizes::<PairingBackend<E, PS, TagDY>>(b"size/ps-dy", 10), ps);
    assert_eq!(
        sizes::<PairingBackend<E, BbsBase, TagDY>>(b"size/bbs-dy", 11),
        bbs
    );
}

#[test]
fn inadmissible_keys_and_non_members_are_refused() {
    type Bk = PairingBackend<E, PS, TagDDH>;
    let World {
        pcreds,
        helper,
        members,
        mut rng,
    } = world::<Bk>(b"test/negative", 7);
    // A PS key whose G1 and G2 halves disagree is not in V_pp.
    let mut bad = helper.key().vk().clone();
    bad.y1 += G1::generator();
    assert_eq!(pcreds.helper_key(&bad).err(), Some(Error::InvalidKey));
    assert!(pcreds.helper_key(helper.key().vk()).is_ok());
    // A credential that does not verify cannot be shown: the prover refuses the witness.
    let hvk = helper.key().clone();
    let newcomer = pcreds.register(&hvk, &mut rng).expect("register");
    let mut forged = members[0].1.as_inner().clone();
    forged.s2 += G1::generator();
    assert_eq!(
        pcreds.credential(&hvk, &members[0].0, forged).err(),
        Some(Error::InvalidCredential)
    );
    // a threshold of zero is no policy
    assert_eq!(Policy::threshold(0).err(), Some(Error::ZeroThreshold));
    let _ = newcomer;
}
