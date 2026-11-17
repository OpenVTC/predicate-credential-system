//! Application contexts (implementation note for OpenVTC, not in the paper):
//! `attest_in_context`, `check_attestation_in_context`, `verify_attestation_in_context`,
//! `request_credential_in_context` and `evaluate_request_in_context`, with the contexts of
//! `attestation_context_in` and `issuance_context_in`, through the public API only.
//!
//! What has to hold, for both pairing bases with `Tag_DDH`:
//!
//! * The round trip: attestations under their own contexts, a credential request under its own
//!   context, the helper's evaluation under the same contexts, issuance and `Unblind`.
//! * Binding: an attestation or a request verifies under the contexts it was made under and
//!   under no other, including "no context" (`None` and `Some(&[])` are different contexts).
//! * The requester cannot move an attestation to another context: an attestation that the
//!   helper evaluates under another context than its own does not count.
//! * Tags do not depend on the context: one attester for one recipient counts once, whatever
//!   contexts its attestations carry.
//! * Backward compatibility: without application contexts the Fiat–Shamir contexts are the
//!   paper's, byte for byte, and with them there is one context per attestation.
//!
//! All runs are seeded.

use ark_bls12_381::{Bls12_381, G1Projective};
use predicate_credential_system::{
    Error,
    hash::bls12_381::G1Hasher,
    kiprf::{DDH, ProtocolTag},
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
type BbsBase = BBS<G1Hasher>;

/// The threshold of the helper's policy, and the number of root members.
const K: usize = 3;

/// A deployment with a helper under `Pol_K` and `K` root members holding credentials.
struct World<Bk: Backend> {
    pcreds: Protocol<Bk>,
    helper: Helper<Bk>,
    hvk: HelperKey<Bk>,
    members: Vec<(User<Bk>, Credential<Bk>)>,
    rng: StdRng,
    /// A counter for fresh sub-session identifiers.
    sessions: u64,
}

impl<Bk: Backend> World<Bk> {
    fn new(label: &[u8], seed: u64) -> Self {
        let mut rng = StdRng::seed_from_u64(seed);
        let pcreds = Protocol::<Bk>::setup(label).expect("setup");
        let helper = pcreds.helper_keygen(Policy::threshold(K).expect("k ≥ 1"), &mut rng);
        let hvk = pcreds.helper_key(helper.key().vk()).expect("hvk ∈ V_pp");
        let mut world = Self {
            pcreds,
            helper,
            hvk,
            members: Vec::new(),
            rng,
            sessions: 0,
        };
        for _ in 0..K {
            let user = world.register();
            let ssid = world.ssid();
            let (message, state) = world
                .pcreds
                .request_credential(&world.hvk, &user, Vec::new(), &ssid, &mut world.rng)
                .expect("root request");
            let evaluated = world
                .pcreds
                .evaluate_request(&world.helper, &message, &ssid)
                .expect("evaluate");
            let Reply::PreCredential(pre) = world
                .pcreds
                .respond(&mut world.helper, evaluated, Decision::Root, &mut world.rng)
                .expect("root response")
            else {
                panic!("root admission must issue");
            };
            let cred = world
                .pcreds
                .unblind(&world.hvk, &user, &pre, state)
                .expect("unblind");
            world.members.push((user, cred));
        }
        world
    }

    fn ssid(&mut self) -> Vec<u8> {
        self.sessions += 1;
        format!("ssid-{}", self.sessions).into_bytes()
    }

    fn register(&mut self) -> User<Bk> {
        self.pcreds
            .register(&self.hvk, &mut self.rng)
            .expect("register")
    }

    /// An attestation from member `j` for `newcomer`, under the application context `app` if
    /// any, through `AttestationRequest` and `AttestationRequestResponse`.
    fn attestation(
        &mut self,
        j: usize,
        newcomer: &User<Bk>,
        app: Option<&[u8]>,
    ) -> Attestation<Bk> {
        let ssid = self.ssid();
        let contact = format!("member-{j}@example").into_bytes();
        let request = self
            .pcreds
            .request_attestation(&self.hvk, newcomer, &ssid, &contact, &mut self.rng)
            .expect("attestation request");
        let pending = self
            .pcreds
            .receive_attestation_request(&self.hvk, &request, &ssid, &contact)
            .expect("π_id");
        let (member, cred) = &self.members[j];
        match app {
            Some(app) => {
                self.pcreds
                    .attest_in_context(&self.hvk, member, cred, pending, app, &mut self.rng)
            }
            None => self
                .pcreds
                .attest(&self.hvk, member, cred, pending, &mut self.rng),
        }
        .expect("attest")
    }
}

/// The contexts `vetter/2026-11/{j}` of the attestations of the round trips.
fn att_apps(count: usize) -> Vec<Vec<u8>> {
    (0..count)
        .map(|j| format!("vetter/2026-11/{j}").into_bytes())
        .collect()
}

fn as_slices(apps: &[Vec<u8>]) -> Vec<&[u8]> {
    apps.iter().map(Vec::as_slice).collect()
}

fn round_trip<B: Base<E>, T: ProtocolTag<G1> + 'static>(label: &[u8], seed: u64) {
    let mut world = World::<PairingBackend<E, B, T>>::new(label, seed);
    let newcomer = world.register();
    let apps = att_apps(K);
    let attestations: Vec<_> = (0..K)
        .map(|j| world.attestation(j, &newcomer, Some(&apps[j])))
        .collect();
    for (att, app) in attestations.iter().zip(&apps) {
        assert_eq!(
            world
                .pcreds
                .check_attestation_in_context(&world.hvk, newcomer.id(), att, app),
            Ok(())
        );
        assert!(
            world
                .pcreds
                .verify_attestation_in_context(&world.hvk, newcomer.id(), att, app)
        );
    }
    let ssid = world.ssid();
    let audience = b"audience: vtc.example";
    let (message, state) = world
        .pcreds
        .request_credential_in_context(
            &world.hvk,
            &newcomer,
            attestations,
            &as_slices(&apps),
            &ssid,
            audience,
            &mut world.rng,
        )
        .expect("request");
    let evaluated = world
        .pcreds
        .evaluate_request_in_context(&world.helper, &message, &ssid, &as_slices(&apps), audience)
        .expect("evaluate");
    assert!(
        evaluated.is_valid(),
        "K distinct attesters under their contexts"
    );
    assert_eq!(evaluated.tags().len(), K);
    let Reply::PreCredential(pre) = world
        .pcreds
        .respond(
            &mut world.helper,
            evaluated,
            Decision::Policy,
            &mut world.rng,
        )
        .expect("respond")
    else {
        panic!("a valid request issues");
    };
    world
        .pcreds
        .unblind(&world.hvk, &newcomer, &pre, state)
        .expect("unblind");
}

#[test]
fn round_trip_under_application_contexts() {
    round_trip::<PS, TagDDH>(b"app-context/round-trip/ps", 1);
    round_trip::<BbsBase, TagDDH>(b"app-context/round-trip/bbs", 2);
}

fn attestation_binding<B: Base<E>, T: ProtocolTag<G1> + 'static>(label: &[u8], seed: u64) {
    let mut world = World::<PairingBackend<E, B, T>>::new(label, seed);
    let newcomer = world.register();
    let id = *newcomer.id();
    let in_app = world.attestation(0, &newcomer, Some(&b"window: 2026-11"[..]));
    let in_empty = world.attestation(1, &newcomer, Some(&b""[..]));
    let plain = world.attestation(2, &newcomer, None);
    let (pcreds, hvk) = (&world.pcreds, &world.hvk);
    // Its own context only.
    assert_eq!(
        pcreds.check_attestation_in_context(hvk, &id, &in_app, b"window: 2026-11"),
        Ok(())
    );
    for other in [&b"window: 2026-12"[..], &b""[..], &b"window: 2026-11 "[..]] {
        assert_eq!(
            pcreds.check_attestation_in_context(hvk, &id, &in_app, other),
            Err(Error::InvalidProof),
            "{other:?}"
        );
    }
    assert_eq!(
        pcreds.check_attestation(hvk, &id, &in_app),
        Err(Error::InvalidProof)
    );
    // The empty context is a context: not "no context".
    assert_eq!(
        pcreds.check_attestation_in_context(hvk, &id, &in_empty, b""),
        Ok(())
    );
    assert_eq!(
        pcreds.check_attestation(hvk, &id, &in_empty),
        Err(Error::InvalidProof)
    );
    // An attestation without context verifies without one and under none.
    assert_eq!(pcreds.check_attestation(hvk, &id, &plain), Ok(()));
    assert!(pcreds.verify_attestation(hvk, &id, &plain));
    assert!(!pcreds.verify_attestation_in_context(hvk, &id, &plain, b""));
    assert!(!pcreds.verify_attestation_in_context(hvk, &id, &plain, b"window: 2026-11"));
}

#[test]
fn attestations_verify_under_their_own_context_only() {
    attestation_binding::<PS, TagDDH>(b"app-context/attestation/ps", 3);
    attestation_binding::<BbsBase, TagDDH>(b"app-context/attestation/bbs", 4);
}

fn request_binding<B: Base<E>, T: ProtocolTag<G1> + 'static>(label: &[u8], seed: u64) {
    let mut world = World::<PairingBackend<E, B, T>>::new(label, seed);
    let newcomer = world.register();
    let apps = att_apps(K);
    let attestations: Vec<_> = (0..K)
        .map(|j| world.attestation(j, &newcomer, Some(&apps[j])))
        .collect();
    let ssid = world.ssid();
    let (message, _) = world
        .pcreds
        .request_credential_in_context(
            &world.hvk,
            &newcomer,
            attestations.clone(),
            &as_slices(&apps),
            &ssid,
            b"audience: a",
            &mut world.rng,
        )
        .expect("request");
    let (pcreds, helper) = (&world.pcreds, &world.helper);
    assert!(
        pcreds
            .evaluate_request_in_context(helper, &message, &ssid, &as_slices(&apps), b"audience: a")
            .expect("its own contexts")
            .is_valid()
    );
    // Another own context, another context of one attestation, or no contexts at all.
    let mut swapped = as_slices(&apps);
    swapped.swap(0, 1);
    let other: Vec<&[u8]> = vec![&b"vetter/2026-12/0"[..], &apps[1], &apps[2]];
    let cases: [(Vec<&[u8]>, &[u8]); 4] = [
        (as_slices(&apps), b"audience: b"),
        (as_slices(&apps), b""),
        (swapped, b"audience: a"),
        (other, b"audience: a"),
    ];
    for (att_apps, app) in cases {
        assert_eq!(
            pcreds
                .evaluate_request_in_context(helper, &message, &ssid, &att_apps, app)
                .err(),
            Some(Error::InvalidProof)
        );
    }
    assert_eq!(
        pcreds.evaluate_request(helper, &message, &ssid).err(),
        Some(Error::InvalidProof)
    );
    // A request made without contexts is refused under any.
    let ssid = world.ssid();
    let plain_atts: Vec<_> = (0..K)
        .map(|j| world.attestation(j, &newcomer, None))
        .collect();
    let (plain, _) = world
        .pcreds
        .request_credential(&world.hvk, &newcomer, plain_atts, &ssid, &mut world.rng)
        .expect("plain request");
    let empties: Vec<&[u8]> = vec![&b""[..]; K];
    assert_eq!(
        world
            .pcreds
            .evaluate_request_in_context(&world.helper, &plain, &ssid, &empties, b"")
            .err(),
        Some(Error::InvalidProof)
    );
    assert!(
        world
            .pcreds
            .evaluate_request(&world.helper, &plain, &ssid)
            .expect("no contexts")
            .is_valid()
    );
}

#[test]
fn requests_verify_under_their_own_contexts_only() {
    request_binding::<PS, TagDDH>(b"app-context/request/ps", 5);
    request_binding::<BbsBase, TagDDH>(b"app-context/request/bbs", 6);
}

fn moved_attestation<B: Base<E>, T: ProtocolTag<G1> + 'static>(label: &[u8], seed: u64) {
    let mut world = World::<PairingBackend<E, B, T>>::new(label, seed);
    let newcomer = world.register();
    let apps = att_apps(K);
    let mut attestations: Vec<_> = (0..K)
        .map(|j| world.attestation(j, &newcomer, Some(&apps[j])))
        .collect();
    // The last attestation was made under another context than the one the helper expects for
    // it. The requester proves under the helper's contexts, so π_iss verifies, but that
    // attestation does not count, and the policy rejects.
    attestations[K - 1] = world.attestation(K - 1, &newcomer, Some(&b"vetter/2025-01/stale"[..]));
    let ssid = world.ssid();
    let (message, _) = world
        .pcreds
        .request_credential_in_context(
            &world.hvk,
            &newcomer,
            attestations,
            &as_slices(&apps),
            &ssid,
            b"",
            &mut world.rng,
        )
        .expect("request");
    let evaluated = world
        .pcreds
        .evaluate_request_in_context(&world.helper, &message, &ssid, &as_slices(&apps), b"")
        .expect("π_iss verifies");
    assert_eq!(evaluated.tags().len(), K - 1);
    assert!(!evaluated.is_valid());
}

#[test]
fn an_attestation_under_another_context_does_not_count() {
    moved_attestation::<PS, TagDDH>(b"app-context/moved/ps", 7);
    moved_attestation::<BbsBase, TagDDH>(b"app-context/moved/bbs", 8);
}

fn tags_ignore_contexts<B: Base<E>, T: ProtocolTag<G1> + 'static>(label: &[u8], seed: u64) {
    let mut world = World::<PairingBackend<E, B, T>>::new(label, seed);
    let newcomer = world.register();
    let first = world.attestation(0, &newcomer, Some(&b"context one"[..]));
    let second = world.attestation(0, &newcomer, Some(&b"context two"[..]));
    let plain = world.attestation(0, &newcomer, None);
    assert_eq!(first.tag, second.tag);
    assert_eq!(first.tag, plain.tag);
    // K attestations, two of them from member 0 under different contexts: K - 1 attesters.
    let mut attestations = vec![first, second];
    let mut apps: Vec<Vec<u8>> = vec![b"context one".to_vec(), b"context two".to_vec()];
    for j in 1..K - 1 {
        let app = format!("context {j}").into_bytes();
        attestations.push(world.attestation(j, &newcomer, Some(&app)));
        apps.push(app);
    }
    let ssid = world.ssid();
    let (message, _) = world
        .pcreds
        .request_credential_in_context(
            &world.hvk,
            &newcomer,
            attestations,
            &as_slices(&apps),
            &ssid,
            b"",
            &mut world.rng,
        )
        .expect("request");
    let evaluated = world
        .pcreds
        .evaluate_request_in_context(&world.helper, &message, &ssid, &as_slices(&apps), b"")
        .expect("evaluate");
    assert_eq!(evaluated.tags().len(), K - 1, "member 0 counts once");
    assert!(!evaluated.is_valid());
}

#[test]
fn tags_do_not_depend_on_the_context() {
    tags_ignore_contexts::<PS, TagDDH>(b"app-context/tags/ps", 9);
    tags_ignore_contexts::<BbsBase, TagDDH>(b"app-context/tags/bbs", 10);
}

fn backward_compatible<B: Base<E>, T: ProtocolTag<G1> + 'static>(label: &[u8], seed: u64) {
    let mut world = World::<PairingBackend<E, B, T>>::new(label, seed);
    let newcomer = world.register();
    let atts: Vec<_> = (0..2)
        .map(|j| world.attestation(j, &newcomer, None))
        .collect();
    let (pcreds, vk) = (&world.pcreds, world.hvk.vk());
    // Without application contexts, the paper's contexts byte for byte.
    assert_eq!(
        pcreds.attestation_context_in(vk, None).unwrap(),
        pcreds.attestation_context(vk).unwrap()
    );
    assert_eq!(
        pcreds
            .issuance_context_in(vk, b"s", &atts, None, None)
            .unwrap(),
        pcreds.issuance_context(vk, b"s", &atts).unwrap()
    );
    // Every context is a different one: none, empty, and two others.
    let (empty, a, b): (&[u8], &[u8], &[u8]) = (b"", b"a", b"b");
    let att_contexts = [
        pcreds.attestation_context_in(vk, None).unwrap(),
        pcreds.attestation_context_in(vk, Some(empty)).unwrap(),
        pcreds.attestation_context_in(vk, Some(a)).unwrap(),
        pcreds.attestation_context_in(vk, Some(b)).unwrap(),
    ];
    let iss = |att_apps: Option<&[&[u8]]>, app: Option<&[u8]>| {
        pcreds
            .issuance_context_in(vk, b"s", &atts, att_apps, app)
            .unwrap()
    };
    let iss_contexts = [
        iss(None, None),
        iss(None, Some(empty)),
        iss(Some(&[empty, empty]), None),
        iss(Some(&[empty, empty]), Some(empty)),
        iss(Some(&[a, empty]), None),
        iss(Some(&[empty, a]), None),
    ];
    // With no attestations as well: an empty list of contexts is not the same as none.
    let iss0 = |att_apps: Option<&[&[u8]]>, app: Option<&[u8]>| {
        pcreds
            .issuance_context_in(vk, b"s", &[], att_apps, app)
            .unwrap()
    };
    let iss0_contexts = [
        iss0(None, None),
        iss0(Some(&[]), None),
        iss0(None, Some(empty)),
        iss0(Some(&[]), Some(empty)),
    ];
    assert_eq!(
        iss0(None, None),
        pcreds.issuance_context(vk, b"s", &[]).unwrap()
    );
    for contexts in [&att_contexts[..], &iss_contexts[..], &iss0_contexts[..]] {
        for (i, x) in contexts.iter().enumerate() {
            for y in &contexts[i + 1..] {
                assert_ne!(x, y);
            }
        }
    }
    // One application context per attestation, when there are any.
    let lengths: [&[&[u8]]; 3] = [&[], &[a], &[a, b, empty]];
    for apps in lengths {
        assert_eq!(
            pcreds.issuance_context_in(vk, b"s", &atts, Some(apps), None),
            Err(Error::LengthMismatch {
                expected: 2,
                actual: apps.len()
            })
        );
    }
    let ssid = world.ssid();
    assert!(matches!(
        world.pcreds.request_credential_in_context(
            &world.hvk,
            &newcomer,
            atts,
            &[&b"only one"[..]],
            &ssid,
            b"",
            &mut world.rng,
        ),
        Err(Error::LengthMismatch {
            expected: 2,
            actual: 1
        })
    ));
}

#[test]
fn without_application_contexts_the_contexts_are_the_papers() {
    backward_compatible::<PS, TagDDH>(b"app-context/compatible/ps", 11);
    backward_compatible::<BbsBase, TagDDH>(b"app-context/compatible/bbs", 12);
}
