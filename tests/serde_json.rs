//! The `serde` layer of the crate ([`predicate_credential_system::serialization`], cargo feature
//! `serde`, on in the tests through the dev-dependency of the crate on itself) through
//! `serde_json`, for every pairing-based base/tag pair:
//!
//! * the JSON SHAPES of the messages, an interface that consumers write schemas against:
//!   objects with camelCase members whose leaves are opaque multibase base58btc strings
//!   (prefix `z`) of the compressed canonical encoding of the leaf, and the reply as `"fail"`,
//!   `"issued"` or `{"preCredential": "z…"}`;
//! * round trips of every serializable object, and a complete join in which every message
//!   travels as JSON and is accepted by its receiver;
//! * the secrets (users, credentials, issuance states, signing keys) as opaque strings;
//! * strict decoding: unknown, missing and repeated members, other multibase bases, malformed
//!   points and scalars, leaves that are no strings, unknown reply variants.
//!
//! All runs are seeded (`StdRng::seed_from_u64`, the seed at each call site). The tests say
//! nothing about security; they pin an encoding.

#![allow(clippy::upper_case_acronyms)] // naming policy: see src/lib.rs

mod common;

use core::fmt::Debug;

use ark_bls12_381::{Fq, Fr, G1Affine};
use ark_ec::AffineRepr;
use ark_ff::{BigInteger, One, PrimeField};
use ark_serialize::CanonicalSerialize;
use common::{BBS, BaseTest, Bk, DDH, DY, Deployment, E, G1, PS, random_proof};
use predicate_credential_system::{
    Error,
    kiprf::ProtocolTag,
    pcreds::{
        Attestation, AttestationRequest, Backend, Credential, CredentialRequest, Decision,
        IssuanceState, MembershipProof, Policy, Protocol, PublicParameters, Reply, User,
        pairing::{BBSParams, BBSVerificationKey, PSVerificationKey, PairingParams},
    },
    serialization::{self, WireFormat},
    sigma::FSProof,
};
use rand::{SeedableRng, rngs::StdRng};
use serde::{Deserialize, Serialize, de::DeserializeOwned};
use serde_json::{Value, json};

/// The threshold of the deployments.
const K: usize = 2;

// ---------------------------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------------------------

/// `value` → JSON text → value, asserting equality; returns the JSON tree.
fn round_trip<V: Serialize + DeserializeOwned + PartialEq + Debug>(value: &V) -> Value {
    let text = serde_json::to_string(value).expect("to JSON");
    let back: V = serde_json::from_str(&text).expect("from JSON");
    assert_eq!(&back, value);
    serde_json::from_str(&text).expect("JSON text")
}

/// The value of a JSON tree, through its text (what travels).
fn parse<V: DeserializeOwned>(tree: &Value) -> Result<V, serde_json::Error> {
    serde_json::from_str(&tree.to_string())
}

/// An opaque value: ONE multibase base58btc string (prefix `z`) of the compressed canonical
/// encoding `bytes`.
fn assert_opaque(tree: &Value, bytes: &[u8]) {
    let text = tree.as_str().expect("an opaque value is a JSON string");
    assert!(
        text.starts_with('z'),
        "multibase base58btc has the prefix z"
    );
    assert_eq!(
        serialization::from_multibase(text).expect("multibase"),
        bytes
    );
    assert_eq!(text, serialization::to_multibase(bytes));
}

/// A structured value: an object with exactly these members.
fn assert_members(tree: &Value, members: &[&str]) {
    let object = tree
        .as_object()
        .expect("a structured value is a JSON object");
    let mut found: Vec<&str> = object.keys().map(String::as_str).collect();
    let mut expected = members.to_vec();
    found.sort_unstable();
    expected.sort_unstable();
    assert_eq!(found, expected);
}

/// The JSON form of a secret: one opaque string of its wiped encoding `bytes`. Returns the
/// JSON text, which is as secret as the value.
fn secret_json<V: Serialize>(value: &V, bytes: &[u8]) -> String {
    let text = serde_json::to_string(value).expect("to JSON");
    assert_opaque(&serde_json::from_str(&text).expect("JSON text"), bytes);
    text
}

/// `{"tag", "show", "proof"}`, each leaf the multibase text of the canonical encoding of the
/// field.
fn assert_attestation<Bk: Backend>(tree: &Value, att: &Attestation<Bk>) {
    assert_members(tree, &["tag", "show", "proof"]);
    assert_opaque(&tree["tag"], &att.tag.to_bytes().unwrap());
    assert_opaque(&tree["show"], &att.show.to_bytes().unwrap());
    assert_opaque(&tree["proof"], &att.proof.to_bytes().unwrap());
}

/// Lower-case hexadecimal.
fn hex(bytes: &[u8]) -> String {
    use core::fmt::Write as _;
    let mut text = String::with_capacity(2 * bytes.len());
    for byte in bytes {
        write!(text, "{byte:02x}").expect("writing to a String");
    }
    text
}

/// Multibase base64url (prefix `u`, no padding), by hand: `multibase` is not a dependency of
/// the tests.
fn base64url(bytes: &[u8]) -> String {
    const ALPHABET: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";
    let mut out = String::from("u");
    for chunk in bytes.chunks(3) {
        let n = chunk
            .iter()
            .enumerate()
            .fold(0u32, |acc, (i, b)| acc | (u32::from(*b) << (16 - 8 * i)));
        for i in 0..=chunk.len() {
            out.push(char::from(ALPHABET[((n >> (18 - 6 * i)) & 63) as usize]));
        }
    }
    out
}

/// The same bytes under other multibase bases than base58btc: each is a valid multibase text
/// (the module refuses it for its base, not for its syntax), and each is refused.
fn other_bases(text: &str, bytes: &[u8]) -> Vec<(&'static str, String)> {
    let others = vec![
        ("base16", format!("f{}", hex(bytes))),
        ("base16 upper", format!("F{}", hex(bytes).to_uppercase())),
        ("base64url", base64url(bytes)),
        // the base58btc digits read under the flickr alphabet (the same characters)
        ("base58flickr", format!("Z{}", &text[1..])),
    ];
    for (base, other) in &others {
        let Err(Error::Serialization(reason)) = serialization::from_multibase(other) else {
            panic!("{base}: accepted by from_multibase");
        };
        assert!(reason.contains("is not accepted"), "{base}: {reason}");
    }
    others
}

/// Leaves that are not the strict form of the leaf `text` (the base58btc text of `bytes`).
fn malformed_leaves(text: &str, bytes: &[u8]) -> Vec<(&'static str, Value)> {
    let mut leaves: Vec<(&'static str, Value)> = other_bases(text, bytes)
        .into_iter()
        .map(|(base, other)| (base, json!(other)))
        .collect();
    leaves.extend([
        ("not multibase", json!("not multibase")),
        ("a leading space", json!(format!(" {text}"))),
        ("a trailing space", json!(format!("{text} "))),
        (
            "a trailing byte",
            json!(serialization::to_multibase(&[bytes, &[0]].concat())),
        ),
        (
            "a byte short",
            json!(serialization::to_multibase(&bytes[..bytes.len() - 1])),
        ),
        ("no bytes", json!("z")),
        ("the empty string", json!("")),
        ("a number", json!(1)),
        ("null", json!(null)),
        ("an array", json!([text])),
        ("an object", json!({ "z": text })),
    ]);
    leaves
}

/// The canonical encoding of the identity of `G_1`, and 48-byte strings that are no valid
/// compressed `G_1` element.
fn malformed_g1() -> Vec<(&'static str, Vec<u8>)> {
    let off_curve = (1u64..)
        .map(Fq::from)
        .find(|x| G1Affine::get_point_from_x_unchecked(*x, false).is_none())
        .expect("an abscissa off the curve");
    let mut off_curve = off_curve.into_bigint().to_bytes_be();
    off_curve[0] |= 0x80; // the compression flag
    let outside = (1u64..)
        .filter_map(|x| G1Affine::get_point_from_x_unchecked(Fq::from(x), false))
        .find(|p| !p.is_in_correct_subgroup_assuming_on_curve())
        .expect("a point outside the subgroup");
    let mut uncompressed = Vec::new();
    G1Affine::generator()
        .serialize_uncompressed(&mut uncompressed)
        .unwrap();
    vec![
        ("all zero", vec![0; 48]),
        ("half an uncompressed point", uncompressed[..48].to_vec()),
        ("an abscissa off the curve", off_curve),
        (
            "a point outside the prime-order subgroup",
            outside.to_bytes().unwrap(),
        ),
    ]
}

/// `bytes` with `replacement` written at `at`.
fn patched(bytes: &[u8], at: usize, replacement: &[u8]) -> Vec<u8> {
    let mut out = bytes.to_vec();
    out[at..at + replacement.len()].copy_from_slice(replacement);
    out
}

/// The opaque leaf `tree[member]` with `replacement` written into its bytes at `at`.
fn patched_leaf(tree: &Value, member: &str, at: usize, replacement: &[u8]) -> Value {
    let bytes = serialization::from_multibase(tree[member].as_str().unwrap()).unwrap();
    let mut out = tree.clone();
    out[member] = json!(serialization::to_multibase(&patched(
        &bytes,
        at,
        replacement
    )));
    out
}

/// What a consumer that is generic over the backend stores of a join, with the adapters of the
/// module (module docs of `serialization`, "Code that is generic over the base or the tag").
#[derive(Serialize, Deserialize)]
#[serde(bound = "", deny_unknown_fields)]
struct Stored<Bk: Backend> {
    #[serde(with = "predicate_credential_system::serialization::canonical")]
    pre_credential: Bk::PreCredential,
    #[serde(with = "predicate_credential_system::serialization::secret")]
    credential: Bk::Credential,
}

// ---------------------------------------------------------------------------------------------
// A join that travels as JSON
// ---------------------------------------------------------------------------------------------

/// A complete join in which every object that leaves a party is JSON: `pp` and `hvk`, the
/// attestation requests and attestations, the credential request, the reply, the membership
/// proof; and what the parties keep (the requester's key, state and credential, the helper's
/// record and signing key) is stored as JSON. Every receiver accepts what it decoded.
fn join<B, T>(label: &[u8], seed: u64)
where
    B: BaseTest,
    B::VerificationKey: Serialize + DeserializeOwned,
    B::SigningKey: Serialize + DeserializeOwned,
    B::PreCredential: Serialize + DeserializeOwned,
    B::Credential: Serialize + DeserializeOwned,
    B::Show: Serialize + DeserializeOwned,
    T: ProtocolTag<G1> + Serialize + DeserializeOwned + 'static,
{
    let mut d = Deployment::<B, T>::new(label, K, seed);

    // ----- what the deployment publishes: pp and hvk, opaque ---------------------------------
    let pp = d.pcreds.public_parameters();
    let tree = round_trip(pp);
    assert_opaque(&tree, &pp.to_bytes().unwrap());
    // the requester rebuilds the protocol from the pp it received as JSON
    let received: PublicParameters<Bk<B, T>> = parse(&tree).unwrap();
    let pcreds = Protocol::from_public_parameters(received).expect("pp from JSON");
    assert_eq!(pcreds.parameters_digest(), d.pcreds.parameters_digest());
    let params = d.pcreds.params();
    assert_opaque(&round_trip(params), &params.to_bytes().unwrap());
    assert_opaque(&round_trip(&params.tag), &params.tag.to_bytes().unwrap());
    let vk = d.helper.key().vk().clone();
    let tree = round_trip(&vk);
    assert_opaque(&tree, &vk.to_bytes().unwrap());
    let hvk = pcreds
        .helper_key(&parse(&tree).unwrap())
        .expect("hvk from JSON");

    // ----- the requester; its key is kept as a secret ------------------------------------------
    let user = pcreds.register(&hvk, &mut d.rng).unwrap();
    let text = secret_json(&user, &user.to_bytes().unwrap());
    let user: User<Bk<B, T>> = serde_json::from_str(&text).unwrap();
    pcreds.check_user(&hvk, &user).expect("user from JSON");
    assert!(!format!("{user:?}").contains(text.trim_matches('"')));

    // ----- attestation requests and attestations -------------------------------------------------
    let mut attestations = Vec::new();
    for j in 0..K {
        let (ssid, contact) = (
            format!("json/att-{j}").into_bytes(),
            format!("member-{j}@example").into_bytes(),
        );
        let request = pcreds
            .request_attestation(&hvk, &user, &ssid, &contact, &mut d.rng)
            .unwrap();
        let tree = round_trip(&request);
        assert_members(&tree, &["id", "proof"]);
        assert_opaque(&tree["id"], &request.id.to_bytes().unwrap());
        assert_opaque(&tree["proof"], &request.proof.to_bytes().unwrap());
        // the member receives it as JSON, checks π_id, and attests
        let pending = d
            .pcreds
            .receive_attestation_request(&d.hvk, &parse(&tree).unwrap(), &ssid, &contact)
            .expect("π_id from JSON");
        let member = &d.members[j];
        let att = d
            .pcreds
            .attest(&d.hvk, &member.user, &member.cred, pending, &mut d.rng)
            .unwrap();
        let tree = round_trip(&att);
        assert_attestation(&tree, &att);
        // the show is the JSON form of the base's show on its own
        assert_eq!(tree["show"], round_trip(&att.show));
        // the requester receives the attestation as JSON and checks it
        let att: Attestation<Bk<B, T>> = parse(&tree).unwrap();
        pcreds
            .check_attestation(&hvk, user.id(), &att)
            .expect("π_att from JSON");
        attestations.push(att);
    }

    // ----- the credential request, and the reply -------------------------------------------------
    let ssid = b"json/request".to_vec();
    let (request, state) = pcreds
        .request_credential(&hvk, &user, attestations, &ssid, &mut d.rng)
        .unwrap();
    let tree = round_trip(&request);
    assert_members(&tree, &["id", "attestations", "request", "proof"]);
    assert_opaque(&tree["id"], &request.id.to_bytes().unwrap());
    assert_opaque(&tree["request"], &request.request.to_bytes().unwrap());
    assert_opaque(&tree["proof"], &request.proof.to_bytes().unwrap());
    assert_eq!(tree["request"], round_trip(&request.request));
    let listed = tree["attestations"]
        .as_array()
        .expect("the attestations are an array");
    assert_eq!(listed.len(), K);
    for (leaf, att) in listed.iter().zip(&request.attestations) {
        assert_attestation(leaf, att);
    }
    // the requester keeps its state, as a secret, until the helper answers
    let stored = secret_json(&state, &state.to_bytes().unwrap());
    drop(state);
    // the helper receives the request as JSON
    let received: CredentialRequest<Bk<B, T>> = parse(&tree).unwrap();
    let evaluated = d
        .pcreds
        .evaluate_request(&d.helper, &received, &ssid)
        .expect("π_iss from JSON");
    assert!(evaluated.is_valid());
    let reply = d
        .pcreds
        .respond(&mut d.helper, evaluated, Decision::Policy, &mut d.rng)
        .unwrap();
    let tree = round_trip(&reply);
    assert_members(&tree, &["preCredential"]);
    let Reply::PreCredential(pre) = &reply else {
        panic!("a valid request is issued");
    };
    assert_opaque(&tree["preCredential"], &pre.to_bytes().unwrap());
    assert_eq!(tree["preCredential"], round_trip(pre));
    // the requester: the reply and the stored state, both from JSON, give the credential
    let Reply::PreCredential(pre) = parse::<Reply<Bk<B, T>>>(&tree).unwrap() else {
        panic!("the reply is σ̂");
    };
    let state: IssuanceState<Bk<B, T>> = serde_json::from_str(&stored).unwrap();
    let cred = pcreds
        .unblind(&hvk, &user, &pre, state)
        .expect("unblind from JSON");

    // ----- what the requester keeps: the credential, as a secret ---------------------------------
    let text = secret_json(&cred, &cred.to_bytes().unwrap());
    assert!(!format!("{cred:?}").contains(text.trim_matches('"')));
    let cred: Credential<Bk<B, T>> = serde_json::from_str(&text).unwrap();
    assert!(pcreds.verify_credential(&hvk, &user, &cred));
    // the credential of the base on its own (Σ-PS: a pair, public type; Σ-BBS: a secret)
    let inner = serde_json::to_value(cred.as_inner()).unwrap();
    assert_opaque(&inner, &cred.as_inner().to_bytes().unwrap());
    assert!(parse::<B::Credential>(&inner).unwrap() == *cred.as_inner());
    // generic code stores σ̂ and σ through the adapters
    let generic = serde_json::to_value(Stored::<Bk<B, T>> {
        pre_credential: pre.clone(),
        credential: cred.as_inner().clone(),
    })
    .unwrap();
    assert_members(&generic, &["pre_credential", "credential"]);
    assert_opaque(&generic["pre_credential"], &pre.to_bytes().unwrap());
    assert_opaque(&generic["credential"], &cred.to_bytes().unwrap());
    let back: Stored<Bk<B, T>> = parse(&generic).unwrap();
    assert!(back.pre_credential == pre && back.credential == *cred.as_inner());

    // ----- the other replies: "issued" for the same request, "fail" for an empty one -----------
    let evaluated = d
        .pcreds
        .evaluate_request(&d.helper, &received, &ssid)
        .unwrap();
    let issued = d
        .pcreds
        .respond(&mut d.helper, evaluated, Decision::Policy, &mut d.rng)
        .unwrap();
    assert_eq!(round_trip(&issued), json!("issued"));
    let newcomer = pcreds.register(&hvk, &mut d.rng).unwrap();
    let (empty, _) = pcreds
        .request_credential(&hvk, &newcomer, Vec::new(), b"json/empty", &mut d.rng)
        .unwrap();
    let tree = round_trip(&empty);
    assert_eq!(tree["attestations"], json!([]));
    let evaluated = d
        .pcreds
        .evaluate_request(&d.helper, &parse(&tree).unwrap(), b"json/empty")
        .unwrap();
    let fail = d
        .pcreds
        .respond(&mut d.helper, evaluated, Decision::Policy, &mut d.rng)
        .unwrap();
    assert_eq!(round_trip(&fail), json!("fail"));

    // ----- anonymous use: a membership proof -----------------------------------------------------
    let proof = pcreds
        .prove(&hvk, &user, &cred, b"hello", &mut d.rng)
        .unwrap();
    let tree = round_trip(&proof);
    assert_members(&tree, &["show", "proof"]);
    assert_opaque(&tree["show"], &proof.show.to_bytes().unwrap());
    assert_opaque(&tree["proof"], &proof.proof.to_bytes().unwrap());
    let proof: MembershipProof<Bk<B, T>> = parse(&tree).unwrap();
    assert!(d.pcreds.verify(&d.hvk, b"hello", &proof));

    // ----- what the helper keeps: its record (opaque) and its signing key (secret) --------------
    let record = d.helper.store();
    assert_opaque(&round_trip(record), &record.to_bytes().unwrap());
    // pp-digest ‖ hvk ‖ sk
    let key = d.helper.to_bytes().unwrap();
    let at = 32 + vk.to_bytes().unwrap().len();
    let sk = <B::SigningKey as WireFormat>::from_bytes(&key[at..]).unwrap();
    let text = secret_json(&sk, &key[at..]);
    assert!(format!("{sk:?}").contains("<redacted>"));
    assert!(!format!("{sk:?}").contains(text.trim_matches('"')));
    let sk: B::SigningKey = serde_json::from_str(&text).unwrap();
    let restored = [&key[..at], &sk.to_bytes().unwrap()[..]].concat();
    let helper = d
        .pcreds
        .restore_helper(&restored, *d.helper.policy(), record.clone())
        .expect("a helper with the signing key from JSON");
    assert_eq!(helper.key(), d.helper.key());
}

#[test]
fn json_join_ps_ddh() {
    join::<PS, DDH>(b"serde/ps+ddh", 0x5e7d_0001);
}

#[test]
fn json_join_ps_dy() {
    join::<PS, DY>(b"serde/ps+dy", 0x5e7d_0002);
}

#[test]
fn json_join_bbs_ddh() {
    join::<BBS, DDH>(b"serde/bbs+ddh", 0x5e7d_0003);
}

#[test]
fn json_join_bbs_dy() {
    join::<BBS, DY>(b"serde/bbs+dy", 0x5e7d_0004);
}

/// The parameters and keys of the bases and tags by name: opaque, each the multibase text of
/// its canonical encoding.
#[test]
fn base_types_are_opaque() {
    let mut rng = StdRng::seed_from_u64(0x5e7d_0005);
    let policy = Policy::threshold(1).unwrap();
    let ps = Protocol::<Bk<PS, DDH>>::setup(b"serde/types/ps").unwrap();
    let params: &PairingParams<E, PS, DDH> = ps.params();
    assert_opaque(&round_trip(params), &params.to_bytes().unwrap());
    let tag: &DDH = &params.tag;
    assert_opaque(&round_trip(tag), &tag.to_bytes().unwrap());
    let helper = ps.helper_keygen(policy, &mut rng);
    let vk: &PSVerificationKey<E> = helper.key().vk();
    assert_opaque(&round_trip(vk), &vk.to_bytes().unwrap());

    let bbs = Protocol::<Bk<BBS, DY>>::setup(b"serde/types/bbs").unwrap();
    let params: &PairingParams<E, BBS, DY> = bbs.params();
    assert_opaque(&round_trip(params), &params.to_bytes().unwrap());
    let base: &BBSParams<E> = &params.base;
    assert_opaque(&round_trip(base), &base.to_bytes().unwrap());
    let tag: &DY = &params.tag;
    assert_opaque(&round_trip(tag), &tag.to_bytes().unwrap());
    let helper = bbs.helper_keygen(policy, &mut rng);
    let vk: &BBSVerificationKey<E> = helper.key().vk();
    assert_opaque(&round_trip(vk), &vk.to_bytes().unwrap());
}

// ---------------------------------------------------------------------------------------------
// Strict decoding
// ---------------------------------------------------------------------------------------------

/// Decoding a structured message accepts exactly what encoding produces: its members and no
/// others, each once, each leaf the base58btc text of a canonical encoding.
fn structured<V: DeserializeOwned + Debug>(tree: &Value, members: &[&str]) {
    let name = core::any::type_name::<V>();
    let refused = |t: &Value, what: &str| {
        assert!(parse::<V>(t).is_err(), "{name}: {what} accepted");
    };
    parse::<V>(tree).expect("control: the encoding decodes");
    assert_members(tree, members);
    // an unknown member, also a near miss of a real one
    for unknown in ["issuer", "Proof", "proofValue", "pre_credential"] {
        let mut t = tree.clone();
        t[unknown] = tree[members[0]].clone();
        refused(&t, unknown);
    }
    // a repeated member (an object TEXT can repeat a key, a `Value` cannot)
    let first = members[0];
    let repeated = tree
        .to_string()
        .replacen('{', &format!("{{\"{first}\":{},", tree[first]), 1);
    assert!(
        serde_json::from_str::<V>(&repeated).is_err(),
        "{name}: a repeated member accepted"
    );
    // the wrong JSON type for the whole message
    for t in [json!(null), json!(1), json!("z"), json!([])] {
        refused(&t, "not an object");
    }
    for member in members {
        let mut t = tree.clone();
        t.as_object_mut().unwrap().remove(*member);
        refused(&t, &format!("{member} missing"));
        // the attestations of a credential request are an array, every other member a leaf
        let Some(text) = tree[*member].as_str() else {
            continue;
        };
        let bytes = serialization::from_multibase(text).unwrap();
        for (what, leaf) in malformed_leaves(text, &bytes) {
            let mut t = tree.clone();
            t[*member] = leaf;
            refused(&t, &format!("{member}: {what}"));
        }
    }
}

/// A reply is `"fail"`, `"issued"` or `{"preCredential": "z…"}`, spelled exactly so.
fn reply_variants<Bk: Backend>(pre: &Value) {
    let refused = |t: Value| {
        assert!(parse::<Reply<Bk>>(&t).is_err(), "{t} accepted");
    };
    for t in [json!("fail"), json!("issued"), pre.clone()] {
        parse::<Reply<Bk>>(&t).expect("control");
    }
    for t in [
        json!("Fail"),
        json!("FAIL"),
        json!("failed"),
        json!("Issued"),
        json!("pending"),
        json!(""),
        json!("preCredential"),
        json!(0),
        json!(null),
        json!([]),
        json!({}),
    ] {
        refused(t);
    }
    let leaf = &pre["preCredential"];
    for t in [
        json!({ "PreCredential": leaf.clone() }),
        json!({ "pre_credential": leaf.clone() }),
        json!({ "preCredential": leaf.clone(), "fail": null }),
        json!({ "preCredential": null }),
        json!({ "preCredential": 1 }),
        json!({ "preCredential": [leaf.clone()] }),
        json!({ "issued": leaf.clone() }),
    ] {
        refused(t);
    }
    // the leaf itself is strict
    let text = leaf.as_str().unwrap();
    let bytes = serialization::from_multibase(text).unwrap();
    for (what, bad) in malformed_leaves(text, &bytes) {
        assert!(
            parse::<Reply<Bk>>(&json!({ "preCredential": bad })).is_err(),
            "σ̂: {what} accepted"
        );
    }
}

/// The messages of one join under `Pol_1`, as JSON, refused in every malformed variant.
fn strict<B: BaseTest, T: ProtocolTag<G1> + 'static>(label: &[u8], seed: u64) {
    let mut d = Deployment::<B, T>::new(label, 1, seed);
    let user = d.register();
    let request = d
        .pcreds
        .request_attestation(&d.hvk, &user, b"ssid", b"contact", &mut d.rng)
        .unwrap();
    let att = d.attestation(0, &user);
    let (message, _) = d
        .pcreds
        .request_credential(&d.hvk, &user, vec![att.clone()], b"strict", &mut d.rng)
        .unwrap();
    let evaluated = d
        .pcreds
        .evaluate_request(&d.helper, &message, b"strict")
        .unwrap();
    let reply = d
        .pcreds
        .respond(&mut d.helper, evaluated, Decision::Policy, &mut d.rng)
        .unwrap();
    let member = &d.members[0];
    let proof = d
        .pcreds
        .prove(&d.hvk, &member.user, &member.cred, b"m", &mut d.rng)
        .unwrap();

    let request_tree = serde_json::to_value(&request).unwrap();
    let att_tree = serde_json::to_value(&att).unwrap();
    let message_tree = serde_json::to_value(&message).unwrap();
    let reply_tree = serde_json::to_value(&reply).unwrap();
    let proof_tree = serde_json::to_value(&proof).unwrap();
    structured::<AttestationRequest<Bk<B, T>>>(&request_tree, &["id", "proof"]);
    structured::<Attestation<Bk<B, T>>>(&att_tree, &["tag", "show", "proof"]);
    structured::<CredentialRequest<Bk<B, T>>>(
        &message_tree,
        &["id", "attestations", "request", "proof"],
    );
    structured::<MembershipProof<Bk<B, T>>>(&proof_tree, &["show", "proof"]);
    reply_variants::<Bk<B, T>>(&reply_tree);
    // an attestation inside a credential request is held to the same form
    let mut t = message_tree.clone();
    t["attestations"][0]["issuer"] = json!("did:example:attester");
    assert!(parse::<CredentialRequest<Bk<B, T>>>(&t).is_err());
    let mut t = message_tree.clone();
    t["attestations"] = json!(att_tree["tag"]);
    assert!(parse::<CredentialRequest<Bk<B, T>>>(&t).is_err());

    // invalid points: a malformed G_1 element as a tag, an identifier, a request, and as the
    // first element of a show and of σ̂
    for (what, bad) in malformed_g1() {
        let leaf = json!(serialization::to_multibase(&bad));
        let mut t = att_tree.clone();
        t["tag"] = leaf.clone();
        assert!(parse::<Attestation<Bk<B, T>>>(&t).is_err(), "t: {what}");
        let t = patched_leaf(&att_tree, "show", 0, &bad);
        assert!(parse::<Attestation<Bk<B, T>>>(&t).is_err(), "σ*: {what}");
        let mut t = request_tree.clone();
        t["id"] = leaf.clone();
        assert!(
            parse::<AttestationRequest<Bk<B, T>>>(&t).is_err(),
            "id_Q: {what}"
        );
        let mut t = message_tree.clone();
        t["request"] = leaf.clone();
        assert!(
            parse::<CredentialRequest<Bk<B, T>>>(&t).is_err(),
            "Ĉ: {what}"
        );
        let mut t = message_tree.clone();
        t["attestations"][0]["tag"] = leaf;
        assert!(
            parse::<CredentialRequest<Bk<B, T>>>(&t).is_err(),
            "a tag inside the request: {what}"
        );
        let t = patched_leaf(&reply_tree, "preCredential", 0, &bad);
        assert!(parse::<Reply<Bk<B, T>>>(&t).is_err(), "σ̂: {what}");
        let t = patched_leaf(&proof_tree, "show", 0, &bad);
        assert!(
            parse::<MembershipProof<Bk<B, T>>>(&t).is_err(),
            "the show of a membership proof: {what}"
        );
    }
    // non-canonical scalars in a proof leaf (n ‖ c ‖ z, big-endian scalars): c = r,
    // c = 2^256 − 1, z_1 = r
    let modulus = Fr::MODULUS.to_bytes_be();
    for (at, bad) in [(8, &modulus[..]), (8, &[0xff; 32][..]), (40, &modulus[..])] {
        let t = patched_leaf(&att_tree, "proof", at, bad);
        assert!(
            parse::<Attestation<Bk<B, T>>>(&t).is_err(),
            "scalar at {at}"
        );
    }

    // A well-formed but tampered attestation decodes, and the VERIFIER rejects it; so does a
    // proof with one response too few, whose JSON form (the self-describing encoding) decodes
    // and which has no compact encoding.
    let mut tampered = att.clone();
    tampered.proof.challenge += Fr::one();
    let tampered: Attestation<Bk<B, T>> = parse(&round_trip(&tampered)).unwrap();
    assert_eq!(
        d.pcreds.check_attestation(&d.hvk, user.id(), &tampered),
        Err(Error::InvalidProof)
    );
    let mut short = att.clone();
    short.proof.responses.pop();
    let short: Attestation<Bk<B, T>> = parse(&round_trip(&short)).unwrap();
    assert_eq!(
        d.pcreds.check_attestation(&d.hvk, user.id(), &short),
        Err(Error::InvalidProof)
    );
    assert!(matches!(
        short.to_compact_bytes(),
        Err(Error::LengthMismatch { .. })
    ));
}

#[test]
fn decoding_is_strict_ps_ddh() {
    strict::<PS, DDH>(b"serde/strict/ps+ddh", 0x5e7d_0010);
}

#[test]
fn decoding_is_strict_bbs_dy() {
    strict::<BBS, DY>(b"serde/strict/bbs+dy", 0x5e7d_0011);
}

/// The secrets are opaque strings, refused when malformed; a decoded secret is checked by the
/// protocol, not by the decoder (`check_user`).
#[test]
fn secrets_are_strict() {
    let mut d = Deployment::<PS, DDH>::new(b"serde/secrets", 1, 0x5e7d_0012);
    let user = d.register();
    let text = serde_json::to_string(&user).unwrap();
    let tree: Value = serde_json::from_str(&text).unwrap();
    let leaf = tree.as_str().unwrap();
    let bytes = serialization::from_multibase(leaf).unwrap();
    for (what, bad) in malformed_leaves(leaf, &bytes) {
        assert!(
            parse::<User<Bk<PS, DDH>>>(&bad).is_err(),
            "user: {what} accepted"
        );
    }
    // a structured form of a secret is refused
    assert!(parse::<User<Bk<PS, DDH>>>(&json!({ "usk": leaf })).is_err());
    // another user's identifier under this key: decodes, and the protocol refuses it
    let other = d.members[0].user.id().to_bytes().unwrap();
    let alien = json!(serialization::to_multibase(&patched(&bytes, 32, &other)));
    let alien: User<Bk<PS, DDH>> = parse(&alien).unwrap();
    assert_eq!(
        d.pcreds.check_user(&d.hvk, &alien),
        Err(Error::IdentifierMismatch)
    );

    let cred = &d.members[0].cred;
    let tree = serde_json::to_value(cred).unwrap();
    let leaf = tree.as_str().unwrap();
    let bytes = serialization::from_multibase(leaf).unwrap();
    for (what, bad) in malformed_leaves(leaf, &bytes) {
        assert!(
            parse::<Credential<Bk<PS, DDH>>>(&bad).is_err(),
            "credential: {what} accepted"
        );
    }
    let (_, state) = d
        .pcreds
        .request_credential(&d.hvk, &user, Vec::new(), b"s", &mut d.rng)
        .unwrap();
    let tree = serde_json::to_value(&state).unwrap();
    let leaf = tree.as_str().unwrap();
    let bytes = serialization::from_multibase(leaf).unwrap();
    for (what, bad) in malformed_leaves(leaf, &bytes) {
        assert!(
            parse::<IssuanceState<Bk<PS, DDH>>>(&bad).is_err(),
            "state: {what} accepted"
        );
    }
}

/// "One object therefore has one JSON form, as it has one binary form" (module docs of
/// `serialization`, "Strictness"). serde's derived decoders would also accept a struct as an
/// ARRAY of its fields in order, and serde_json a unit variant as a single-entry map with the
/// value `null`; neither form is produced by encoding, and the hand-written decoders of the
/// messages refuse both.
#[test]
fn every_object_has_one_json_form() {
    type P = Bk<PS, DDH>;
    let mut d = Deployment::<PS, DDH>::new(b"serde/one-form", 1, 0x5e7d_0013);
    let user = d.register();
    let request = d
        .pcreds
        .request_attestation(&d.hvk, &user, b"ssid", b"contact", &mut d.rng)
        .unwrap();
    let att = d.attestation(0, &user);
    let (message, _) = d
        .pcreds
        .request_credential(&d.hvk, &user, vec![att.clone()], b"one-form", &mut d.rng)
        .unwrap();
    let member = &d.members[0];
    let proof = d
        .pcreds
        .prove(&d.hvk, &member.user, &member.cred, b"m", &mut d.rng)
        .unwrap();
    // each message as the array of its members, in the order of its fields
    fn as_array<V: Serialize>(value: &V, fields: &[&str]) -> Value {
        let tree = serde_json::to_value(value).unwrap();
        Value::Array(fields.iter().map(|field| tree[*field].clone()).collect())
    }
    let mut accepted = Vec::new();
    let mut check = |what: &str, accepted_as_itself: bool, form: &Value| {
        if accepted_as_itself {
            accepted.push(format!("{what} as {form}"));
        }
    };
    let form = as_array(&request, &["id", "proof"]);
    check(
        "an attestation request",
        parse::<AttestationRequest<P>>(&form).is_ok_and(|back| back == request),
        &form,
    );
    let form = as_array(&att, &["tag", "show", "proof"]);
    check(
        "an attestation",
        parse::<Attestation<P>>(&form).is_ok_and(|back| back == att),
        &form,
    );
    let form = as_array(&message, &["id", "attestations", "request", "proof"]);
    check(
        "a credential request",
        parse::<CredentialRequest<P>>(&form).is_ok_and(|back| back == message),
        &form,
    );
    let form = as_array(&proof, &["show", "proof"]);
    check(
        "a membership proof",
        parse::<MembershipProof<P>>(&form).is_ok_and(|back| back == proof),
        &form,
    );
    for (form, reply) in [
        (json!({ "fail": null }), Reply::<P>::Fail),
        (json!({ "issued": null }), Reply::<P>::Issued),
    ] {
        check(
            &format!("{reply:?}"),
            parse::<Reply<P>>(&form).is_ok_and(|back| back == reply),
            &form,
        );
    }
    assert!(
        accepted.is_empty(),
        "forms that encoding never produces: {accepted:#?}"
    );
}

// ---------------------------------------------------------------------------------------------
// FSProof, and the predicates of the earlier construction
// ---------------------------------------------------------------------------------------------

/// A stand-alone Fiat–Shamir proof is one opaque string of its self-describing derived
/// encoding `n ‖ c ‖ z` (`n` a little-endian `u64`, then the NARG string). It decodes whatever
/// its number of responses (the statement decides whether that is right, as for the compact
/// codec).
#[test]
fn fs_proofs_have_an_opaque_json_form() {
    let mut rng = StdRng::seed_from_u64(0x5e7d_0020);
    for n in [0usize, 1, 7] {
        let proof = random_proof(n, &mut rng);
        let tree = round_trip(&proof);
        let bytes = proof.to_bytes().unwrap();
        assert_eq!(bytes.len(), 32 + 8 + 32 * n);
        assert_eq!(bytes[..8], (n as u64).to_le_bytes());
        assert_eq!(bytes[8..], proof.to_narg()[..]);
        assert_opaque(&tree, &bytes);
        let text = tree.as_str().unwrap();
        for (what, bad) in malformed_leaves(text, &bytes) {
            assert!(parse::<FSProof<Fr>>(&bad).is_err(), "{what} accepted");
        }
        // a length that disagrees with the responses
        let longer = json!(serialization::to_multibase(&patched(
            &bytes,
            0,
            &(n as u64 + 1).to_le_bytes()
        )));
        assert!(parse::<FSProof<Fr>>(&longer).is_err());
    }
}

/// The lattice instantiation (feature `lattice`): its objects are opaque strings like every
/// other leaf (secrets through `serialization::secret`), and its messages have the same
/// structured shapes (here an attestation request and an attestation with stand-in proofs: the
/// shape, not the verification, is under test).
#[cfg(feature = "lattice")]
#[test]
fn lattice_objects_are_opaque_and_its_messages_structured() {
    use predicate_credential_system::{
        kiprf::lwr::LWRTag,
        lattice::{Rq, Ternary},
        pcreds::lattice::{
            LatticeBackend, LatticeParams, LatticePoint, LatticeProof, LatticeProtocol,
            base::{VSISTape, VSISVerificationKey},
        },
    };
    let mut rng = StdRng::seed_from_u64(0x5e7d_1a77);
    let pcreds = LatticeProtocol::setup(b"serde/lattice").unwrap();
    let helper = pcreds.helper_keygen(Policy::threshold(1).unwrap(), &mut rng);
    let user = pcreds.register(helper.key(), &mut rng).unwrap();
    // public objects: one opaque string each, the multibase of their canonical encoding
    let tree = round_trip(pcreds.params());
    assert_opaque(&tree, &serialization::to_bytes(pcreds.params()).unwrap());
    let _: LatticeParams = parse(&tree).unwrap();
    for point in [
        LatticePoint::Identifier([3; 32]),
        LatticePoint::Request([7; 32]),
    ] {
        let tree = round_trip(&point);
        assert_opaque(&tree, &serialization::to_bytes(&point).unwrap());
    }
    let vk: &VSISVerificationKey = helper.key().vk();
    assert_opaque(&round_trip(vk), &serialization::to_bytes(vk).unwrap());
    let id: &LWRTag = user.id();
    assert_opaque(&round_trip(id), &serialization::to_bytes(id).unwrap());
    let rq = Rq::one();
    assert_opaque(&round_trip(&rq), &serialization::to_bytes(&rq).unwrap());
    let proof = LatticeProof::from_bytes(vec![1, 2, 3]).unwrap();
    assert_opaque(
        &round_trip(&proof),
        &serialization::to_bytes(&proof).unwrap(),
    );
    round_trip(pcreds.public_parameters());
    // secrets: opaque strings as well
    let key = Ternary::sample(&mut rng);
    let text = serde_json::to_value(&key).unwrap();
    assert_opaque(&text, &serialization::to_bytes(&key).unwrap());
    assert_eq!(parse::<Ternary>(&text).unwrap(), key);
    let tape = VSISTape::sample(&mut rng);
    let text = serde_json::to_value(&tape).unwrap();
    assert!(parse::<VSISTape>(&text).unwrap().ct_eq(&tape));
    let user_text = serde_json::to_value(&user).unwrap();
    assert_opaque(&user_text, &user.to_bytes().unwrap());
    // messages: the structured shapes of every backend
    let request = AttestationRequest::<LatticeBackend> {
        id: user.id().clone(),
        proof: proof.clone(),
    };
    let tree = round_trip(&request);
    assert_members(&tree, &["id", "proof"]);
    let att = Attestation::<LatticeBackend> {
        tag: user.id().clone(),
        show: (),
        proof,
    };
    let tree = round_trip(&att);
    assert_members(&tree, &["tag", "show", "proof"]);
    // the empty show is the multibase of no bytes
    assert_opaque(&tree["show"], &[]);
    // a malformed leaf is refused
    assert!(parse::<LatticePoint>(&json!(serialization::to_multibase(&[9]))).is_err());
}

/// A measurement, not a test of the encoding: the JSON forms of full-size lattice messages (an
/// attestation with a proof of 87,500 bytes, a credential request at `k = 5` with five of them
/// and a `π_iss` of 44,400 bytes, the sizes of measured proofs, the proof bytes random), their
/// lengths and the time to encode and to decode them. base58btc takes time quadratic in the
/// length of a string.
///
/// ```text
/// cargo test --release --features lattice --test serde_json -- --ignored --nocapture lattice_json_cost
/// ```
#[cfg(feature = "lattice")]
#[test]
#[ignore = "measurement: seconds of base58btc (run in release with --ignored --nocapture)"]
fn lattice_json_cost() {
    use std::time::Instant;

    use predicate_credential_system::{
        kiprf::lwr::LWRTag,
        lattice::Rq,
        pcreds::lattice::{LatticeBackend, LatticeProof},
    };
    use rand::RngCore;

    fn proof(rng: &mut StdRng, len: usize) -> LatticeProof {
        let mut bytes = vec![0u8; len];
        rng.fill_bytes(&mut bytes);
        LatticeProof::from_bytes(bytes).unwrap()
    }
    fn timed<T: serde::Serialize + serde::de::DeserializeOwned>(what: &str, value: &T) -> T {
        let start = Instant::now();
        let text = serde_json::to_string(value).unwrap();
        let encode = start.elapsed();
        let start = Instant::now();
        let back: T = serde_json::from_str(&text).unwrap();
        let decode = start.elapsed();
        println!(
            "{what}: {} bytes of JSON, encoded in {:.2} s, decoded in {:.2} s",
            text.len(),
            encode.as_secs_f64(),
            decode.as_secs_f64()
        );
        back
    }

    let mut rng = StdRng::seed_from_u64(0x15_0c05);
    let att = Attestation::<LatticeBackend> {
        tag: LWRTag::from_entries([7; 168]),
        show: (),
        proof: proof(&mut rng, 87_500),
    };
    assert_eq!(timed("attestation", &att).proof, att.proof);
    let request = CredentialRequest::<LatticeBackend> {
        id: LWRTag::from_entries([9; 168]),
        attestations: (0..5)
            .map(|_| Attestation {
                tag: LWRTag::from_entries([7; 168]),
                show: (),
                proof: proof(&mut rng, 87_500),
            })
            .collect(),
        request: Rq::one(),
        proof: proof(&mut rng, 44_400),
    };
    assert_eq!(
        timed("credential request, k = 5", &request).proof,
        request.proof
    );
}

/// `max_multibase_len` bounds the text of `n` bytes for the extreme inputs: zero bytes (one
/// digit `1` each), the largest values and random bytes.
#[test]
fn the_multibase_bound_holds_for_every_length() {
    use rand::RngCore;
    let mut rng = StdRng::seed_from_u64(0x6d62_0001);
    for n in [0usize, 1, 2, 3, 31, 32, 33, 48, 255, 256, 1000, 5376] {
        let mut random = vec![0u8; n];
        rng.fill_bytes(&mut random);
        for bytes in [vec![0u8; n], vec![0xff; n], random] {
            assert!(
                serialization::to_multibase(&bytes).len() <= serialization::max_multibase_len(n),
                "{n} bytes"
            );
        }
    }
}

/// A leaf longer than the multibase text of the longest valid leaf of its role is refused
/// before it is decoded: the error names the bound, while a leaf one character shorter reaches
/// the decoder (and is refused there, as no valid value). Every pairing-based leaf has the
/// bound `pairing::MAX_LEAF_BYTES`.
#[test]
fn over_long_leaves_are_refused_before_decoding() {
    use predicate_credential_system::pcreds::pairing::MAX_LEAF_BYTES;
    let max = serialization::max_multibase_len(MAX_LEAF_BYTES);
    let leaf = |chars: usize| Value::String(format!("z{}", "1".repeat(chars - 1)));
    let long = json!({"id": leaf(max + 1), "proof": leaf(2)});
    let error = parse::<AttestationRequest<Bk<PS, DDH>>>(&long)
        .unwrap_err()
        .to_string();
    assert!(error.contains("longer than"), "{error}");
    let at = json!({"id": leaf(max), "proof": leaf(2)});
    let error = parse::<AttestationRequest<Bk<PS, DDH>>>(&at)
        .unwrap_err()
        .to_string();
    assert!(!error.contains("longer than"), "{error}");
}

/// The lattice leaves have their exact sizes as bounds, and a proof the bound of its kind: an
/// attestation tag or proof one character longer than the multibase text of its bound is
/// refused before it is decoded; a leaf of 4 MiB, whose base58btc decoding would take hours,
/// is refused as quickly.
#[cfg(feature = "lattice")]
#[test]
fn over_long_lattice_leaves_are_refused_before_decoding() {
    use predicate_credential_system::pcreds::{
        Leaf, ProofKind,
        lattice::{LatticeBackend, LatticeProof},
    };
    let leaf = |chars: usize| Value::String(format!("z{}", "1".repeat(chars - 1)));
    let bound = |leaf: Leaf| serialization::max_multibase_len(LatticeBackend::max_leaf_bytes(leaf));
    assert_eq!(LatticeBackend::max_leaf_bytes(Leaf::Tag), 336);
    assert_eq!(LatticeBackend::max_leaf_bytes(Leaf::Show), 0);
    assert_eq!(
        LatticeBackend::max_leaf_bytes(Leaf::Proof(ProofKind::Attestation)),
        4 + LatticeProof::max_bytes(ProofKind::Attestation)
    );
    let tag = bound(Leaf::Tag);
    let proof = bound(Leaf::Proof(ProofKind::Attestation));
    // valid leaves, each a run of zero bytes (one digit `1` each): a tag of 336 zero bytes and
    // the empty proof, LE32(0) (the JSON object lists its members in sorted order: proof, show,
    // tag)
    let (tag_ok, proof_ok) = (leaf(1 + 336), leaf(1 + 4));
    for (att, refused) in [
        (
            json!({"tag": leaf(tag + 1), "show": "z", "proof": proof_ok}),
            true,
        ),
        (
            json!({"tag": leaf(tag), "show": "z", "proof": proof_ok}),
            false,
        ),
        (
            json!({"tag": tag_ok, "show": "z", "proof": leaf(proof + 1)}),
            true,
        ),
        (
            json!({"tag": tag_ok, "show": "z", "proof": leaf(proof)}),
            false,
        ),
        (
            json!({"tag": tag_ok, "show": "z", "proof": leaf(4 << 20)}),
            true,
        ),
    ] {
        let error = parse::<Attestation<LatticeBackend>>(&att)
            .unwrap_err()
            .to_string();
        assert_eq!(error.contains("longer than"), refused, "{error}");
    }
}
