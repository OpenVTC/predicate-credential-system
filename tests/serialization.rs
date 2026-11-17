//! The encodings of the protocol `Π_PCreds` ([`predicate_credential_system::pcreds`]) for every
//! pairing-based base/tag pair over BLS12-381.
//!
//! * **Round trips** of every protocol object through the derived canonical encoding
//!   ([`WireFormat`]) and, for the messages, through the fixed-format compact codec
//!   ([`predicate_credential_system::pcreds::codec`]); the decoded objects are accepted by the
//!   party that receives them. Secrets travel through their wiped encodings
//!   (`Zeroizing<Vec<u8>>`), and the helper comes back through `Protocol::restore_helper`.
//! * **Sizes.** The compact sizes are those of the paper's size table (§7.1, `tab:sizes`). Every
//!   format is written out below as a sequence of slots (`G_1`: 48 B, `Z_p`: 32 B, the count of
//!   a credential request: 4 B, the tag of a reply: 1 B), from the formats of the paper and
//!   independently of the library, so that the sizes are checked rather than echoed. The
//!   derived encodings are longer by their length prefixes: arkworks writes a `Vec` (or a set)
//!   as a little-endian `u64` length followed by its elements, so a proof `(c, z)` is 8 bytes
//!   longer than in the compact codec, and a credential request with `n` attestations
//!   `(8 − 4) + 8n + 8 = 12 + 8n` bytes longer (a `u64` count instead of the 4-byte one, one
//!   prefix in each attestation's proof and one in `π_iss`).
//! * **Strictness** of the decoders: trailing bytes, truncation at every position,
//!   non-canonical scalars, malformed points (off the curve, outside the prime-order subgroup,
//!   uncompressed, abscissa `≥ q`, inconsistent flags), unknown reply tags, hostile attestation
//!   counts, and proofs of the wrong shape.
//! * **Regression vectors** for the digest of `pp` and the proof contexts, computed by this
//!   implementation.
//!
//! Every run is seeded (`StdRng::seed_from_u64`, the seed at each call site).

#![allow(clippy::upper_case_acronyms)] // naming policy: see src/lib.rs

mod common;

use core::fmt::Debug;

use ark_bls12_381::{Fq, Fq2, Fr, G1Affine, G2Affine};
use ark_ec::{AffineRepr, PrimeGroup};
use ark_ff::{BigInteger, One, PrimeField, Zero};
use ark_serialize::CanonicalSerialize;
use common::{BBS, BaseTest, Bk, DDH, DY, Deployment, E, G1, G2, PS, random_proof};
use predicate_credential_system::{
    Error,
    kiprf::ProtocolTag,
    pcreds::{
        Attestation, AttestationRequest, Backend, Credential, CredentialRequest, Decision,
        IssuanceRecord, IssuanceState, IssuanceStore, MembershipProof, ProofKind, Protocol,
        PublicParameters, Reply, User,
        pairing::{
            BBSCredential, BBSParams, BBSPreCredential, BBSShow, BBSVerificationKey, G1Request,
            PSPair, PSVerificationKey, PairingParams,
        },
    },
    serialization::WireFormat,
    sigma::FSProof,
};
use rand::{SeedableRng, rngs::StdRng};
use zeroize::Zeroizing;

// ---------------------------------------------------------------------------------------------
// The formats, written out
// ---------------------------------------------------------------------------------------------

/// Bytes of a compressed `G_1` element of BLS12-381.
const G1_BYTES: usize = 48;
/// Bytes of a compressed `G_2` element.
const G2_BYTES: usize = 96;
/// Bytes of a canonical scalar of `Z_p`.
const ZP_BYTES: usize = 32;
/// Bytes of the digest of `pp` that users, issuance states and helpers carry.
const DIGEST_BYTES: usize = 32;
/// The length prefix arkworks writes before the elements of a `Vec` or a set: a little-endian
/// `u64`.
const LEN_PREFIX: usize = 8;
/// The attestation count of a compact credential request: a little-endian `u32`.
const COUNT_BYTES: usize = 4;
/// The threshold of the deployments, and the `k = 5` of the paper's size table.
const K: usize = 5;
/// The numbers of attestations of the credential requests of a run.
const COUNTS: [usize; 3] = [0, 1, K];
/// The message of the membership proofs.
const MESSAGE: &[u8] = b"serialization suite";
/// Responses of `π_id`: `R_Tag` has the one variable `usk` (§5.2, "Relations").
const IDENTIFIER_RESPONSES: usize = 1;
/// Responses of `π_iss`: `R_iss` has `usk` and the randomness `ρ` of `Ĉ`, for both bases (§6.2:
/// `C = g_1^ρ Y^usk`, resp. `C = h_0 h_u^usk h_r^ρ`).
const ISSUANCE_RESPONSES: usize = 2;

/// One field of a compact encoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Slot {
    /// A compressed `G_1` element.
    G1,
    /// A canonical scalar of `Z_p`, little-endian.
    Zp,
    /// A scalar of a proof, in the NARG string of `draft-irtf-cfrg-sigma-protocols-04`
    /// (§5.5): canonical, big-endian (`I2OSP`).
    Proof,
    /// The attestation count of a credential request.
    Count,
    /// The tag byte of a reply.
    Tag,
}

impl Slot {
    const fn bytes(self) -> usize {
        match self {
            Self::G1 => G1_BYTES,
            Self::Zp | Self::Proof => ZP_BYTES,
            Self::Count => COUNT_BYTES,
            Self::Tag => 1,
        }
    }
}

/// The size of a format.
fn size(slots: &[Slot]) -> usize {
    slots.iter().map(|slot| slot.bytes()).sum()
}

/// The offsets of the slots of kind `kind` in a format.
fn offsets(slots: &[Slot], kind: Slot) -> Vec<usize> {
    let mut at = 0;
    let mut found = Vec::new();
    for &slot in slots {
        if slot == kind {
            found.push(at);
        }
        at += slot.bytes();
    }
    found
}

/// The formats of a base over BLS12-381 (§6.2 and `tab:sizes`), written out independently of
/// the library.
trait Format: BaseTest {
    /// `pp_Σ`: nothing for `Σ-PS`; `(h_0, h_u, h_r)` = 3 `G_1` for `Σ-BBS`.
    const PARAMS: usize;
    /// `hvk`: `Σ-PS` `(X̃, Ỹ, Y)` = 2 `G_2` + `G_1`; `Σ-BBS` `X̃` = `G_2`.
    const VK: usize;
    /// The credential `σ`: `Σ-PS` `(σ_1, σ_2)` = 2 `G_1`; `Σ-BBS` `(A, e, ρ)` = `G_1` + 2 `Z_p`.
    const CRED: usize;
    /// Responses of `π_att` and `π_prove`, one per variable of `R_Possess`: `Σ-PS` `(usk, t)`;
    /// `Σ-BBS` `(usk, ρ, r_1, e, r_3, u, v)`.
    const POSSESSION_RESPONSES: usize;
    /// The pre-credential `σ̂`: `Σ-PS` `(σ_1, σ_2)`; `Σ-BBS` `(A, e)`.
    const PRE: &'static [Slot];
    /// The paper's size table (`tab:sizes`): `|att|`, `|π|` at `k = 5`, the membership proof.
    const PAPER: [usize; 3];
}

impl Format for PS {
    const PARAMS: usize = 0;
    const VK: usize = 2 * G2_BYTES + G1_BYTES;
    const CRED: usize = 2 * G1_BYTES;
    const POSSESSION_RESPONSES: usize = 2;
    const PRE: &'static [Slot] = &[Slot::G1, Slot::G1];
    const PAPER: [usize; 3] = [240, 1344, 192];
}

impl Format for BBS {
    const PARAMS: usize = 3 * G1_BYTES;
    const VK: usize = G2_BYTES;
    const CRED: usize = G1_BYTES + 2 * ZP_BYTES;
    const POSSESSION_RESPONSES: usize = 7;
    const PRE: &'static [Slot] = &[Slot::G1, Slot::Zp];
    const PAPER: [usize; 3] = [448, 2384, 400];
}

/// The encoding of `pp_Tag` (§6.1).
trait TagFormat: ProtocolTag<G1> + 'static {
    /// The size of the derived encoding of `pp_Tag` for the deployment `label`.
    fn params_size(label: &[u8]) -> usize;
}

impl TagFormat for DDH {
    /// The oracle `htag` of the deployment: its domain, the label, as a `Vec<u8>` (the marker
    /// of the group encodes as nothing).
    fn params_size(label: &[u8]) -> usize {
        LEN_PREFIX + label.len()
    }
}

impl TagFormat for DY {
    /// The generator `g_1`.
    fn params_size(_label: &[u8]) -> usize {
        G1_BYTES
    }
}

/// A proof `(c, z_1, …, z_n)`: its NARG string.
fn proof_slots(responses: usize) -> Vec<Slot> {
    vec![Slot::Proof; 1 + responses]
}

/// A show `σ*`: `Σ-PS` `(σ'_1, σ'_2)`, `Σ-BBS` `(Ā, B̄, D)`.
fn show_slots<B: Format>() -> Vec<Slot> {
    vec![Slot::G1; B::NUM_SHOW_ELEMENTS]
}

/// `id_Q ‖ π_id`.
fn attestation_request_slots() -> Vec<Slot> {
    [vec![Slot::G1], proof_slots(IDENTIFIER_RESPONSES)].concat()
}

/// `t ‖ σ* ‖ π_att`.
fn attestation_slots<B: Format>() -> Vec<Slot> {
    [
        vec![Slot::G1],
        show_slots::<B>(),
        proof_slots(B::POSSESSION_RESPONSES),
    ]
    .concat()
}

/// `id_Q ‖ n ‖ att_1 ‖ … ‖ att_n ‖ Ĉ ‖ π_iss`.
fn credential_request_slots<B: Format>(n: usize) -> Vec<Slot> {
    let mut slots = vec![Slot::G1, Slot::Count];
    for _ in 0..n {
        slots.extend(attestation_slots::<B>());
    }
    slots.push(Slot::G1);
    slots.extend(proof_slots(ISSUANCE_RESPONSES));
    slots
}

/// `σ* ‖ π_prove`.
fn membership_slots<B: Format>() -> Vec<Slot> {
    [show_slots::<B>(), proof_slots(B::POSSESSION_RESPONSES)].concat()
}

/// One tag byte, then `σ̂` for a pre-credential.
fn reply_slots<B: Format, T: TagFormat>(reply: &Reply<Bk<B, T>>) -> Vec<Slot> {
    match reply {
        Reply::Fail | Reply::Issued => vec![Slot::Tag],
        Reply::PreCredential(_) => [&[Slot::Tag][..], B::PRE].concat(),
    }
}

// ---------------------------------------------------------------------------------------------
// The compact codec behind one interface
// ---------------------------------------------------------------------------------------------

/// The compact codec of the five messages (inherent methods in the library) behind one
/// interface, so that the checks below are written once.
trait Compact: WireFormat + Clone + PartialEq + Debug {
    fn compact(&self) -> Result<Vec<u8>, Error>;
    fn from_compact(bytes: &[u8]) -> Result<Self, Error>;
    /// The size the codec announces for the compact encoding.
    fn announced(&self) -> usize;
}

impl<Bk: Backend> Compact for AttestationRequest<Bk> {
    fn compact(&self) -> Result<Vec<u8>, Error> {
        self.to_compact_bytes()
    }
    fn from_compact(bytes: &[u8]) -> Result<Self, Error> {
        Self::from_compact_bytes(bytes)
    }
    fn announced(&self) -> usize {
        self.compact_size()
    }
}

impl<Bk: Backend> Compact for Attestation<Bk> {
    fn compact(&self) -> Result<Vec<u8>, Error> {
        self.to_compact_bytes()
    }
    fn from_compact(bytes: &[u8]) -> Result<Self, Error> {
        Self::from_compact_bytes(bytes)
    }
    fn announced(&self) -> usize {
        self.size()
    }
}

impl<Bk: Backend> Compact for CredentialRequest<Bk> {
    fn compact(&self) -> Result<Vec<u8>, Error> {
        self.to_compact_bytes()
    }
    fn from_compact(bytes: &[u8]) -> Result<Self, Error> {
        Self::from_compact_bytes(bytes)
    }
    fn announced(&self) -> usize {
        self.compact_size()
    }
}

impl<Bk: Backend> Compact for MembershipProof<Bk> {
    fn compact(&self) -> Result<Vec<u8>, Error> {
        self.to_compact_bytes()
    }
    fn from_compact(bytes: &[u8]) -> Result<Self, Error> {
        Self::from_compact_bytes(bytes)
    }
    fn announced(&self) -> usize {
        self.size()
    }
}

impl<Bk: Backend> Compact for Reply<Bk> {
    fn compact(&self) -> Result<Vec<u8>, Error> {
        self.to_compact_bytes()
    }
    fn from_compact(bytes: &[u8]) -> Result<Self, Error> {
        Self::from_compact_bytes(bytes)
    }
    fn announced(&self) -> usize {
        self.compact_size()
    }
}

/// A message round-trips through both encodings; the compact encoding has the announced size
/// and the size of `slots`, the derived one is longer by `prefixes` bytes. Returns the value
/// decoded from the compact encoding.
fn encodings<M: Compact>(value: &M, slots: &[Slot], prefixes: usize) -> M {
    let compact = value.compact().expect("compact encoding");
    assert_eq!(compact.len(), value.announced(), "the announced size");
    assert_eq!(compact.len(), size(slots), "the format");
    let decoded = M::from_compact(&compact).expect("compact decoding");
    assert_eq!(&decoded, value);
    let derived = value.to_bytes().expect("derived encoding");
    assert_eq!(
        derived.len(),
        compact.len() + prefixes,
        "the length prefixes"
    );
    assert_eq!(&M::from_bytes(&derived).expect("derived decoding"), value);
    decoded
}

/// `bytes` with `inserted` inserted at `at`.
fn insert(bytes: &[u8], at: usize, inserted: &[u8]) -> Vec<u8> {
    [&bytes[..at], inserted, &bytes[at..]].concat()
}

/// A derived round trip of a value whose encoding has `len` bytes, with the strictness of the
/// derived decoder ([`derived_strictness`]). Returns the decoded value.
fn canonical<V: WireFormat + PartialEq + Debug>(value: &V, len: usize) -> V {
    let bytes = value.to_bytes().expect("derived encoding");
    assert_eq!(bytes.len(), len, "{}", core::any::type_name::<V>());
    let decoded = V::from_bytes(&bytes).expect("derived decoding");
    assert_eq!(&decoded, value);
    derived_strictness::<V>(&bytes);
    decoded
}

/// The derived decoder takes exactly the compressed encoding `bytes`: one more byte is
/// [`Error::TrailingBytes`], every proper prefix [`Error::Serialization`], and the uncompressed
/// encoding of the same value (if it differs, i.e. if the value has a group element) is refused.
fn derived_strictness<V: WireFormat + Debug>(bytes: &[u8]) {
    let name = core::any::type_name::<V>();
    // (a copy of an empty encoding, `()` for the `pp_Σ` of `Σ-PS`, appends nothing)
    for extra in [&[0u8][..], &[0xff; 3], bytes]
        .into_iter()
        .filter(|extra| !extra.is_empty())
    {
        assert!(
            matches!(
                V::from_bytes(&[bytes, extra].concat()),
                Err(Error::TrailingBytes)
            ),
            "{name}: trailing bytes"
        );
    }
    for cut in 0..bytes.len() {
        assert!(
            matches!(V::from_bytes(&bytes[..cut]), Err(Error::Serialization(_))),
            "{name}: truncated to {cut} bytes"
        );
    }
    let value = V::from_bytes(bytes).expect("derived decoding");
    let mut uncompressed = Vec::new();
    value
        .serialize_uncompressed(&mut uncompressed)
        .expect("uncompressed encoding");
    if uncompressed != bytes {
        // control: a genuine uncompressed encoding of the value ...
        let back = V::deserialize_uncompressed(&uncompressed[..]).expect("uncompressed decoding");
        assert_eq!(back.to_bytes().expect("re-encoding"), bytes);
        // ... that the crate's decoder does not accept
        assert!(
            matches!(V::from_bytes(&uncompressed), Err(Error::Serialization(_))),
            "{name}: uncompressed"
        );
    }
}

/// The type of the encodings of secrets: a buffer that is wiped on drop. Calling this on the
/// result of `to_bytes` is the assertion that it has this type.
fn wiped(encoding: Result<Zeroizing<Vec<u8>>, Error>) -> Zeroizing<Vec<u8>> {
    encoding.expect("encoding of a secret")
}

// ---------------------------------------------------------------------------------------------
// Malformed encodings of group elements
// ---------------------------------------------------------------------------------------------

/// The big-endian bytes of an element of `F_q`.
fn be(x: &Fq) -> Vec<u8> {
    x.into_bigint().to_bytes_be()
}

/// The compressed encoding of an abscissa in the format arkworks writes for BLS12-381 (the
/// zcash format): big-endian (for `G_2`, `x = c_0 + c_1 u` as `c_1 ‖ c_0`), with the compression
/// flag `0x80` and, for the larger of the two ordinates, the sign flag `0x20` in the first byte.
fn with_flags(mut bytes: Vec<u8>, largest: bool) -> Vec<u8> {
    bytes[0] |= 0x80 | if largest { 0x20 } else { 0 };
    bytes
}

/// The encoding of the identity of `G_1`: the compression and infinity flags, then zeros.
fn identity_g1() -> Vec<u8> {
    G1Affine::identity().to_bytes().expect("identity")
}

/// 48-byte strings that a validated decoder of a compressed `G_1` element must refuse, each
/// with its defect.
fn malformed_g1() -> Vec<(&'static str, Vec<u8>)> {
    let g = G1Affine::generator();
    // control: `with_flags` writes what arkworks writes
    let largest = G1Affine::get_point_from_x_unchecked(g.x, true) == Some(g);
    assert_eq!(with_flags(be(&g.x), largest), g.to_bytes().unwrap());
    // an abscissa with x³ + 4 not a square in F_q: no point of E(F_q) has it
    let off_curve = (1u64..)
        .map(Fq::from)
        .find(|x| G1Affine::get_point_from_x_unchecked(*x, false).is_none())
        .expect("an abscissa off the curve");
    // a point of E(F_q) outside the subgroup of order r (the cofactor of G_1 is not 1)
    let outside = (1u64..)
        .filter_map(|x| G1Affine::get_point_from_x_unchecked(Fq::from(x), false))
        .find(|p| !p.is_in_correct_subgroup_assuming_on_curve())
        .expect("a point outside the subgroup");
    assert!(outside.is_on_curve());
    let mut uncompressed = Vec::new();
    g.serialize_uncompressed(&mut uncompressed).unwrap();
    let identity = identity_g1();
    let mut identity_with_x = identity.clone();
    identity_with_x[G1_BYTES - 1] = 1;
    let mut identity_with_sign = identity.clone();
    identity_with_sign[0] |= 0x20;
    // x = 2^381 − 1: every bit of the abscissa set, under the compression flag alone
    let mut all_ones = vec![0xff; G1_BYTES];
    all_ones[0] = 0x9f;
    vec![
        ("all zero: no compression flag", vec![0; G1_BYTES]),
        (
            "the first half of an uncompressed encoding",
            uncompressed[..G1_BYTES].to_vec(),
        ),
        (
            "an abscissa off the curve",
            with_flags(be(&off_curve), false),
        ),
        (
            "an abscissa off the curve, other sign",
            with_flags(be(&off_curve), true),
        ),
        (
            "the abscissa q",
            with_flags(Fq::MODULUS.to_bytes_be(), false),
        ),
        ("the abscissa 2^381 - 1", all_ones),
        ("the infinity flag with x != 0", identity_with_x),
        ("the infinity flag with the sign flag", identity_with_sign),
        (
            "on the curve, outside the prime-order subgroup",
            outside.to_bytes().unwrap(),
        ),
    ]
}

/// 96-byte strings that a validated decoder of a compressed `G_2` element must refuse.
fn malformed_g2() -> Vec<(&'static str, Vec<u8>)> {
    let g = G2Affine::generator();
    let largest = G2Affine::get_point_from_x_unchecked(g.x, true) == Some(g);
    assert_eq!(
        with_flags([be(&g.x.c1), be(&g.x.c0)].concat(), largest),
        g.to_bytes().unwrap()
    );
    let x = |k: u64| Fq2::new(Fq::from(k), Fq::zero());
    let off_curve = (1u64..)
        .map(x)
        .find(|x| G2Affine::get_point_from_x_unchecked(*x, false).is_none())
        .expect("an abscissa off the curve");
    let outside = (1u64..)
        .filter_map(|k| G2Affine::get_point_from_x_unchecked(x(k), false))
        .find(|p| !p.is_in_correct_subgroup_assuming_on_curve())
        .expect("a point outside the subgroup");
    assert!(outside.is_on_curve());
    let mut uncompressed = Vec::new();
    g.serialize_uncompressed(&mut uncompressed).unwrap();
    vec![
        ("all zero: no compression flag", vec![0; G2_BYTES]),
        (
            "the first half of an uncompressed encoding",
            uncompressed[..G2_BYTES].to_vec(),
        ),
        (
            "an abscissa off the curve",
            with_flags([be(&off_curve.c1), be(&off_curve.c0)].concat(), false),
        ),
        (
            "on the curve, outside the prime-order subgroup",
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

// ---------------------------------------------------------------------------------------------
// Real protocol objects
// ---------------------------------------------------------------------------------------------

/// A credential request with its sub-session and the requester's state.
type Request<B, T> = (
    Vec<u8>,
    CredentialRequest<Bk<B, T>>,
    IssuanceState<Bk<B, T>>,
);

/// The objects of one run of the protocol under `Pol_K`, each accepted by its receiver.
struct Run<B: Format, T: TagFormat> {
    d: Deployment<B, T>,
    /// The requester `Q`.
    user: User<Bk<B, T>>,
    /// The `(ssid, P̃)` of the attestation request.
    att_ssid: Vec<u8>,
    contact: Vec<u8>,
    /// `(id_Q, π_id)`.
    att_request: AttestationRequest<Bk<B, T>>,
    /// One attestation from each of the `K` members.
    attestations: Vec<Attestation<Bk<B, T>>>,
    /// `(ssid, message, state)` with 0, 1 and `K` attestations ([`COUNTS`]).
    requests: Vec<Request<B, T>>,
    /// `Fail` (0 attestations, `d = policy`), `σ̂` (`K`, `d = policy`), `issued` (1, `d = root`).
    replies: [Reply<Bk<B, T>>; 3],
    /// `Q`'s credential, unblinded from `σ̂`.
    credential: Credential<Bk<B, T>>,
    /// A membership proof of member 0 on [`MESSAGE`].
    membership: MembershipProof<Bk<B, T>>,
}

/// A copy of a stored issuance state, through its encoding (`unblind` consumes a state).
fn copy_of<Bk: Backend>(state: &IssuanceState<Bk>) -> IssuanceState<Bk> {
    IssuanceState::from_bytes(&state.to_bytes().unwrap()).unwrap()
}

fn run<B: Format, T: TagFormat>(label: &[u8], seed: u64) -> Run<B, T> {
    let mut d = Deployment::<B, T>::new(label, K, seed);
    let user = d.register();
    let (att_ssid, contact) = (b"ser/attestation".to_vec(), b"member-0@example".to_vec());
    let att_request = d
        .pcreds
        .request_attestation(&d.hvk, &user, &att_ssid, &contact, &mut d.rng)
        .expect("π_id");
    let attestations = d.attestations(&user);
    let mut requests = Vec::new();
    for n in COUNTS {
        let ssid = d.ssid();
        let (message, state) = d
            .pcreds
            .request_credential(&d.hvk, &user, attestations[..n].to_vec(), &ssid, &mut d.rng)
            .expect("credential request");
        requests.push((ssid, message, state));
    }
    let respond = |d: &mut Deployment<B, T>, i: usize, decision: Decision| {
        let (ssid, message, _) = &requests[i];
        let evaluated = d
            .pcreds
            .evaluate_request(&d.helper, message, ssid)
            .expect("evaluate");
        assert_eq!(evaluated.is_valid(), COUNTS[i] >= K);
        d.pcreds
            .respond(&mut d.helper, evaluated, decision, &mut d.rng)
            .expect("respond")
    };
    let fail = respond(&mut d, 0, Decision::Policy);
    let pre = respond(&mut d, 2, Decision::Policy);
    let issued = respond(&mut d, 1, Decision::Root);
    assert_eq!(fail, Reply::Fail);
    assert_eq!(issued, Reply::Issued);
    let Reply::PreCredential(sigma_hat) = &pre else {
        panic!("a valid request is issued");
    };
    let credential = d
        .pcreds
        .unblind(&d.hvk, &user, sigma_hat, copy_of(&requests[2].2))
        .expect("unblind");
    let member = &d.members[0];
    let membership = d
        .pcreds
        .prove(&d.hvk, &member.user, &member.cred, MESSAGE, &mut d.rng)
        .expect("prove");
    Run {
        d,
        user,
        att_ssid,
        contact,
        att_request,
        attestations,
        requests,
        replies: [fail, pre, issued],
        credential,
        membership,
    }
}

// ---------------------------------------------------------------------------------------------
// Round trips
// ---------------------------------------------------------------------------------------------

/// Every protocol object round-trips through every encoding it has, and the receiver accepts
/// the decoded value.
fn round_trips<B: Format, T: TagFormat>(label: &[u8], seed: u64) {
    let r = run::<B, T>(label, seed);
    let pcreds = &r.d.pcreds;

    // (id_Q, π_id): the owner of the contact name accepts the decoded request.
    let decoded = encodings(&r.att_request, &attestation_request_slots(), LEN_PREFIX);
    pcreds
        .receive_attestation_request(&r.d.hvk, &decoded, &r.att_ssid, &r.contact)
        .expect("π_id after the round trip");
    // the derived encoding is the compact one with the number of responses before the NARG
    // string of the proof
    assert_eq!(
        r.att_request.to_bytes().unwrap(),
        insert(
            &r.att_request.to_compact_bytes().unwrap(),
            G1_BYTES,
            &(IDENTIFIER_RESPONSES as u64).to_le_bytes(),
        )
    );

    // att = (t, σ*, π_att): the recipient accepts the decoded attestations.
    for att in &r.attestations {
        let decoded = encodings(att, &attestation_slots::<B>(), LEN_PREFIX);
        assert_eq!(
            pcreds.check_attestation(&r.d.hvk, r.user.id(), &decoded),
            Ok(())
        );
        let show = (1 + B::NUM_SHOW_ELEMENTS) * G1_BYTES;
        assert_eq!(
            att.to_bytes().unwrap(),
            insert(
                &att.to_compact_bytes().unwrap(),
                show,
                &(B::POSSESSION_RESPONSES as u64).to_le_bytes(),
            )
        );
        // the parts are their canonical encodings
        let compact = att.to_compact_bytes().unwrap();
        assert_eq!(compact[..G1_BYTES], att.tag.to_bytes().unwrap()[..]);
        assert_eq!(compact[G1_BYTES..show], att.show.to_bytes().unwrap()[..]);
    }

    // (id_Q, att⃗, Ĉ, π_iss) with 0, 1 and K attestations: the helper accepts the decoded
    // requests and counts their attestations.
    for ((ssid, message, _), n) in r.requests.iter().zip(COUNTS) {
        let prefixes = (LEN_PREFIX - COUNT_BYTES) + n * LEN_PREFIX + LEN_PREFIX;
        let decoded = encodings(message, &credential_request_slots::<B>(n), prefixes);
        assert_eq!(
            message.compact_size(),
            message.size() + G1_BYTES + COUNT_BYTES
        );
        let compact = message.to_compact_bytes().unwrap();
        let derived = message.to_bytes().unwrap();
        assert_eq!(
            compact[G1_BYTES..G1_BYTES + COUNT_BYTES],
            (n as u32).to_le_bytes()
        );
        assert_eq!(
            derived[G1_BYTES..G1_BYTES + LEN_PREFIX],
            (n as u64).to_le_bytes()
        );
        let evaluated = pcreds
            .evaluate_request(&r.d.helper, &decoded, ssid)
            .expect("π_iss after the round trip");
        assert_eq!(evaluated.tags().len(), n);
        assert_eq!(evaluated.is_valid(), n >= K);
        assert_eq!(evaluated.id(), r.user.id());
    }

    // Replies: the compact encoding is the canonical one, a tag byte and σ̂.
    for (reply, tag) in r.replies.iter().zip([0u8, 2, 1]) {
        encodings(reply, &reply_slots::<B, T>(reply), 0);
        let bytes = reply.to_compact_bytes().unwrap();
        assert_eq!(bytes, reply.to_bytes().unwrap());
        assert_eq!(bytes[0], tag);
        if let Reply::PreCredential(pre) = reply {
            assert_eq!(bytes[1..], pre.to_bytes().unwrap()[..]);
        }
    }

    // σ*‖π_prove: any verifier accepts the decoded membership proof.
    let decoded = encodings(&r.membership, &membership_slots::<B>(), LEN_PREFIX);
    assert_eq!(pcreds.check_membership(&r.d.hvk, MESSAGE, &decoded), Ok(()));

    // pp, and its parts: a party that receives pp rebuilds the same protocol from it.
    let pp = pcreds.public_parameters();
    let params: &PairingParams<E, B, T> = pcreds.params();
    let tag_size = T::params_size(label);
    let received = canonical(pp, LEN_PREFIX + label.len() + B::PARAMS + tag_size);
    let rebuilt = Protocol::<Bk<B, T>>::from_public_parameters(received).expect("pp");
    assert_eq!(rebuilt.parameters_digest(), pcreds.parameters_digest());
    assert_eq!(canonical(params, B::PARAMS + tag_size), *params);
    canonical(&params.base, B::PARAMS);
    canonical(&params.tag, tag_size);
    // the identifier point x_0 = H_id(⟨hvk⟩) is the key's, not a part of pp
    canonical(r.d.hvk.identifier_point(), ZP_BYTES);
    assert_eq!(
        pcreds.identifier_point(r.d.hvk.vk()).unwrap(),
        *r.d.hvk.identifier_point()
    );
    // well formed but not derived from the label: decodes, and is refused
    let mut moved = pp.clone();
    moved.label = b"another deployment".to_vec();
    let moved = PublicParameters::<Bk<B, T>>::from_bytes(&moved.to_bytes().unwrap()).unwrap();
    assert!(matches!(
        Protocol::<Bk<B, T>>::from_public_parameters(moved),
        Err(Error::InvalidPublicParameters(_))
    ));

    // The types of the base, through the associated types (Σ-PS: PSVerificationKey, G1Request,
    // and PSPair as show, pre-credential and credential; Σ-BBS: BBSParams above,
    // BBSVerificationKey, G1Request, BBSShow, BBSPreCredential, BBSCredential).
    let vk = canonical(r.d.hvk.vk(), B::VK);
    assert!(pcreds.helper_key(&vk).is_ok());
    canonical(&r.requests[2].1.request, G1_BYTES);
    canonical(&r.attestations[0].show, B::NUM_SHOW_ELEMENTS * G1_BYTES);
    canonical(&r.membership.show, B::NUM_SHOW_ELEMENTS * G1_BYTES);
    let Reply::PreCredential(pre) = &r.replies[1] else {
        unreachable!("the second reply is σ̂");
    };
    canonical(pre, size(B::PRE));
    canonical(r.credential.as_inner(), B::CRED);
    canonical(
        &r.att_request.proof,
        ZP_BYTES + LEN_PREFIX + IDENTIFIER_RESPONSES * ZP_BYTES,
    );

    secrets(&r, pre);
}

/// The secrets, through their wiped encodings.
fn secrets<B: Format, T: TagFormat>(r: &Run<B, T>, pre: &B::PreCredential) {
    let pcreds = &r.d.pcreds;

    // User: usk ‖ id ‖ pp-digest ‖ helper fingerprint; the way back is WireFormat::from_bytes,
    // then check_user.
    let bytes = wiped(r.user.to_bytes());
    assert_eq!(bytes.len(), ZP_BYTES + G1_BYTES + 2 * DIGEST_BYTES);
    assert_eq!(bytes[..32], r.user.expose_key().to_bytes().unwrap()[..]);
    assert_eq!(bytes[32..80], r.user.id().to_bytes().unwrap()[..]);
    assert_eq!(bytes[80..112], r.user.parameters_digest()[..]);
    assert_eq!(bytes[112..], r.user.helper_fingerprint()[..]);
    assert_eq!(r.user.helper_fingerprint(), r.d.hvk.fingerprint());
    // the blanket WireFormat::to_bytes gives the same bytes, in a buffer nobody wipes
    assert_eq!(bytes[..], WireFormat::to_bytes(&r.user).unwrap()[..]);
    let user = User::<Bk<B, T>>::from_bytes(&bytes).expect("user");
    assert_eq!(pcreds.check_user(&r.d.hvk, &user), Ok(()));
    assert_eq!(user.id(), r.user.id());
    assert_eq!(user.expose_key(), r.user.expose_key());
    assert_eq!(user.parameters_digest(), r.user.parameters_digest());
    derived_strictness::<User<Bk<B, T>>>(&bytes);
    // a well-formed encoding of a user that is not one: decodes, and check_user refuses it
    let other = r.d.members[0].user.id().to_bytes().unwrap();
    let alien = User::<Bk<B, T>>::from_bytes(&patched(&bytes, 32, &other)).unwrap();
    assert_eq!(
        pcreds.check_user(&r.d.hvk, &alien),
        Err(Error::IdentifierMismatch)
    );
    for at in [80, 112] {
        let mut digest = bytes[at..at + DIGEST_BYTES].to_vec();
        digest[0] ^= 1;
        let alien = User::<Bk<B, T>>::from_bytes(&patched(&bytes, at, &digest)).unwrap();
        assert_eq!(
            pcreds.check_user(&r.d.hvk, &alien),
            Err(Error::IdentifierMismatch)
        );
    }

    // Credential: the credential of the base, nothing else.
    let bytes = wiped(r.credential.to_bytes());
    assert_eq!(bytes.len(), B::CRED);
    assert_eq!(bytes[..], r.credential.as_inner().to_bytes().unwrap()[..]);
    let cred = Credential::<Bk<B, T>>::from_bytes(&bytes).expect("credential");
    assert_eq!(cred, r.credential);
    assert!(pcreds.verify_credential(&r.d.hvk, &r.user, &cred));
    derived_strictness::<Credential<Bk<B, T>>>(&bytes);

    // IssuanceState: τ ‖ id ‖ pp-digest; σ̂ and the stored τ give the same credential.
    let (_, _, state) = &r.requests[2];
    let bytes = wiped(state.to_bytes());
    assert_eq!(bytes.len(), ZP_BYTES + G1_BYTES + DIGEST_BYTES);
    assert_eq!(bytes[..32], state.expose_tape().to_bytes().unwrap()[..]);
    assert_eq!(bytes[32..80], r.user.id().to_bytes().unwrap()[..]);
    assert_eq!(bytes[80..], pcreds.parameters_digest()[..]);
    let stored = IssuanceState::<Bk<B, T>>::from_bytes(&bytes).expect("state");
    assert_eq!(stored.expose_tape(), state.expose_tape());
    assert_eq!(format!("{stored:?}"), "IssuanceState(<redacted>)");
    let cred = pcreds
        .unblind(&r.d.hvk, &r.user, pre, stored)
        .expect("unblind with the stored state");
    assert_eq!(cred, r.credential);
    derived_strictness::<IssuanceState<Bk<B, T>>>(&bytes);
    // a state of another user: decodes, and unblind refuses it
    let alien = IssuanceState::<Bk<B, T>>::from_bytes(&patched(&bytes, 32, &other)).unwrap();
    assert_eq!(
        pcreds.unblind(&r.d.hvk, &r.user, pre, alien).err(),
        Some(Error::IssuanceStateMismatch)
    );

    // Helper: pp-digest ‖ hvk ‖ sk, back through restore_helper; the record is kept apart.
    let bytes = wiped(r.d.helper.to_bytes());
    assert_eq!(bytes.len(), DIGEST_BYTES + B::VK + ZP_BYTES);
    assert_eq!(bytes[..32], pcreds.parameters_digest()[..]);
    assert_eq!(
        bytes[32..32 + B::VK],
        r.d.helper.key().vk().to_bytes().unwrap()[..]
    );
    let record = r.d.helper.store();
    // K root members and the requester
    assert_eq!(record.len(), K + 1);
    let record_bytes = record.to_bytes().unwrap();
    assert_eq!(
        record_bytes.len(),
        LEN_PREFIX + record.len() * (LEN_PREFIX + G1_BYTES)
    );
    let stored_record = canonical(record, record_bytes.len());
    assert_eq!(
        stored_record.contains(&r.user.id().to_bytes().unwrap()),
        Ok(true)
    );
    let mut helper = pcreds
        .restore_helper(&bytes, *r.d.helper.policy(), stored_record)
        .expect("restore");
    assert_eq!(helper.key(), r.d.helper.key());
    assert_eq!(helper.policy(), r.d.helper.policy());
    // The restored helper remembers the requester ...
    let (ssid, message, _) = &r.requests[2];
    let mut rng = StdRng::seed_from_u64(0x5e21_00ff);
    let evaluated = pcreds.evaluate_request(&helper, message, ssid).unwrap();
    assert_eq!(
        pcreds
            .respond(&mut helper, evaluated, Decision::Policy, &mut rng)
            .unwrap(),
        Reply::Issued
    );
    // ... and issues with the restored sk: a root admission of a new user unblinds.
    let fresh = pcreds.register(&r.d.hvk, &mut rng).unwrap();
    let (message, state) = pcreds
        .request_credential(&r.d.hvk, &fresh, Vec::new(), b"fresh", &mut rng)
        .unwrap();
    let evaluated = pcreds
        .evaluate_request(&helper, &message, b"fresh")
        .unwrap();
    let Reply::PreCredential(pre) = pcreds
        .respond(&mut helper, evaluated, Decision::Root, &mut rng)
        .unwrap()
    else {
        panic!("a root admission issues");
    };
    assert!(pcreds.unblind(&r.d.hvk, &fresh, &pre, state).is_ok());
}

#[test]
fn round_trips_ps_ddh() {
    round_trips::<PS, DDH>(b"ser/ps+ddh", 0x5e21_0001);
}

#[test]
fn round_trips_ps_dy() {
    round_trips::<PS, DY>(b"ser/ps+dy", 0x5e21_0002);
}

#[test]
fn round_trips_bbs_ddh() {
    round_trips::<BBS, DDH>(b"ser/bbs+ddh", 0x5e21_0003);
}

#[test]
fn round_trips_bbs_dy() {
    round_trips::<BBS, DY>(b"ser/bbs+dy", 0x5e21_0004);
}

// ---------------------------------------------------------------------------------------------
// Sizes
// ---------------------------------------------------------------------------------------------

fn sizes<B: Format, T: TagFormat>(label: &[u8], seed: u64) {
    // The number of responses of each proof, from the relations of the paper.
    assert_eq!(
        <Bk<B, T>>::responses(ProofKind::Identifier),
        IDENTIFIER_RESPONSES
    );
    assert_eq!(
        <Bk<B, T>>::responses(ProofKind::Attestation),
        B::POSSESSION_RESPONSES
    );
    assert_eq!(
        <Bk<B, T>>::responses(ProofKind::Possession),
        B::POSSESSION_RESPONSES
    );
    assert_eq!(
        <Bk<B, T>>::responses(ProofKind::Issuance),
        ISSUANCE_RESPONSES
    );

    let r = run::<B, T>(label, seed);
    let [att, pi, membership] = B::PAPER;
    let (_, message, _) = &r.requests[2];
    // the formats give the paper's sizes ...
    assert_eq!(size(&attestation_slots::<B>()), att);
    assert_eq!(
        size(&credential_request_slots::<B>(K)),
        G1_BYTES + COUNT_BYTES + pi
    );
    assert_eq!(size(&membership_slots::<B>()), membership);
    // ... and so do the objects: |att|, |π| (the K attestations, Ĉ and π_iss), the
    // membership proof, |cred|
    assert_eq!(r.attestations[0].size(), att);
    assert_eq!(message.size(), pi);
    assert_eq!(r.membership.size(), membership);
    assert_eq!(r.credential.to_bytes().unwrap().len(), B::CRED);
    // the wire format adds id_Q and the count to |π|
    assert_eq!(message.compact_size(), G1_BYTES + COUNT_BYTES + pi);
    assert_eq!(
        message.to_compact_bytes().unwrap().len(),
        message.compact_size()
    );
    // the other messages: id_Q ‖ (c, z_usk); the replies
    assert_eq!(
        r.att_request.compact_size(),
        G1_BYTES + (1 + IDENTIFIER_RESPONSES) * ZP_BYTES
    );
    assert_eq!(r.att_request.compact_size(), 112);
    let reply_sizes = r.replies.each_ref().map(Reply::compact_size);
    assert_eq!(reply_sizes, [1, 1 + size(B::PRE), 1]);
    // the derived encodings, longer by their length prefixes (module docs)
    assert_eq!(
        r.attestations[0].to_bytes().unwrap().len(),
        att + LEN_PREFIX
    );
    assert_eq!(
        message.to_bytes().unwrap().len(),
        message.compact_size() + 12 + 8 * K
    );
    assert_eq!(
        r.membership.to_bytes().unwrap().len(),
        membership + LEN_PREFIX
    );
}

/// The compact sizes are those of the paper's size table (§7.1, `tab:sizes`, "for either tag"),
/// over BLS12-381 with compressed group elements:
///
/// * `Σ-PS`: `|att|` = `t` (`G_1`) + `σ* = (σ'_1, σ'_2)` (2 `G_1`) + `π_att = (c, z_usk, z_t)`
///   (3 `Z_p`) = 144 + 96 = 240; `|π|` at `k = 5` = 5·240 + `Ĉ` (48) + `π_iss = (c, z_usk, z_ρ)`
///   (96) = 1344; membership proof = `σ*` (96) + `π_prove` (3 `Z_p`) = 192; `|cred|` = 96.
/// * `Σ-BBS`: `|att|` = 48 + `(Ā, B̄, D)` (144) + `(c, z_usk, z_ρ, z_{r_1}, z_e, z_{r_3}, z_u,
///   z_v)` (8 `Z_p` = 256) = 448; `|π|` = 5·448 + 48 + 96 = 2384; membership proof = 144 + 256
///   = 400; `|cred|` = `(A, e, ρ)` = 112.
#[test]
fn compact_sizes_are_the_papers() {
    let g1 = G1::generator();
    let g2 = G2::generator();
    assert_eq!(g1.compressed_size(), G1_BYTES);
    assert_eq!(g2.compressed_size(), G2_BYTES);
    assert_eq!(Fr::one().compressed_size(), ZP_BYTES);
    sizes::<PS, DDH>(b"ser/size/ps+ddh", 0x5e22_0001);
    sizes::<PS, DY>(b"ser/size/ps+dy", 0x5e22_0002);
    sizes::<BBS, DDH>(b"ser/size/bbs+ddh", 0x5e22_0003);
    sizes::<BBS, DY>(b"ser/size/bbs+dy", 0x5e22_0004);
}

// ---------------------------------------------------------------------------------------------
// Strictness
// ---------------------------------------------------------------------------------------------

/// The compact decoder takes exactly the encodings the encoder writes: trailing bytes, every
/// proper prefix, a non-canonical scalar in any scalar slot and a malformed point in any
/// `G_1` slot are refused, and so is the same layout with uncompressed points.
fn compact_strictness<M: Compact>(value: &M, slots: &[Slot]) {
    let name = core::any::type_name::<M>();
    let bytes = value.compact().expect("compact encoding");
    assert_eq!(bytes.len(), size(slots));
    // every accepted string is the unique encoding of its value
    for extra in [&[0u8][..], &[0xff; G1_BYTES], &bytes[..]] {
        assert_eq!(
            M::from_compact(&[&bytes[..], extra].concat()),
            Err(Error::TrailingBytes),
            "{name}: trailing bytes"
        );
    }
    for cut in 0..bytes.len() {
        assert!(
            matches!(M::from_compact(&bytes[..cut]), Err(Error::Serialization(_))),
            "{name}: truncated to {cut} bytes"
        );
    }
    // scalars: r and 2^256 − 1 are refused, r − 1 (the largest canonical scalar) is taken, in
    // the byte order of the slot (big-endian inside a proof)
    for (kind, modulus, largest) in [
        (
            Slot::Zp,
            Fr::MODULUS.to_bytes_le(),
            (-Fr::one()).into_bigint().to_bytes_le(),
        ),
        (
            Slot::Proof,
            Fr::MODULUS.to_bytes_be(),
            (-Fr::one()).into_bigint().to_bytes_be(),
        ),
    ] {
        for at in offsets(slots, kind) {
            for bad in [&modulus[..], &[0xff; ZP_BYTES]] {
                assert!(
                    matches!(
                        M::from_compact(&patched(&bytes, at, bad)),
                        Err(Error::Serialization(_))
                    ),
                    "{name}: scalar ≥ r at {at}"
                );
            }
            assert!(M::from_compact(&patched(&bytes, at, &largest)).is_ok());
        }
    }
    // points: every malformed encoding is refused; the identity is taken (decoding does not
    // decide validity, see `decoding_does_not_decide_validity`)
    let malformed = malformed_g1();
    for at in offsets(slots, Slot::G1) {
        for (defect, bad) in &malformed {
            assert!(
                matches!(
                    M::from_compact(&patched(&bytes, at, bad)),
                    Err(Error::Serialization(_))
                ),
                "{name}: {defect} at {at}"
            );
        }
        assert!(M::from_compact(&patched(&bytes, at, &identity_g1())).is_ok());
    }
    // the same layout with every G_1 element uncompressed (96 B)
    if slots.contains(&Slot::G1) {
        let mut uncompressed = Vec::new();
        let mut at = 0;
        for &slot in slots {
            let field = &bytes[at..at + slot.bytes()];
            if slot == Slot::G1 {
                G1Affine::from_bytes(field)
                    .unwrap()
                    .serialize_uncompressed(&mut uncompressed)
                    .unwrap();
            } else {
                uncompressed.extend_from_slice(field);
            }
            at += slot.bytes();
        }
        assert!(
            matches!(M::from_compact(&uncompressed), Err(Error::Serialization(_))),
            "{name}: uncompressed points"
        );
    }
    derived_strictness::<M>(&value.to_bytes().expect("derived encoding"));
}

fn strictness<B: Format, T: TagFormat>(label: &[u8], seed: u64) {
    let r = run::<B, T>(label, seed);
    compact_strictness(&r.att_request, &attestation_request_slots());
    compact_strictness(&r.attestations[0], &attestation_slots::<B>());
    for ((_, message, _), n) in r.requests.iter().zip(COUNTS) {
        compact_strictness(message, &credential_request_slots::<B>(n));
    }
    compact_strictness(&r.membership, &membership_slots::<B>());
    for reply in &r.replies {
        compact_strictness(reply, &reply_slots::<B, T>(reply));
    }
    reply_tags(&r);
    attestation_counts(&r);
    proof_shapes(&r);
}

/// A reply is one of three tag bytes; any other byte is refused, and so is a tag with the
/// payload of another.
fn reply_tags<B: Format, T: TagFormat>(r: &Run<B, T>) {
    type R<B, T> = Reply<Bk<B, T>>;
    let pre = r.replies[1].to_compact_bytes().unwrap();
    for tag in [3u8, 4, 0x7f, 0x80, 0xff] {
        assert!(matches!(
            R::<B, T>::from_compact_bytes(&[tag]),
            Err(Error::Serialization(_))
        ));
        let other = patched(&pre, 0, &[tag]);
        assert!(matches!(
            R::<B, T>::from_compact_bytes(&other),
            Err(Error::Serialization(_))
        ));
        assert!(matches!(
            R::<B, T>::from_bytes(&other),
            Err(Error::Serialization(_))
        ));
    }
    for tag in [0u8, 1] {
        assert_eq!(
            R::<B, T>::from_compact_bytes(&patched(&pre, 0, &[tag])),
            Err(Error::TrailingBytes)
        );
    }
    assert!(matches!(
        R::<B, T>::from_compact_bytes(&[2]),
        Err(Error::Serialization(_))
    ));
    assert!(matches!(
        R::<B, T>::from_compact_bytes(&[]),
        Err(Error::Serialization(_))
    ));
}

/// The one length on the wire, the attestation count of a credential request: a count that
/// disagrees with the attestations is refused, and a count of `u32::MAX` on a short input fails
/// at once (the decoder allocates nothing ahead of the input).
fn attestation_counts<B: Format, T: TagFormat>(r: &Run<B, T>) {
    type M<B, T> = CredentialRequest<Bk<B, T>>;
    let (_, message, _) = &r.requests[1];
    let bytes = message.to_compact_bytes().unwrap();
    let count = G1_BYTES..G1_BYTES + COUNT_BYTES;
    assert_eq!(bytes[count.clone()], 1u32.to_le_bytes());
    // more attestations than there are: the decoder runs into Ĉ ‖ π_iss and off the end
    for n in [2u32, 3, 1000, u32::MAX] {
        let b = patched(&bytes, count.start, &n.to_le_bytes());
        assert!(
            matches!(
                M::<B, T>::from_compact_bytes(&b),
                Err(Error::Serialization(_))
            ),
            "count {n}"
        );
    }
    // fewer: Ĉ and π_iss are read from the attestation, which either fails or leaves bytes
    let b = patched(&bytes, count.start, &0u32.to_le_bytes());
    assert!(matches!(
        M::<B, T>::from_compact_bytes(&b),
        Err(Error::Serialization(_) | Error::TrailingBytes)
    ));
    // u32::MAX and nothing behind it
    let b = [
        &bytes[..count.end - COUNT_BYTES],
        &u32::MAX.to_le_bytes()[..],
    ]
    .concat();
    assert!(matches!(
        M::<B, T>::from_compact_bytes(&b),
        Err(Error::Serialization(_))
    ));
    // the derived encoding: a u64 count of u64::MAX on a short input
    let derived = message.to_bytes().unwrap();
    let b = patched(&derived, G1_BYTES, &u64::MAX.to_le_bytes());
    assert!(matches!(
        M::<B, T>::from_bytes(&b),
        Err(Error::Serialization(_))
    ));
}

/// A proof of the wrong shape (a number of responses its kind does not have) has no compact
/// encoding ([`Error::LengthMismatch`]); its derived encoding, which is self-describing, decodes,
/// and the verifiers refuse it.
fn proof_shapes<B: Format, T: TagFormat>(r: &Run<B, T>) {
    let pcreds = &r.d.pcreds;
    let possession = B::POSSESSION_RESPONSES;
    let mismatch = |expected, actual| Err(Error::LengthMismatch { expected, actual });

    // π_id: one response
    for actual in [0, IDENTIFIER_RESPONSES + 1] {
        let mut m = r.att_request.clone();
        m.proof.responses.resize(actual, Fr::one());
        assert_eq!(m.to_compact_bytes(), mismatch(IDENTIFIER_RESPONSES, actual));
        assert_eq!(
            m.serialize_compact(&mut Vec::<u8>::new()),
            Err(Error::LengthMismatch {
                expected: IDENTIFIER_RESPONSES,
                actual
            })
        );
        assert_eq!(
            AttestationRequest::<Bk<B, T>>::from_bytes(&m.to_bytes().unwrap()).unwrap(),
            m
        );
        assert_eq!(
            pcreds
                .receive_attestation_request(&r.d.hvk, &m, &r.att_ssid, &r.contact)
                .err(),
            Some(Error::InvalidProof)
        );
    }

    // π_att
    for actual in [possession - 1, possession + 1] {
        let mut m = r.attestations[0].clone();
        m.proof.responses.resize(actual, Fr::one());
        assert_eq!(m.to_compact_bytes(), mismatch(possession, actual));
        assert_eq!(
            Attestation::<Bk<B, T>>::from_bytes(&m.to_bytes().unwrap()).unwrap(),
            m
        );
        assert_eq!(
            pcreds.check_attestation(&r.d.hvk, r.user.id(), &m),
            Err(Error::InvalidProof)
        );
    }

    // π_iss, and an attestation inside a credential request
    let (ssid, message, _) = &r.requests[2];
    let mut m = message.clone();
    m.proof.responses.push(Fr::one());
    assert_eq!(
        m.to_compact_bytes(),
        mismatch(ISSUANCE_RESPONSES, ISSUANCE_RESPONSES + 1)
    );
    assert_eq!(
        pcreds.evaluate_request(&r.d.helper, &m, ssid).err(),
        Some(Error::InvalidProof)
    );
    let mut m = message.clone();
    m.attestations[K - 1].proof.responses.pop();
    assert_eq!(m.to_compact_bytes(), mismatch(possession, possession - 1));
    assert_eq!(
        CredentialRequest::<Bk<B, T>>::from_bytes(&m.to_bytes().unwrap()).unwrap(),
        m
    );

    // π_prove
    let mut m = r.membership.clone();
    m.proof.responses.push(Fr::one());
    assert_eq!(m.to_compact_bytes(), mismatch(possession, possession + 1));
    assert_eq!(
        pcreds.check_membership(&r.d.hvk, MESSAGE, &m),
        Err(Error::InvalidProof)
    );
}

#[test]
fn decoders_are_strict_ps_ddh() {
    strictness::<PS, DDH>(b"ser/strict/ps+ddh", 0x5e23_0001);
}

#[test]
fn decoders_are_strict_ps_dy() {
    strictness::<PS, DY>(b"ser/strict/ps+dy", 0x5e23_0002);
}

#[test]
fn decoders_are_strict_bbs_ddh() {
    strictness::<BBS, DDH>(b"ser/strict/bbs+ddh", 0x5e23_0003);
}

#[test]
fn decoders_are_strict_bbs_dy() {
    strictness::<BBS, DY>(b"ser/strict/bbs+dy", 0x5e23_0004);
}

/// The base types by name, with their `G_2` elements: malformed points are refused in every
/// slot, as they are in the encoding of a helper key.
#[test]
fn base_types_are_strict() {
    let malformed_1 = malformed_g1();
    let malformed_2 = malformed_g2();
    let refused = |result: Result<(), Error>, what: &str| {
        assert!(matches!(result, Err(Error::Serialization(_))), "{what}");
    };

    // Σ-PS
    let r = run::<PS, DDH>(b"ser/types/ps", 0x5e24_0001);
    let vk: &PSVerificationKey<E> = r.d.hvk.vk();
    let bytes = canonical(vk, 2 * G2_BYTES + G1_BYTES).to_bytes().unwrap();
    // X̃ ‖ Ỹ ‖ Y
    assert_eq!(bytes[..96], vk.x2.to_bytes().unwrap()[..]);
    assert_eq!(bytes[96..192], vk.y2.to_bytes().unwrap()[..]);
    assert_eq!(bytes[192..], vk.y1.to_bytes().unwrap()[..]);
    for at in [0, G2_BYTES] {
        for (defect, bad) in &malformed_2 {
            let b = patched(&bytes, at, bad);
            refused(PSVerificationKey::<E>::from_bytes(&b).map(drop), defect);
        }
    }
    for (defect, bad) in &malformed_1 {
        let b = patched(&bytes, 2 * G2_BYTES, bad);
        refused(PSVerificationKey::<E>::from_bytes(&b).map(drop), defect);
    }
    let cred: &PSPair<E> = r.credential.as_inner();
    canonical(cred, 2 * G1_BYTES);
    let request: &G1Request<E> = &r.requests[2].1.request;
    canonical(request, G1_BYTES);
    helper_strictness(&r, &malformed_2);

    // Σ-BBS
    let r = run::<BBS, DY>(b"ser/types/bbs", 0x5e24_0002);
    let params: &BBSParams<E> = &r.d.pcreds.params().base;
    let bytes = canonical(params, 3 * G1_BYTES).to_bytes().unwrap();
    for at in [0, G1_BYTES, 2 * G1_BYTES] {
        for (defect, bad) in &malformed_1 {
            refused(
                BBSParams::<E>::from_bytes(&patched(&bytes, at, bad)).map(drop),
                defect,
            );
        }
    }
    let vk: &BBSVerificationKey<E> = r.d.hvk.vk();
    canonical(vk, G2_BYTES);
    for (defect, bad) in &malformed_2 {
        refused(BBSVerificationKey::<E>::from_bytes(bad).map(drop), defect);
    }
    let Reply::PreCredential(pre) = &r.replies[1] else {
        unreachable!("the second reply is σ̂");
    };
    let pre: &BBSPreCredential<E> = pre;
    let bytes = canonical(pre, G1_BYTES + ZP_BYTES).to_bytes().unwrap();
    refused(
        BBSPreCredential::<E>::from_bytes(&patched(&bytes, G1_BYTES, &Fr::MODULUS.to_bytes_le()))
            .map(drop),
        "e = r",
    );
    let show: &BBSShow<E> = &r.attestations[0].show;
    canonical(show, 3 * G1_BYTES);
    let cred: &BBSCredential<E> = r.credential.as_inner();
    canonical(cred, G1_BYTES + 2 * ZP_BYTES);
    helper_strictness(&r, &malformed_2);
}

/// `Protocol::restore_helper` takes exactly the encoding of a helper of its deployment.
fn helper_strictness<B: Format, T: TagFormat>(
    r: &Run<B, T>,
    malformed_2: &[(&'static str, Vec<u8>)],
) {
    let pcreds = &r.d.pcreds;
    let policy = *r.d.helper.policy();
    let restore = |bytes: &[u8]| {
        pcreds
            .restore_helper(bytes, policy, IssuanceRecord::new())
            .map(drop)
    };
    let bytes = wiped(r.d.helper.to_bytes());
    assert_eq!(restore(&bytes), Ok(()));
    assert_eq!(
        restore(&[&bytes[..], &[0]].concat()),
        Err(Error::TrailingBytes)
    );
    for cut in 0..bytes.len() {
        assert!(
            matches!(restore(&bytes[..cut]), Err(Error::Serialization(_))),
            "helper truncated to {cut} bytes"
        );
    }
    // the first G_2 element of hvk
    for (defect, bad) in malformed_2 {
        assert!(
            matches!(
                restore(&patched(&bytes, DIGEST_BYTES, bad)),
                Err(Error::Serialization(_))
            ),
            "{defect}"
        );
    }
    // the sk ≥ r
    assert!(matches!(
        restore(&patched(
            &bytes,
            DIGEST_BYTES + B::VK,
            &Fr::MODULUS.to_bytes_le()
        )),
        Err(Error::Serialization(_))
    ));
    // a key of another deployment, and an sk that does not belong to hvk
    let mut rng = StdRng::seed_from_u64(0x5e24_00ff);
    let elsewhere = Protocol::<Bk<B, T>>::setup(b"ser/elsewhere").unwrap();
    let foreign = wiped(elsewhere.helper_keygen(policy, &mut rng).to_bytes());
    assert_eq!(restore(&foreign), Err(Error::InvalidKey));
    let other = wiped(pcreds.helper_keygen(policy, &mut rng).to_bytes());
    let mixed = [
        &bytes[..DIGEST_BYTES + B::VK],
        &other[DIGEST_BYTES + B::VK..],
    ]
    .concat();
    assert_eq!(restore(&mixed), Err(Error::InvalidKey));
    let mut digest = bytes[..DIGEST_BYTES].to_vec();
    digest[31] ^= 0x80;
    assert_eq!(
        restore(&patched(&bytes, 0, &digest)),
        Err(Error::InvalidKey)
    );
}

/// Decoding checks the ENCODING; validity is the verifier's business (module docs of
/// `serialization`: arkworks validation accepts the identity and the zero scalar). A degenerate
/// tag, show or challenge decodes, and the verifier names what is wrong with it.
fn validity<B: Format, T: TagFormat>(label: &[u8], seed: u64) {
    let r = run::<B, T>(label, seed);
    let identity = identity_g1();
    let bytes = r.attestations[0].to_compact_bytes().unwrap();
    let check = |b: &[u8]| {
        let decoded = Attestation::from_compact_bytes(b).expect("well formed");
        r.d.pcreds
            .check_attestation(&r.d.hvk, r.user.id(), &decoded)
    };
    assert_eq!(check(&bytes), Ok(()));
    // t = 1
    assert_eq!(
        check(&patched(&bytes, 0, &identity)),
        Err(Error::InvalidTag)
    );
    // the first element of σ* (σ'_1, resp. Ā) = 1
    assert_eq!(
        check(&patched(&bytes, G1_BYTES, &identity)),
        Err(Error::InvalidCredential)
    );
    // c = 0
    let c = (1 + B::NUM_SHOW_ELEMENTS) * G1_BYTES;
    assert_eq!(
        check(&patched(&bytes, c, &[0; ZP_BYTES])),
        Err(Error::InvalidProof)
    );
}

/// The identity of `G_1` is encoded as `0xc0 ‖ 0^47` and round-trips; the all-zero string is no
/// encoding at all (evaluation.tex, "Implementation lessons", says it decodes to the identity).
#[test]
fn decoding_does_not_decide_validity() {
    let identity = identity_g1();
    assert_eq!(identity[0], 0xc0);
    assert!(identity[1..].iter().all(|b| *b == 0));
    assert!(G1::from_bytes(&identity).unwrap().is_zero());
    assert!(matches!(
        G1::from_bytes(&[0; G1_BYTES]),
        Err(Error::Serialization(_))
    ));
    validity::<PS, DDH>(b"ser/validity/ps", 0x5e25_0001);
    validity::<BBS, DY>(b"ser/validity/bbs", 0x5e25_0002);
}

/// The issuance record is a set; its encoding lists the identifiers in order (`BTreeSet`). A
/// decoder that is strict in the sense of the module docs of `serialization` ("every accepted
/// byte string is the unique encoding of the value it decodes to") refuses an encoding that
/// lists them out of order or twice. (arkworks decodes a set by collecting its elements, which
/// sorts and merges them; the decoder of `IssuanceRecord` checks the order itself.)
#[test]
fn issuance_record_encodings_are_unique() {
    let mut record = IssuanceRecord::new();
    let (a, b) = (
        G1::generator().to_bytes().unwrap(),
        (G1::generator() * Fr::from(2u64)).to_bytes().unwrap(),
    );
    record.record(&a).unwrap();
    record.record(&b).unwrap();
    let bytes = record.to_bytes().unwrap();
    let item = |id: &[u8]| [&(id.len() as u64).to_le_bytes()[..], id].concat();
    let (first, second) = if a < b { (&a, &b) } else { (&b, &a) };
    assert_eq!(
        bytes,
        [&2u64.to_le_bytes()[..], &item(first), &item(second)].concat()
    );
    let unsorted = [&2u64.to_le_bytes()[..], &item(second), &item(first)].concat();
    let repeated = [&2u64.to_le_bytes()[..], &item(first), &item(first)].concat();
    let accepted: Vec<String> = [("unsorted", unsorted), ("repeated", repeated)]
        .into_iter()
        .filter_map(|(what, encoding)| {
            let decoded = IssuanceRecord::from_bytes(&encoding).ok()?;
            let again = decoded.to_bytes().expect("re-encoding");
            assert_ne!(again, encoding, "{what}: not a non-canonical encoding");
            Some(format!(
                "{what}: decodes to {} identifier(s), whose encoding is another byte string \
                 ({} bytes, the input has {})",
                decoded.len(),
                again.len(),
                encoding.len()
            ))
        })
        .collect();
    assert!(
        accepted.is_empty(),
        "non-canonical encodings accepted: {accepted:#?}"
    );
}

// ---------------------------------------------------------------------------------------------
// FSProof
// ---------------------------------------------------------------------------------------------

/// A Fiat–Shamir proof `(c, z_1, …, z_n)` in its two encodings: the compact one is the NARG
/// string `c ‖ z` of `draft-irtf-cfrg-sigma-protocols-04` (§5.5, big-endian scalars) and takes `n`
/// from the caller (from the statement, never from the wire), the derived one is self-describing,
/// `n (u64, little-endian) ‖ c ‖ z`.
#[test]
fn fs_proof_encodings() {
    let mut rng = StdRng::seed_from_u64(0x5e26_0001);
    for n in [0usize, 1, 2, 7] {
        let proof = random_proof(n, &mut rng);
        let mut compact = Vec::new();
        proof.serialize_compact(&mut compact).unwrap();
        assert_eq!(compact.len(), (1 + n) * ZP_BYTES);
        assert_eq!(compact.len(), proof.compact_size());
        assert_eq!(compact, proof.to_narg());
        // big-endian: the challenge's canonical (little-endian) bytes, reversed
        let mut le = proof.challenge.to_bytes().unwrap();
        le.reverse();
        assert_eq!(compact[..32], le[..]);
        let derived = canonical(&proof, LEN_PREFIX + (1 + n) * ZP_BYTES)
            .to_bytes()
            .unwrap();
        assert_eq!(derived, insert(&compact, 0, &(n as u64).to_le_bytes()));

        // compact: n from the caller
        let mut reader = &compact[..];
        assert_eq!(
            FSProof::<Fr>::deserialize_compact(&mut reader, n).unwrap(),
            proof
        );
        assert!(reader.is_empty());
        assert!(matches!(
            FSProof::<Fr>::deserialize_compact(&compact[..], n + 1),
            Err(Error::Serialization(_))
        ));
        if n > 0 {
            // one response fewer: a prefix is read, one scalar is left behind
            let mut reader = &compact[..];
            let shorter = FSProof::<Fr>::deserialize_compact(&mut reader, n - 1).unwrap();
            assert_eq!(reader.len(), ZP_BYTES);
            assert_eq!(shorter.responses, proof.responses[..n - 1]);
        }
        for cut in 0..compact.len() {
            assert!(matches!(
                FSProof::<Fr>::deserialize_compact(&compact[..cut], n),
                Err(Error::Serialization(_))
            ));
        }
        for at in (0..=n).map(|i| i * ZP_BYTES) {
            let bad = patched(&compact, at, &Fr::MODULUS.to_bytes_be());
            assert!(matches!(
                FSProof::<Fr>::deserialize_compact(&bad[..], n),
                Err(Error::Serialization(_))
            ));
            let bad = patched(&derived, LEN_PREFIX + at, &[0xff; 32]);
            assert!(matches!(
                FSProof::<Fr>::from_bytes(&bad),
                Err(Error::Serialization(_))
            ));
        }

        // derived: a length that disagrees with the responses
        let with_len = |len: u64| patched(&derived, 0, &len.to_le_bytes());
        assert!(matches!(
            FSProof::<Fr>::from_bytes(&with_len(n as u64 + 1)),
            Err(Error::Serialization(_))
        ));
        assert!(matches!(
            FSProof::<Fr>::from_bytes(&with_len(u64::MAX)),
            Err(Error::Serialization(_))
        ));
        if n > 0 {
            assert_eq!(
                FSProof::<Fr>::from_bytes(&with_len(n as u64 - 1)),
                Err(Error::TrailingBytes)
            );
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Regression vectors
// ---------------------------------------------------------------------------------------------

/// Lower-case hexadecimal.
fn hex(bytes: &[u8]) -> String {
    use core::fmt::Write as _;
    let mut text = String::with_capacity(2 * bytes.len());
    for byte in bytes {
        write!(text, "{byte:02x}").expect("writing to a String");
    }
    text
}

/// REGRESSION vectors: the digest of `pp` for `Setup("kat")`, COMPUTED BY THIS IMPLEMENTATION
/// when the test was written and pinned here; they are not known answers from an external
/// source. The digest covers the framing of `pp` (the oracle suffix `/PCREDS-PP`, the item
/// labels and their order, the encodings of the items, the name of the instantiation) and the
/// oracles that derive the parameters (the generators of `Σ-BBS` and of `Tag_DY`, hashed to
/// `G_1`); `pp` no longer carries an identifier point (`x_0 = H_id(⟨hvk⟩)` is the key's). It leads every Fiat–Shamir context, so a change of any of these
/// silently breaks the interoperability of proofs between versions; this test makes it loud.
const PP_DIGEST_PS_DDH: &str = "211dcada9c04ab21dfcf6903a148428198338da6e9471dba6f985b7230e6e238";
const PP_DIGEST_BBS_DY: &str = "5ad4a7e62c00c62ca47d6c091a49353926ad3a060ad0b8d074b4efe6938b1f28";

fn digest<B: Format, T: TagFormat>(label: &[u8]) -> String {
    let pcreds = Protocol::<Bk<B, T>>::setup(label).unwrap();
    // deterministic, and a function of the published pp
    let again = Protocol::<Bk<B, T>>::setup(label).unwrap();
    assert_eq!(again.parameters_digest(), pcreds.parameters_digest());
    assert_eq!(
        pcreds.public_parameters().digest().unwrap(),
        *pcreds.parameters_digest()
    );
    let received =
        PublicParameters::<Bk<B, T>>::from_bytes(&pcreds.public_parameters().to_bytes().unwrap())
            .unwrap();
    let rebuilt = Protocol::<Bk<B, T>>::from_public_parameters(received).unwrap();
    assert_eq!(rebuilt.parameters_digest(), pcreds.parameters_digest());
    hex(pcreds.parameters_digest())
}

#[test]
fn parameter_digests_are_pinned() {
    assert_eq!(digest::<PS, DDH>(b"kat"), PP_DIGEST_PS_DDH);
    assert_eq!(digest::<BBS, DY>(b"kat"), PP_DIGEST_BBS_DY);
    // the instantiation and the label enter the digest
    assert_ne!(digest::<PS, DY>(b"kat"), PP_DIGEST_PS_DDH);
    assert_ne!(digest::<BBS, DDH>(b"kat"), PP_DIGEST_BBS_DY);
    assert_ne!(digest::<PS, DDH>(b"kat2"), PP_DIGEST_PS_DDH);
}

/// More REGRESSION vectors of this implementation (not external known answers): the contexts
/// of the four proofs, the identifier point `x_0 = H_id(⟨hvk⟩)` and the recipient point
/// `x_Q = H_req(⟨pp, hvk, id_Q, j_Q⟩)` under
/// `Setup("kat")` of `Σ-PS + Tag_DDH`, for a key, an identifier and an attestation built from
/// fixed scalars (no random number generator enters the vectors). They pin the framing of the
/// contexts (oracle suffixes, items, their order) and the derived encodings of the items, which
/// the digest of `pp` does not cover.
const CONTEXTS_PS_DDH: [&str; 6] = [
    // identifier_context(ssid, contact)
    "fcee2a843146c489df751f4bcc56366a5eeb83758f9582027f92efd3aa48ff6b",
    // attestation_context(hvk)
    "8f27f4d05692c733556ff03a367ad6b1cdb025a6415d3c686ae3b682758ce64a",
    // issuance_context(hvk, ssid, [att]): the attestation enters with its proof in the canonical
    // encoding `LE64(n) ‖ NARG string` (big-endian scalars, draft-irtf-cfrg-sigma-protocols-04).
    // Regenerated when the proofs moved to the drafts' encoding, and recomputed then by a Python
    // transcription of the framing from the unchanged encodings of `hvk`, `t` and `σ*`.
    "b4e8856b1818da7f763acb93415136ab503f3aa26972141e74fe6b02fa2c231f",
    // prove_context(hvk, message)
    "00150e595d70480528464efd404f90fda4b38e419c47288e3e550445210c15b5",
    // recipient_point(hvk, id), the canonical encoding of the scalar x_Q
    "a777e673b2f64ac93d1a6552fcaebeefc3da0d95364a210bbee59dc8bec4194e",
    // identifier_point(hvk), the canonical encoding of the scalar x_0
    "9bd27fe6e04b47c15957b3e998a73bbb31bead91d4a108bd6610fa93b786246a",
];

#[test]
fn proof_contexts_are_pinned() {
    let pcreds = Protocol::<Bk<PS, DDH>>::setup(b"kat").unwrap();
    let g1 = |k: u64| G1::generator() * Fr::from(k);
    let g2 = |k: u64| G2::generator() * Fr::from(k);
    let vk = PSVerificationKey::<E> {
        x2: g2(2),
        y2: g2(3),
        y1: g1(3),
    };
    let attestation = Attestation::<Bk<PS, DDH>> {
        tag: g1(7),
        show: PSPair {
            s1: g1(11),
            s2: g1(13),
        },
        proof: FSProof {
            challenge: Fr::from(17u64),
            responses: vec![Fr::from(19u64), Fr::from(23u64)],
        },
    };
    let contexts = [
        hex(&pcreds.identifier_context(b"ssid", b"contact")),
        hex(&pcreds.attestation_context(&vk).unwrap()),
        hex(&pcreds
            .issuance_context(&vk, b"ssid", &[attestation])
            .unwrap()),
        hex(&pcreds.prove_context(&vk, b"message").unwrap()),
        hex(&pcreds
            .recipient_point(&vk, &g1(5))
            .unwrap()
            .to_bytes()
            .unwrap()),
        hex(&pcreds.identifier_point(&vk).unwrap().to_bytes().unwrap()),
    ];
    assert_eq!(contexts, CONTEXTS_PS_DDH);
}
