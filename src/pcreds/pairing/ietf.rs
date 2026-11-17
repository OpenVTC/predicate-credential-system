//! Credential-level interoperability of `Σ-BBS` with IETF BBS: the BBS signature draft and its
//! blind-issuance and per-verifier-pseudonym companions (`draft-irtf-cfrg-bbs-signatures`,
//! `draft-irtf-cfrg-bbs-blind-signatures`, `draft-irtf-cfrg-bbs-per-verifier-linkability`),
//! ciphersuite BLS12-381-SHA-256, as implemented by the crate `affinidi-bbs` of the Affinidi /
//! OpenVTC stack (curve backend `bls12_381_plus`).
//!
//! Implementation note: nothing in this module is part of the paper. `Σ-BBS` (§6.2.2) takes the
//! generators `h_0, h_u, h_r` from `pp`, "derived by hashing fixed public labels to
//! `G_1 \ {1}`"; [`Base::setup`](super::Base::setup) derives them from the deployment label.
//! This module derives them the way the IETF ciphersuite does instead (also by hashing public
//! strings to `G_1`; in addition `h_0` depends on the helper's key and on a header, through
//! `domain`), which makes a credential of `Σ-BBS` and an IETF BBS signature THE SAME OBJECT.
//!
//! # The mapping
//!
//! A credential of `Σ-BBS` is `(A, e, ρ)` with `A^{x+e} = B(usk, ρ) = h_0 h_u^usk h_r^ρ`: the
//! paper reads `(A, e)` as a two-message BBS signature on `(usk, ρ)` (proof of the Lemma on
//! `Σ-BBS`). An IETF BBS signature is `(A, e)` with `A = B^{1/(SK + e)}` and
//! `B = P_1 · Q_1^{domain} · ∏ G_i^{m_i}`, verified by `e(A, PK · BP_2^e) = e(B, BP_2)`: the
//! `Verify` of `Σ-BBS` with `X̃ = PK`, `g̃ = BP_2` and
//!
//! ```text
//! h_0 := P_1 · Q_1^{domain}        (h_u, h_r) := the generators of the two signed values (usk, ρ)
//! ```
//!
//! where `domain = hash_to_scalar(PK ‖ L ‖ Q_1 ‖ G_1 ‖ … ‖ G_L ‖ api_id ‖ header)` over the `L`
//! generators of the signed values ([`calculate_domain`]). So `h_0` depends on the helper's key
//! and on the header, which is why [`BBSParams::ietf`] takes both. Which generators carry
//! `(usk, ρ)` depends on the [`Interface`]; in each of them the signature covers exactly these
//! two values, so `L = 2`:
//!
//! | [`Interface`] | `usk` | `ρ` | other signed values |
//! |---|---|---|---|
//! | [`Core`](Interface::Core): `Sign` / `Verify` | message 1, generator `H_1` | message 2, `H_2` | none |
//! | [`Blind`](Interface::Blind): `Commit` / `BlindSign` / `BlindVerify` | the committed message, `J_1` | `secret_prover_blind`, `Q_2` | no signer message |
//! | [`BlindPseudonym`](Interface::BlindPseudonym): `NymCommit` / `BlindSignWithNym` / `BlindVerifyWithNym` | the `nym_secret`, `J_1` | `secret_prover_blind`, `Q_2` | no signer message, no other committed message |
//!
//! In the blind interfaces the IETF prover's commitment is `C' = Q_2^{spb} J_1^{usk}`, and the
//! request of `Σ-BBS` is `C = B(usk, ρ) = h_0 · C'` for `ρ = spb`: the public part `h_0` that
//! the IETF signer multiplies in is already inside `C`, and `BlindIssue` signs `C` as it is.
//! The pre-credential `σ̂ = (A, e)` is therefore an IETF blind signature, and `BlindIssue` on
//! `h_0 · C'` answers an IETF commitment, outside the protocol: it checks neither the IETF
//! commitment proof (not implemented here) nor anything that `π_iss` proves. The two sides
//! choose `e` differently (IETF: a hash of `SK` and the signed data; `BlindIssue`: uniform),
//! which verification does not see.
//!
//! The byte encodings agree except for the endianness of scalars: compressed `G_1` / `G_2`
//! points are the same 48 / 96 bytes (ZCash format) in arkworks and in `bls12_381_plus`, while
//! scalars are big-endian (`I2OSP`) in IETF BBS and little-endian in arkworks. The
//! `to_ietf_bytes` / `from_ietf_bytes` methods below are that bridge; the two stacks share no
//! type. `ρ` is not part of an IETF signature (it is message 2, or the prover's
//! `secret_prover_blind`), so [`BBSCredential::from_ietf_bytes`] takes it separately.
//!
//! # Setting up a deployment
//!
//! The parameters depend on the helper's key, so the key exists first:
//!
//! 1. the helper's key pair: [`Base::keygen`](super::Base::keygen), or an IETF secret key
//!    ([`BBSSigningKey::from_ietf_bytes`] and [`BBSSigningKey::verification_key`]);
//! 2. `pp_Σ = BBSParams::ietf(interface, &hvk, header)`, and `pp_Tag` derived from the
//!    deployment label as in `Setup`:
//!    [`PairingParams`](super::PairingParams)` { base: pp_Σ, tag: T::setup(label)? }`;
//! 3. [`Protocol::setup_with_params`](crate::pcreds::Protocol::setup_with_params) on these
//!    parameters;
//! 4. the helper, from the key pair, through
//!    [`Protocol::helper_from_key_pair`](crate::pcreds::Protocol::helper_from_key_pair) (which
//!    checks that `sk` belongs to `hvk`); from then on it is stored and restored like any other
//!    helper ([`Helper::to_bytes`](crate::pcreds::Helper::to_bytes),
//!    [`Protocol::restore_helper`](crate::pcreds::Protocol::restore_helper));
//! 5. whoever receives `pp` recomputes the parameters from `(hvk, header, label)` and calls
//!    [`Protocol::from_public_parameters_with_params`](crate::pcreds::Protocol::from_public_parameters_with_params);
//!    [`Protocol::from_public_parameters`](crate::pcreds::Protocol::from_public_parameters)
//!    refuses them, as they are not derived from the label alone.
//!
//! `tests/bbs_ietf_interop.rs` runs these steps.
//!
//! # Transparency
//!
//! The points `Q_1`, `H_i`, `Q_2`, `J_i` are hash-to-curve outputs of fixed strings
//! ([`create_generators`]), and so is the constant `P_1` ([`p1`]): it is the first output of the
//! same derivation under the core `api_id` with the seed `api_id ‖ BP_MESSAGE_GENERATOR_SEED`
//! (checked by a unit test). Every party recomputes the parameters. A discrete-logarithm relation
//! among `(h_0, h_u, h_r)` is one among the four points `(P_1, Q_1, h_u, h_r)`, which depend on
//! neither the key nor the header: `h_0^a h_u^b h_r^c = 1` reads
//! `P_1^a Q_1^{a·domain} h_u^b h_r^c = 1`, whose exponent vector is nonzero whenever `(a, b, c)`
//! is. So a helper that chooses its key (or grinds the header) obtains no such relation unless it
//! knows one among four hash-to-curve outputs of fixed strings; with hash-to-curve modeled as a
//! random oracle, finding one is as hard as a discrete logarithm in `G_1` (the standard
//! reduction of the discrete-logarithm-relation problem to DL).
//!
//! Not claimed: the paper states the security of `Σ-BBS` (Lemma on `Σ-BBS`, Def. "BBS one-more
//! issuance") for parameters sampled BEFORE the key; here `h_0` is a function of the key. The
//! IETF drafts make this choice on purpose (`domain` binds `PK` and the header); that the
//! paper's lemma carries over to it is not shown here.
//!
//! # What is NOT covered
//!
//! * **The presentation.** A show of `Σ-BBS` is the two-randomizer IETF/TZ show `(Ā, B̄, D)`:
//!   IETF `ProofGen` computes the same `D = B^{r_2}`, `Ā = A^{r_1 r_2}`, `B̄ = D^{r_1} Ā^{-e}`,
//!   and the first two clauses of `Π_Possess`, `B̄ = D^{r_1} Ā^{-e}` and
//!   `h_0 = D^{r_3} h_u^{-usk} h_r^{-ρ}`, are the relations behind the commitments `T_1`, `T_2`
//!   of IETF `ProofGen` with both values undisclosed. The third clause `D = B̄^u Ā^v` "is not
//!   part of the IETF/TZ show" (§6.2.2, after the box); it costs two responses. The challenge
//!   (IETF: `hash_to_scalar` over the disclosed messages, `(Ā, B̄, D, T_1, T_2)`, `domain` and the
//!   presentation header; here: [`crate::sigma::fiat_shamir`] under the contexts of
//!   [`crate::pcreds`]), the
//!   AND-composition with the tag clause on the shared `usk`, and the byte layout differ as
//!   well. So neither an attestation nor a membership proof of this crate is an IETF BBS proof,
//!   and an IETF proof is not a proof of this crate.
//! * **Tags and pseudonyms.** The IETF per-verifier pseudonym is `OP^{nym_secret}` with
//!   `OP = hash_to_curve_g1(context_id)` under the pseudonym `api_id`; `Tag_DDH` is
//!   `htag(x)^usk` with this crate's oracle at a scalar point `x`. Under
//!   [`Interface::BlindPseudonym`] the two are clauses of the same shape on the same key, but
//!   not the same function.
//! * **Messages.** IETF BBS signs byte strings, mapped to scalars by [`message_to_scalar`]
//!   (core messages, committed messages); `secret_prover_blind`, `prover_nym` and
//!   `signer_nym_entropy` are scalars. This crate certifies the scalars `(usk, ρ)` themselves,
//!   and a credential crosses over only if both sides agree on them. Through an IETF API that
//!   takes byte strings, that is possible only for a value in the image of the map: `usk` in
//!   [`Interface::Blind`], both values in [`Interface::Core`]. `ρ` comes from `PrepareIssue`
//!   and is uniform, so a credential issued by the protocol under [`Interface::Core`] is an IETF
//!   signature that a byte-oriented IETF `Verify` cannot be asked to check.
//! * **The signer's pseudonym entropy.** In the pseudonym interface the IETF signer adds
//!   `signer_nym_entropy` to the committed `prover_nym`. The certified key is then
//!   `usk + entropy`, not the `usk` behind the user's identifier `id = Tag(usk, x_0)`; it equals
//!   `usk` for entropy `0`. `BlindIssue` adds nothing.
//! * **Their verifier.** A bridge keeps the checks of THIS crate (`hvk ∈ V_pp`, the public checks
//!   of `Π_Possess`, subgroup validation of everything received); it does not defer to another
//!   implementation's.
//! * **Scope.** Two signed values, no selective disclosure, and the ciphersuite
//!   BLS12-381-SHA-256 only.
//!
//! The hashing is pinned by the test vectors of RFC 9380 and by fixtures of the three drafts as
//! vendored by `affinidi-bbs` 0.3.3 (unit tests below); `tests/bbs_ietf_interop.rs` runs the
//! bridges against `affinidi-bbs` 0.3.3.

use ark_bls12_381::{Bls12_381, Fr, G1Affine, G1Projective, G2Affine, g1};
use ark_ec::{
    AffineRepr, CurveGroup, PrimeGroup,
    hashing::{HashToCurve, curve_maps::wb::WBMap, map_to_curve_hasher::MapToCurveBasedHasher},
};
use ark_ff::{BigInt, PrimeField, Zero, field_hashers::DefaultFieldHasher};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use sha2::{Digest, Sha256};
use zeroize::{Zeroize, Zeroizing};

use super::base::{BBSCredential, BBSParams, BBSSigningKey, BBSVerificationKey, is_valid};
use crate::error::Error;

/// The identifier of the ciphersuite BLS12-381-SHA-256 of IETF BBS.
pub const CIPHERSUITE_ID: &[u8] = b"BBS_BLS12381G1_XMD:SHA-256_SSWU_RO_";

/// `P_1` of BLS12-381-SHA-256, compressed.
const P1: [u8; G1_LEN] = [
    0xa8, 0xce, 0x25, 0x61, 0x02, 0x84, 0x08, 0x21, 0xa3, 0xe9, 0x4e, 0xa9, 0x02, 0x5e, 0x46, 0x62,
    0xb2, 0x05, 0x76, 0x2f, 0x97, 0x76, 0xb3, 0xa7, 0x66, 0xc8, 0x72, 0xb9, 0x48, 0xf1, 0xfd, 0x22,
    0x5e, 0x7c, 0x59, 0x69, 0x85, 0x88, 0xe7, 0x0d, 0x11, 0x40, 0x6d, 0x16, 0x1b, 0x4e, 0x28, 0xc9,
];

/// Output length of `expand_message` inside `hash_to_scalar` and `create_generators`:
/// `⌈(⌈log_2 r⌉ + 128) / 8⌉ = ⌈(255 + 128) / 8⌉ = 48`.
const EXPAND_LEN: usize = 48;
/// Size of an IETF scalar (`I2OSP(x, 32)`).
const SCALAR_LEN: usize = 32;
/// Size of a compressed `G_1` point.
const G1_LEN: usize = 48;
/// Size of a compressed `G_2` point (an IETF public key).
const G2_LEN: usize = 96;
/// Size of an IETF signature: `A` compressed, then `I2OSP(e, 32)`.
const SIGNATURE_LEN: usize = G1_LEN + SCALAR_LEN;

/// The interface of the BBS draft family that fixes the generators of `(usk, ρ)` and the domain
/// (module docs, "The mapping").
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Interface {
    /// `Sign` / `Verify` of the core draft over the two messages `(usk, ρ)`.
    Core,
    /// Blind signing with no signer message: the committed message `usk`, and
    /// `secret_prover_blind = ρ`.
    Blind,
    /// Blind signing with a pseudonym, with no signer message and no other committed message:
    /// the `nym_secret` `usk`, and `secret_prover_blind = ρ`.
    BlindPseudonym,
}

impl Interface {
    /// The `api_id` of the interface: the ciphersuite identifier followed by `H2G_HM2S_`,
    /// `BLIND_H2G_HM2S_` or `H2G_HM2S_PSEUDONYM_`.
    #[must_use]
    pub fn api_id(self) -> Vec<u8> {
        let suffix: &[u8] = match self {
            Self::Core => b"H2G_HM2S_",
            Self::Blind => b"BLIND_H2G_HM2S_",
            Self::BlindPseudonym => b"H2G_HM2S_PSEUDONYM_",
        };
        [CIPHERSUITE_ID, suffix].concat()
    }

    /// The `api_id` under which the generators of the COMMITTED part (`Q_2` and the `J_i`) are
    /// created, `BLIND_ ‖ api_id`; `None` for the core interface.
    #[must_use]
    pub fn blind_generators_api_id(self) -> Option<Vec<u8>> {
        match self {
            Self::Core => None,
            Self::Blind | Self::BlindPseudonym => Some([b"BLIND_", &self.api_id()[..]].concat()),
        }
    }
}

/// `expand_message_xmd` of RFC 9380 §5.3.1 with SHA-256.
///
/// Implementation note: arkworks' expander is not used for scalars, because its padding
/// differs from the RFC when the output is not a base-field element (module [`crate::hash`],
/// "Hash to field").
///
/// # Errors
/// [`Error::LengthMismatch`] if `dst` is longer than 255 bytes, more than 255 blocks of 32 bytes
/// are requested, or `len` exceeds 65535.
pub fn expand_message_xmd(msg: &[u8], dst: &[u8], len: usize) -> Result<Vec<u8>, Error> {
    const BLOCK: usize = 32;
    let ell = len.div_ceil(BLOCK);
    let (Ok(dst_len), Ok(len_u16), Ok(ell_u8)) = (
        u8::try_from(dst.len()),
        u16::try_from(len),
        u8::try_from(ell),
    ) else {
        return Err(Error::LengthMismatch {
            expected: 255,
            actual: dst.len().max(ell),
        });
    };
    let block = |parts: &[&[u8]]| {
        let mut h = Sha256::new();
        for part in parts {
            h.update(part);
        }
        h.update(dst);
        h.update([dst_len]);
        h.finalize()
    };
    // b_0 = H(Z_pad ‖ msg ‖ I2OSP(len, 2) ‖ 0 ‖ DST'),  b_1 = H(b_0 ‖ 1 ‖ DST')
    let b0 = block(&[&[0u8; 64], msg, &len_u16.to_be_bytes(), &[0u8]]);
    let mut bi = block(&[&b0, &[1u8]]);
    // Sized up front (at most 255 blocks), so that no partial copy is left behind by a move.
    let mut out = Vec::with_capacity(usize::from(ell_u8.max(1)) * BLOCK);
    out.extend_from_slice(&bi);
    for i in 2..=ell_u8 {
        // b_i = H((b_0 XOR b_{i-1}) ‖ i ‖ DST')
        let xored: Zeroizing<Vec<u8>> =
            Zeroizing::new(b0.iter().zip(&bi).map(|(a, b)| a ^ b).collect());
        bi = block(&[&xored, &[i]]);
        out.extend_from_slice(&bi);
    }
    out.truncate(len);
    Ok(out)
}

/// `hash_to_scalar(msg, dst) = OS2IP(expand_message(msg, dst, 48)) mod r`. The expanded bytes
/// are wiped (the message may be secret, e.g. a committed message that maps to `usk`).
///
/// # Errors
/// As [`expand_message_xmd`].
pub fn hash_to_scalar(msg: &[u8], dst: &[u8]) -> Result<Fr, Error> {
    let uniform = Zeroizing::new(expand_message_xmd(msg, dst, EXPAND_LEN)?);
    Ok(Fr::from_be_bytes_mod_order(&uniform))
}

/// The scalar that IETF BBS signs for the byte string `message` in the given interface
/// (`messages_to_scalars`, under `api_id ‖ MAP_MSG_TO_SCALAR_AS_HASH_`); in the blind interfaces
/// the same map applies to committed messages.
///
/// # Errors
/// As [`expand_message_xmd`].
pub fn message_to_scalar(interface: Interface, message: &[u8]) -> Result<Fr, Error> {
    let dst = [&interface.api_id()[..], b"MAP_MSG_TO_SCALAR_AS_HASH_"].concat();
    hash_to_scalar(message, &dst)
}

/// `hash_to_curve_g1` of the suite `BLS12381G1_XMD:SHA-256_SSWU_RO_` of RFC 9380 under the tag
/// `dst` (for a base-field output, arkworks' expander is the RFC's).
fn hash_to_curve_g1(msg: &[u8], dst: &[u8]) -> Result<G1Projective, Error> {
    type Suite =
        MapToCurveBasedHasher<G1Projective, DefaultFieldHasher<Sha256, 128>, WBMap<g1::Config>>;
    let suite = <Suite as HashToCurve<G1Projective>>::new(dst)?;
    Ok(suite.hash(msg)?.into())
}

/// The generator derivation of the drafts with an explicit seed and tags: `v_0 =
/// expand_message(generator_seed, seed_dst, 48)`, then for `i = 1, …, count`:
/// `v_i = expand_message(v_{i-1} ‖ I2OSP(i, 8), seed_dst, 48)` and
/// `G_i = hash_to_curve_g1(v_i, generator_dst)`.
fn hash_to_generators(
    count: usize,
    generator_seed: &[u8],
    seed_dst: &[u8],
    generator_dst: &[u8],
) -> Result<Vec<G1Projective>, Error> {
    let mut v = expand_message_xmd(generator_seed, seed_dst, EXPAND_LEN)?;
    // Not pre-allocated: `count` is the caller's.
    let mut generators = Vec::new();
    for i in 1..=count as u64 {
        v = expand_message_xmd(&[&v[..], &i.to_be_bytes()].concat(), seed_dst, EXPAND_LEN)?;
        generators.push(hash_to_curve_g1(&v, generator_dst)?);
    }
    Ok(generators)
}

/// `create_generators(count, api_id)`: the points `(Q_1, H_1, …, H_{count-1})` for the `api_id`
/// of an interface, `(Q_2, J_1, …, J_{count-1})` for its blind-generator `api_id`
/// ([`Interface::blind_generators_api_id`]).
///
/// # Errors
/// As [`expand_message_xmd`]; [`Error::HashToCurve`] if the suite fails.
pub fn create_generators(count: usize, api_id: &[u8]) -> Result<Vec<G1Projective>, Error> {
    hash_to_generators(
        count,
        &[api_id, b"MESSAGE_GENERATOR_SEED"].concat(),
        &[api_id, b"SIG_GENERATOR_SEED_"].concat(),
        &[api_id, b"SIG_GENERATOR_DST_"].concat(),
    )
}

/// The fixed point `P_1` of the ciphersuite.
///
/// # Errors
/// Never in practice: the constant is a valid point (pinned by a unit test).
pub fn p1() -> Result<G1Projective, Error> {
    Ok(G1Affine::deserialize_compressed(&P1[..])?.into())
}

/// `calculate_domain(PK, Q_1, (G_1, …, G_L), header, api_id)`: `hash_to_scalar` of
/// `PK ‖ I2OSP(L, 8) ‖ Q_1 ‖ G_1 ‖ … ‖ G_L ‖ api_id ‖ I2OSP(len(header), 8) ‖ header` under the
/// tag `api_id ‖ H2S_`.
///
/// # Errors
/// As [`expand_message_xmd`]; [`Error::Serialization`] if a point cannot be encoded.
pub fn calculate_domain(
    vk: &BBSVerificationKey<Bls12_381>,
    q1: &G1Projective,
    generators: &[G1Projective],
    header: &[u8],
    api_id: &[u8],
) -> Result<Fr, Error> {
    let mut data = vk.to_ietf_bytes()?.to_vec();
    data.extend_from_slice(&(generators.len() as u64).to_be_bytes());
    for point in core::iter::once(q1).chain(generators) {
        point.into_affine().serialize_compressed(&mut data)?;
    }
    data.extend_from_slice(api_id);
    data.extend_from_slice(&(header.len() as u64).to_be_bytes());
    data.extend_from_slice(header);
    hash_to_scalar(&data, &[api_id, b"H2S_"].concat())
}

/// An IETF scalar (`I2OSP(x, 32)`, big-endian) as a field element. The intermediate integer is
/// wiped.
///
/// # Errors
/// [`Error::LengthMismatch`] unless there are 32 bytes; [`Error::Serialization`] if the value is
/// not reduced modulo the group order.
pub fn scalar_from_be_bytes(bytes: &[u8]) -> Result<Fr, Error> {
    let Ok(bytes) = <&[u8; SCALAR_LEN]>::try_from(bytes) else {
        return Err(Error::LengthMismatch {
            expected: SCALAR_LEN,
            actual: bytes.len(),
        });
    };
    // Little-endian limbs, the most significant one first in the big-endian bytes.
    let mut limbs = BigInt::<4>::default();
    for (limb, word) in limbs.0.iter_mut().rev().zip(bytes.as_chunks::<8>().0) {
        *limb = u64::from_be_bytes(*word);
    }
    let scalar = Fr::from_bigint(limbs);
    limbs.zeroize();
    scalar.ok_or_else(|| Error::Serialization("the scalar is not reduced modulo r".into()))
}

/// Writes `I2OSP(x, 32)` into `out`; the intermediate integer is wiped.
fn write_be(scalar: &Fr, out: &mut [u8; SCALAR_LEN]) {
    let mut limbs = scalar.into_bigint();
    for (word, limb) in out
        .as_chunks_mut::<8>()
        .0
        .iter_mut()
        .zip(limbs.0.iter().rev())
    {
        *word = limb.to_be_bytes();
    }
    limbs.zeroize();
}

/// A field element as an IETF scalar (`I2OSP(x, 32)`, big-endian).
#[must_use]
pub fn scalar_to_be_bytes(scalar: &Fr) -> [u8; SCALAR_LEN] {
    let mut out = [0u8; SCALAR_LEN];
    write_be(scalar, &mut out);
    out
}

impl BBSParams<Bls12_381> {
    /// The parameters under which a credential `(A, e, ρ)` of `Σ-BBS` on `usk` IS an IETF BBS
    /// signature `(A, e)` of the helper key `vk` on the two values `(usk, ρ)` under `header`
    /// (module docs, "The mapping"): `h_0 = P_1 · Q_1^{domain}`, and `(h_u, h_r)` the generators
    /// of `(usk, ρ)` in the given [`Interface`], with `domain` over exactly these two
    /// generators.
    ///
    /// Like the parameters of [`Base::setup`](super::Base::setup) they are transparent: a
    /// function of public constants, the helper's key and the header, which every party
    /// recomputes instead of trusting a received copy. Unlike them they depend on the key, so a
    /// deployment is set up with them AFTER the helper's key exists (module docs, "Setting up a
    /// deployment").
    ///
    /// # Errors
    /// [`Error::InvalidGroupElement`] if `vk` is not an element of `G_2`; [`Error::InvalidKey`]
    /// if `vk` is the identity (refused by IETF `KeyValidate`, although `V_pp = G_2` for
    /// `Σ-BBS`); [`Error::DegenerateInput`] if a derived generator is the identity (for `h_0`:
    /// one value of `domain` out of `r`); the errors of [`create_generators`] and
    /// [`calculate_domain`].
    pub fn ietf(
        interface: Interface,
        vk: &BBSVerificationKey<Bls12_381>,
        header: &[u8],
    ) -> Result<Self, Error> {
        if !is_valid(vk) {
            return Err(Error::InvalidGroupElement("hvk"));
        }
        if vk.0.is_zero() {
            return Err(Error::InvalidKey);
        }
        let api_id = interface.api_id();
        // (Q_1, the generator of usk, the generator of ρ), and the list the domain covers in the
        // order of the signed values
        let (q1, hu, hr, covered) = match interface.blind_generators_api_id() {
            None => match create_generators(3, &api_id)?[..] {
                [q1, h1, h2] => (q1, h1, h2, [h1, h2]),
                _ => return Err(Error::DegenerateInput("IETF generators")),
            },
            Some(blind_api_id) => {
                // no signer message: (Q_1) alone; the committed part: (Q_2, J_1)
                let signer = create_generators(1, &api_id)?;
                let blind = create_generators(2, &blind_api_id)?;
                match (&signer[..], &blind[..]) {
                    ([q1], [q2, j1]) => (*q1, *j1, *q2, [*q2, *j1]),
                    _ => return Err(Error::DegenerateInput("IETF generators")),
                }
            }
        };
        let domain = calculate_domain(vk, &q1, &covered, header, &api_id)?;
        let pp = Self {
            h0: p1()? + q1 * domain,
            hu,
            hr,
        };
        if pp.h0.is_zero() || pp.hu.is_zero() || pp.hr.is_zero() {
            return Err(Error::DegenerateInput("BBS generators"));
        }
        Ok(pp)
    }
}

impl BBSVerificationKey<Bls12_381> {
    /// The key as an IETF public key: the 96 bytes of the compressed `G_2` point.
    ///
    /// # Errors
    /// [`Error::Serialization`] if the point cannot be encoded.
    pub fn to_ietf_bytes(&self) -> Result<[u8; G2_LEN], Error> {
        let mut out = [0u8; G2_LEN];
        self.0.into_affine().serialize_compressed(&mut out[..])?;
        Ok(out)
    }

    /// An IETF public key as a verification key, validated (on the curve, in the subgroup) and
    /// not the identity (IETF `KeyValidate`).
    ///
    /// # Errors
    /// [`Error::LengthMismatch`] unless there are 96 bytes; [`Error::Serialization`] for an
    /// invalid point; [`Error::InvalidKey`] for the identity.
    pub fn from_ietf_bytes(bytes: &[u8]) -> Result<Self, Error> {
        if bytes.len() != G2_LEN {
            return Err(Error::LengthMismatch {
                expected: G2_LEN,
                actual: bytes.len(),
            });
        }
        let point = G2Affine::deserialize_compressed(bytes)?;
        if point.is_zero() {
            return Err(Error::InvalidKey);
        }
        Ok(Self(point.into()))
    }
}

impl BBSSigningKey<Bls12_381> {
    /// The key as an IETF secret key (`I2OSP(SK, 32)`), in a buffer that is wiped on drop.
    #[must_use]
    pub fn to_ietf_bytes(&self) -> Zeroizing<[u8; SCALAR_LEN]> {
        let mut out = Zeroizing::new([0u8; SCALAR_LEN]);
        write_be(&self.0, &mut out);
        out
    }

    /// An IETF secret key as a signing key.
    ///
    /// # Errors
    /// As [`scalar_from_be_bytes`]; [`Error::InvalidKey`] for `SK = 0`, which is not an IETF
    /// secret key.
    pub fn from_ietf_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let mut x = scalar_from_be_bytes(bytes)?;
        if x.is_zero() {
            return Err(Error::InvalidKey);
        }
        let key = Self(x);
        x.zeroize();
        Ok(key)
    }

    /// The verification key `X̃ = g̃^x` (IETF `SkToPk`, with `BP_2 = g̃`).
    #[must_use]
    pub fn verification_key(&self) -> BBSVerificationKey<Bls12_381> {
        BBSVerificationKey(<Bls12_381 as ark_ec::pairing::Pairing>::G2::generator() * self.0)
    }
}

impl BBSCredential<Bls12_381> {
    /// The signature `(A, e)` of the credential as an IETF BBS signature: `A` compressed
    /// (48 bytes) followed by `I2OSP(e, 32)`. The certified `ρ` is not part of it.
    ///
    /// # Errors
    /// [`Error::Serialization`] if the point cannot be encoded.
    pub fn to_ietf_bytes(&self) -> Result<[u8; SIGNATURE_LEN], Error> {
        let mut out = [0u8; SIGNATURE_LEN];
        self.a
            .into_affine()
            .serialize_compressed(&mut out[..G1_LEN])?;
        let mut e = [0u8; SCALAR_LEN];
        write_be(&self.e, &mut e);
        out[G1_LEN..].copy_from_slice(&e);
        Ok(out)
    }

    /// The credential `(A, e, ρ)` from an IETF BBS signature `(A, e)` (validated point, reduced
    /// scalar) and the certified value `ρ`: message 2 in [`Interface::Core`],
    /// `secret_prover_blind` in the blind interfaces. As everywhere, decoding says nothing
    /// about validity: `Verify` does
    /// ([`Protocol::credential`](crate::pcreds::Protocol::credential) runs it).
    ///
    /// # Errors
    /// [`Error::LengthMismatch`] unless there are 80 bytes; [`Error::Serialization`] for an
    /// invalid point or scalar.
    pub fn from_ietf_bytes(signature: &[u8], rho: &Fr) -> Result<Self, Error> {
        if signature.len() != SIGNATURE_LEN {
            return Err(Error::LengthMismatch {
                expected: SIGNATURE_LEN,
                actual: signature.len(),
            });
        }
        let (a, e) = signature.split_at(G1_LEN);
        Ok(Self {
            a: G1Affine::deserialize_compressed(a)?.into(),
            e: scalar_from_be_bytes(e)?,
            rho: *rho,
        })
    }
}

#[cfg(test)]
mod tests {
    use ark_ec::pairing::Pairing;
    use ark_ff::{BigInteger, UniformRand};
    use rand::{SeedableRng, rngs::StdRng};

    use super::*;
    use crate::{
        hash::bls12_381::G1Hasher,
        pcreds::pairing::{BBS, Base, pairing_product_is_identity},
    };

    type Bbs = BBS<G1Hasher>;
    type G2 = <Bls12_381 as Pairing>::G2;

    fn hex(text: &str) -> Vec<u8> {
        (0..text.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&text[i..i + 2], 16).unwrap())
            .collect()
    }

    fn compressed(point: &G1Projective) -> Vec<u8> {
        let mut out = Vec::new();
        point.into_affine().serialize_compressed(&mut out).unwrap();
        out
    }

    /// `e(A, X̃ g̃^e) = e(B, g̃)`, the equation of IETF `Verify` and of `Verify` of `Σ-BBS`.
    fn signs(
        vk: &BBSVerificationKey<Bls12_381>,
        signature: &BBSCredential<Bls12_381>,
        b: &G1Projective,
    ) -> bool {
        let g2 = G2::generator();
        pairing_product_is_identity::<Bls12_381>(&[
            (signature.a, vk.0 + g2 * signature.e),
            (-*b, g2),
        ])
    }

    /// The key and header shared by the fixtures of the three drafts (as vendored by
    /// affinidi-bbs 0.3.3, `tests/vectors/`).
    const FIXTURE_PK: &str = "a820f230f6ae38503b86c70dc50b61c58a77e45c39ab25c0652bbaa8fa136f2851bd4781c9dcde39fc9d\
                              1d52c9e60268061e7d7632171d91aa8d460acee0e96f1e7c4cfb12d3ff9ab5d5dc91c277db75c845d649\
                              ef3c4f63aebc364cd55ded0c";
    const FIXTURE_HEADER: &str = "11223344556677889900aabbccddeeff";

    /// RFC 9380, Appendix K.1 (`expand_message_xmd`, SHA-256,
    /// DST `QUUX-V01-CS02-with-expander-SHA256-128`, `len_in_bytes = 0x20`).
    #[test]
    fn expand_message_xmd_matches_rfc_9380() {
        let dst = b"QUUX-V01-CS02-with-expander-SHA256-128";
        for (msg, expected) in [
            (
                &b""[..],
                "68a985b87eb6b46952128911f2a4412bbc302a9d759667f87f7a21d803f07235",
            ),
            (
                &b"abc"[..],
                "d8ccab23b5985ccea865c6c97b6e5b8350e794e603b4b97902f53a8a0d605615",
            ),
        ] {
            assert_eq!(expand_message_xmd(msg, dst, 0x20).unwrap(), hex(expected));
        }
        // several blocks, and the limits of the encoding
        assert_eq!(expand_message_xmd(b"abc", dst, 100).unwrap().len(), 100);
        assert!(expand_message_xmd(b"", &[0u8; 256], 32).is_err());
        assert!(expand_message_xmd(b"", dst, 256 * 32).is_err());
    }

    /// The fixture "valid multi-message signature" (`signature004`) of the core draft: its
    /// trace pins `domain` and `B`, hence `P_1`, `create_generators`, `calculate_domain` and
    /// `message_to_scalar` of [`Interface::Core`] at once (over ten messages; the two-message
    /// parameters of [`BBSParams::ietf`] run the same code).
    #[test]
    fn core_fixture_pins_domain_and_b() {
        let vk = BBSVerificationKey::from_ietf_bytes(&hex(FIXTURE_PK)).unwrap();
        let header = hex(FIXTURE_HEADER);
        let messages = [
            "9872ad089e452c7b6e283dfac2a80d58e8d0ff71cc4d5e310a1debdda4a45f02",
            "c344136d9ab02da4dd5908bbba913ae6f58c2cc844b802a6f811f5fb075f9b80",
            "7372e9daa5ed31e6cd5c825eac1b855e84476a1d94932aa348e07b73",
            "77fe97eb97a1ebe2e81e4e3597a3ee740a66e9ef2412472c",
            "496694774c5604ab1b2544eababcf0f53278ff50",
            "515ae153e22aae04ad16f759e07237b4",
            "d183ddc6e2665aa4e2f088af",
            "ac55fb33a75909ed",
            "96012096",
            "",
        ];
        let api_id = Interface::Core.api_id();
        let generators = create_generators(messages.len() + 1, &api_id).unwrap();
        let domain =
            calculate_domain(&vk, &generators[0], &generators[1..], &header, &api_id).unwrap();
        assert_eq!(
            scalar_to_be_bytes(&domain).to_vec(),
            hex("6272832582a0ac96e6fe53e879422f24c51680b25fbf17bad22a35ea93ce5b47")
        );
        let mut b = p1().unwrap() + generators[0] * domain;
        for (message, generator) in messages.iter().zip(&generators[1..]) {
            b += *generator * message_to_scalar(Interface::Core, &hex(message)).unwrap();
        }
        assert_eq!(
            compressed(&b),
            hex(
                "84f48376f7df6af40bc329cf484cdbfd0b19d0b326fccab4e9d8f00d1dbcf48139d498b19667f203cf8a\
                 1d1f8340c522"
            )
        );
        // … and the fixture's signature satisfies the equation of Verify for this B
        let signature = BBSCredential::from_ietf_bytes(
            &hex(
                "8339b285a4acd89dec7777c09543a43e3cc60684b0a6f8ab335da4825c96e1463e28f8c5f4fd0641d19c\
                 ec5920d3a8ff4bedb6c9691454597bbd298288abed3632078557b2ace7d44caed846e1a0a1e8",
            ),
            &Fr::zero(),
        )
        .unwrap();
        assert!(signs(&vk, &signature, &b));
    }

    /// `P_1` is itself a hash-to-curve output of a fixed string: the first point of the
    /// generator derivation under the core `api_id` with the seed
    /// `api_id ‖ BP_MESSAGE_GENERATOR_SEED` (in place of `api_id ‖ MESSAGE_GENERATOR_SEED`).
    /// Checked here, not taken from the draft's text; module docs, "Transparency".
    #[test]
    fn p1_is_a_hash_to_curve_output() {
        let api_id = Interface::Core.api_id();
        let derived = hash_to_generators(
            1,
            &[&api_id[..], b"BP_MESSAGE_GENERATOR_SEED"].concat(),
            &[&api_id[..], b"SIG_GENERATOR_SEED_"].concat(),
            &[&api_id[..], b"SIG_GENERATOR_DST_"].concat(),
        )
        .unwrap();
        assert_eq!(derived, vec![p1().unwrap()]);
        // and it is none of the message generators
        assert!(!create_generators(3, &api_id).unwrap().contains(&derived[0]));
    }

    /// The fixture "Multiple Prover Committed Messages, No Signer Messages" of the blind draft:
    /// a blind signature with NO signer message over five committed messages. It pins the blind
    /// namespacing (`api_id` and `BLIND_ ‖ api_id`), both generator lists, `message_to_scalar`
    /// of committed messages, and `calculate_domain` over `(Q_2, J_1, …, J_5)` with no signer
    /// generator: the shape of [`BBSParams::ietf`] for [`Interface::Blind`], which has one
    /// committed message.
    #[test]
    fn blind_fixture_with_no_signer_messages() {
        let vk = BBSVerificationKey::from_ietf_bytes(&hex(FIXTURE_PK)).unwrap();
        let header = hex(FIXTURE_HEADER);
        let committed = [
            "5982967821da3c5983496214df36aa5e58de6fa25314af4cf4c00400779f08c3",
            "a75d8b634891af92282cc81a675972d1929d3149863c1fc0",
            "835889a40744813a892eff9deb1edaeb",
            "e1ca9729410dc6ba",
            "",
        ];
        let spb = scalar_from_be_bytes(&hex(
            "4fba5396baa36b2fde81d46a9b9ee89c425dbc5e1ffd65c20249afb4abd37589",
        ))
        .unwrap();
        let signature = BBSCredential::from_ietf_bytes(
            &hex(
                "b7446e6ae4e8b5707ac0108f3b1049e9ea01bd6b2b4a7dcf06e5ad1c62a9c0b1585829f0e30fba6c97\
                 61469ed908deca52ba5499cef2827b99527b4adf1f30522ce32366385ba87594b8d0e44d156eec",
            ),
            &spb,
        )
        .unwrap();
        let b = |interface: Interface, spb: &Fr| {
            let api_id = interface.api_id();
            let q1 = create_generators(1, &api_id).unwrap()[0];
            let blind = create_generators(
                committed.len() + 1,
                &interface.blind_generators_api_id().unwrap(),
            )
            .unwrap();
            let domain = calculate_domain(&vk, &q1, &blind, &header, &api_id).unwrap();
            let mut b = p1().unwrap() + q1 * domain + blind[0] * spb;
            for (message, generator) in committed.iter().zip(&blind[1..]) {
                b += *generator * message_to_scalar(interface, &hex(message)).unwrap();
            }
            b
        };
        assert!(signs(&vk, &signature, &b(Interface::Blind, &spb)));
        // checks that can fail: another blind, another namespace
        assert!(!signs(
            &vk,
            &signature,
            &b(Interface::Blind, &(spb + Fr::from(1u64)))
        ));
        assert!(!signs(&vk, &signature, &b(Interface::BlindPseudonym, &spb)));
    }

    /// The fixture "no prover committed, no signer messages" of the pseudonym draft is EXACTLY a
    /// credential of `Σ-BBS` under `BBSParams::ietf(BlindPseudonym, PK, header)`: a signature on
    /// `(secret_prover_blind, nym_secret)` over `(Q_2, J_1)`, the certified key being
    /// `nym_secret = prover_nym + signer_nym_entropy` (module docs, "The signer's pseudonym
    /// entropy").
    #[test]
    fn pseudonym_fixture_is_a_credential_under_ietf_parameters() {
        let vk = BBSVerificationKey::from_ietf_bytes(&hex(FIXTURE_PK)).unwrap();
        let header = hex(FIXTURE_HEADER);
        let scalar = |text: &str| scalar_from_be_bytes(&hex(text)).unwrap();
        let prover_nym = scalar("6830ea571e9fca0194d9ebd5c571369d8b81655afe0bbb9c6f5efe934f699418");
        let entropy = scalar("3d40961fce6c09eec24a371322732932503b458d7a4cf7891bdaa765b30027c5");
        let nym_secret = scalar("3183d923c36e56a823ea4ae0de4287ca87ff06e5785a57268b39a5fa0269bbdc");
        assert_eq!(prover_nym + entropy, nym_secret);
        let spb = scalar("3ba0a2583bc7229fa9f2ae3a6697091032947c3a48f302b7fd2b08ca9d193041");
        let cred = BBSCredential::from_ietf_bytes(
            &hex(
                "8e0595c93044ff2da97c466418ea0eb8648f1ed5cb040f90decb338810c5db168a464eacba02eb9dec\
                 7659920e59409a1faff9a30512ac66886db438787b463125e08e5aeaf4f4467a066dbd1520a984",
            ),
            &spb,
        )
        .unwrap();
        let verify = |interface: Interface, usk: &Fr, cred: &BBSCredential<Bls12_381>| {
            let pp = BBSParams::ietf(interface, &vk, &header).unwrap();
            <Bbs as Base<Bls12_381>>::verify(&pp, &vk, usk, cred)
        };
        assert!(verify(Interface::BlindPseudonym, &nym_secret, &cred));
        // the signer's entropy moved the key; the blind is certified; the namespace matters
        assert!(!verify(Interface::BlindPseudonym, &prover_nym, &cred));
        let other_blind = BBSCredential {
            rho: spb + Fr::from(1u64),
            ..cred.clone()
        };
        assert!(!verify(
            Interface::BlindPseudonym,
            &nym_secret,
            &other_blind
        ));
        assert!(!verify(Interface::Blind, &nym_secret, &cred));
        assert!(!verify(Interface::Core, &nym_secret, &cred));
    }

    /// A point on the twist that is not in the prime-order subgroup `G_2`.
    fn outside_g2() -> G2Affine {
        (1u64..)
            .find_map(|x| {
                G2Affine::get_point_from_x_unchecked(ark_bls12_381::Fq2::from(x), true)
                    .filter(|point| !point.is_in_correct_subgroup_assuming_on_curve())
            })
            .unwrap()
    }

    #[test]
    fn parameters_depend_on_interface_key_and_header() {
        let mut rng = StdRng::seed_from_u64(0x1e7f_0001);
        let mut key = || BBSSigningKey::<Bls12_381>(Fr::rand(&mut rng)).verification_key();
        let (vk, other) = (key(), key());
        let interfaces = [Interface::Core, Interface::Blind, Interface::BlindPseudonym];
        let ietf = |interface, vk: &BBSVerificationKey<Bls12_381>, header: &[u8]| {
            BBSParams::ietf(interface, vk, header).unwrap()
        };
        for interface in interfaces {
            let pp = ietf(interface, &vk, b"header");
            // deterministic and well formed
            assert_eq!(pp, ietf(interface, &vk, b"header"));
            assert_eq!(<Bbs as Base<Bls12_381>>::check_params(&pp), Ok(()));
            // h_0 is a function of the key and of the header …
            assert_ne!(pp.h0, ietf(interface, &other, b"header").h0);
            assert_ne!(pp.h0, ietf(interface, &vk, b"another header").h0);
            // … (h_u, h_r) of the interface alone
            let again = ietf(interface, &other, b"another header");
            assert_eq!((pp.hu, pp.hr), (again.hu, again.hr));
            assert_ne!(pp.hu, pp.hr);
        }
        // the interfaces are separated, and none gives the label-derived parameters
        let all = interfaces.map(|interface| ietf(interface, &vk, b"header"));
        for (i, a) in all.iter().enumerate() {
            for b in &all[i + 1..] {
                assert!(a.h0 != b.h0 && a.hu != b.hu && a.hr != b.hr);
            }
            assert_ne!(*a, <Bbs as Base<Bls12_381>>::setup(b"header").unwrap());
        }
        // the identity is not an IETF key, and a point outside G_2 is no key at all
        assert_eq!(
            BBSParams::ietf(Interface::Core, &BBSVerificationKey(G2::zero()), b"header"),
            Err(Error::InvalidKey)
        );
        assert_eq!(
            BBSParams::ietf(
                Interface::Core,
                &BBSVerificationKey(outside_g2().into()),
                b"header"
            ),
            Err(Error::InvalidGroupElement("hvk"))
        );
    }

    #[test]
    fn byte_bridges_round_trip_and_are_strict() {
        let mut rng = StdRng::seed_from_u64(0x1e7f_0002);
        // scalars: big-endian, canonical; arkworks' little-endian encoding reversed
        let x = Fr::rand(&mut rng);
        let mut le = Vec::new();
        x.serialize_compressed(&mut le).unwrap();
        le.reverse();
        assert_eq!(scalar_to_be_bytes(&x).to_vec(), le);
        assert_eq!(scalar_from_be_bytes(&scalar_to_be_bytes(&x)).unwrap(), x);
        let one = scalar_to_be_bytes(&Fr::from(1u64));
        assert!(one[31] == 1 && one[..31].iter().all(|b| *b == 0));
        // r - 1 is the largest scalar; r, 2^256 - 1 and short inputs are refused
        let minus_one = -Fr::from(1u64);
        assert_eq!(
            scalar_from_be_bytes(&scalar_to_be_bytes(&minus_one)).unwrap(),
            minus_one
        );
        let modulus = Fr::MODULUS.to_bytes_be();
        assert!(matches!(
            scalar_from_be_bytes(&modulus),
            Err(Error::Serialization(_))
        ));
        assert!(scalar_from_be_bytes(&[0xff; 32]).is_err());
        assert_eq!(
            scalar_from_be_bytes(&[0u8; 31]),
            Err(Error::LengthMismatch {
                expected: 32,
                actual: 31
            })
        );

        // signing keys; SkToPk agrees with the base's key check
        let sk = BBSSigningKey::<Bls12_381>(Fr::rand(&mut rng));
        let vk = sk.verification_key();
        let pp = BBSParams::ietf(Interface::Core, &vk, b"header").unwrap();
        assert!(<Bbs as Base<Bls12_381>>::key_pair_matches(&pp, &vk, &sk));
        let back = BBSSigningKey::from_ietf_bytes(&sk.to_ietf_bytes()[..]).unwrap();
        assert!(<Bbs as Base<Bls12_381>>::key_pair_matches(&pp, &vk, &back));
        assert_eq!(
            BBSSigningKey::<Bls12_381>::from_ietf_bytes(&[0u8; 32]).err(),
            Some(Error::InvalidKey)
        );

        // verification keys: validated, not the identity
        assert_eq!(
            BBSVerificationKey::from_ietf_bytes(&vk.to_ietf_bytes().unwrap()).unwrap(),
            vk
        );
        assert!(BBSVerificationKey::<Bls12_381>::from_ietf_bytes(&[0u8; 95]).is_err());
        let identity = BBSVerificationKey::<Bls12_381>(G2::zero());
        assert_eq!(
            BBSVerificationKey::<Bls12_381>::from_ietf_bytes(&identity.to_ietf_bytes().unwrap()),
            Err(Error::InvalidKey)
        );
        let mut outside = [0u8; G2_LEN];
        outside_g2().serialize_compressed(&mut outside[..]).unwrap();
        assert!(matches!(
            BBSVerificationKey::<Bls12_381>::from_ietf_bytes(&outside),
            Err(Error::Serialization(_))
        ));

        // a credential: (A, e) cross as the 80 bytes of an IETF signature, ρ separately
        let cred = BBSCredential::<Bls12_381> {
            a: G1Projective::generator() * Fr::from(7u64),
            e: Fr::from(9u64),
            rho: Fr::from(11u64),
        };
        let bytes = cred.to_ietf_bytes().unwrap();
        assert_eq!(&bytes[G1_LEN..], &scalar_to_be_bytes(&cred.e)[..]);
        assert_eq!(
            BBSCredential::from_ietf_bytes(&bytes, &cred.rho).unwrap(),
            cred
        );
        assert!(BBSCredential::<Bls12_381>::from_ietf_bytes(&bytes[..79], &cred.rho).is_err());
        assert!(
            BBSCredential::<Bls12_381>::from_ietf_bytes(&[&bytes[..], &[0]].concat(), &cred.rho)
                .is_err()
        );
    }
}
