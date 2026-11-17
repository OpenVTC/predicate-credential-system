//! The Fiat-Shamir transform of the generalized Schnorr protocol (§2.3, last paragraph, and §5.1,
//! `zkPoK_ctx{(X, W) ∈ R}`), as the IETF CFRG drafts `draft-irtf-cfrg-sigma-protocols-04`
//! ("Sigma -04") and `draft-irtf-cfrg-fiat-shamir-04` ("FS -04") specify it.
//!
//! The paper replaces the verifier's challenge by `c = H_1(ctx, A)`, "where `ctx` contains the
//! public statement and the protocol context", and notes that "the verifier reconstructs the
//! commitments and hashes the complete public statement". This module instantiates `H_1` with
//! the compact non-interactive argument of Sigma -04 §5.5:
//!
//! 1. **Tag and session identifier** (Sigma -04 §5.1, FS -04 §5.1). The tag of a proof under
//!    the context `ctx` is the US-ASCII string
//!
//!    ```text
//!    tag = "PCS-V01-SIGMA04-CMPT-with-" ‖ suite ‖ "-ctx-" ‖ hex(ctx)
//!    ```
//!
//!    It names this crate (`PCS`), the version of this tag format (`V01`), the revision of the
//!    drafts it follows (`SIGMA04`: Sigma -04 with FS -04), the flavor marker of compact NARG
//!    strings (`CMPT`) and the ciphersuite identifier `suite` of the relation
//!    ([`crate::sigma::ciphersuite`]: `sigma-proofs_Shake128_BLS12381` for relations over `G_1`
//!    of BLS12-381, an identifier of this crate's extension otherwise), and it ends with the
//!    application context: the caller's `ctx` bytes in lower-case hexadecimal, two digits per
//!    byte. The session identifier is `DeriveSessionID(tag)` ([`derive_session_id`]).
//! 2. **Challenge** (Sigma -04 §5.2, [`derive_challenge`]): the duplex sponge initialized with the
//!    session identifier absorbs `SerializeLinearRelation(instance)` and the serialized
//!    commitment, and the challenge is `DecodeField(Squeeze(N_s + 16), p, 1)`.
//! 3. **Proof** (Sigma -04 §5.5): the NARG string `Scalar.serialize([c]) ‖ Scalar.serialize(z)`
//!    ([`FSProof::to_narg`]), `(1 + n) · N_s` bytes for `n` responses, with big-endian scalars.
//!    The verifier validates the instance, requires that exact length and canonical scalars,
//!    recomputes `A' = φ(z) − c·Y` and accepts iff the challenge of `A'` is `c`
//!    ([`verify_compact`], [`verify`]).
//!
//! # Why `ctx` is in the tag, and in which form
//!
//! FS -04 §5.1 requires the tag to identify the application context, so that a proof made for
//! one application is not accepted in another, and the paper's `ctx` is exactly that context
//! (`ctx_j`, `ctx_0` of the construction box, which begin with `pp`). `ctx` is the last field of
//! the tag, so a tag determines its fields: remove the fixed prefix, split at the LAST
//! occurrence of `-ctx-` (the hexadecimal digits after it contain no `-`), and decode the digits.
//! Distinct `(suite, ctx)` therefore give distinct tags, as §5.1 requires of a tag composed of
//! several fields. Writing `ctx` in hexadecimal keeps the tag US-ASCII, as §5.1 recommends.
//!
//! `ctx` must be rebuilt by the verifier from public data and never be taken from the prover
//! (Sigma -04 §5.1: "Neither should accept a session identifier supplied by an untrusted third
//! party"). It is also the ONLY deployment-specific input: this module does not know the public
//! parameters. A caller that wants its proofs bound to a deployment puts (a digest of) `pp` into
//! `ctx`, as `ctx_j` and `ctx_0` of the construction box do. Statements whose bases are
//! deployment independent (`id = g_1^usk`) replay across deployments otherwise.
//!
//! # Binding to the whole statement
//!
//! The instance that the challenge absorbs is the whole statement: every element, every
//! coefficient and the shape ([`LinearRelation::serialize_instance`]). This is the *strong*
//! Fiat-Shamir transform in the terminology of Bernhard, Pereira and Warinschi ("How not to
//! prove yourself", ASIACRYPT 2012). Hashing the statement inside this module, rather than
//! trusting each caller to put it into `ctx`, defeats the *weak* Fiat-Shamir attack in which a
//! target (a tag) or a base (a shown credential) is chosen after the challenge. The test suite
//! mounts that attack.
//!
//! Security of the transform is in the random-oracle model for the duplex sponge. Knowledge
//! extraction from a Fiat-Shamir proof is by rewinding (Sigma -04 §7.2). The paper's
//! straight-line alternatives are out of scope of this crate.
//!
//! # In formulas
//!
//! For the relation $`Y_i = \sum_j b_{ij}\, x_{v_{ij}} B_{ij}`$ of [`crate::sigma`] with
//! commitment $`A = (A_i)_i`$:
//!
//! ```math
//! c = \mathsf{DecodeField}\bigl(\mathsf{DS}(\mathsf{DeriveSessionID}(\mathsf{tag}(\mathsf{ctx})),\ \mathsf{instance},\ A)\bigr), \qquad z_j = r_j + c\, x_j, \qquad \pi = (c, z)
//! ```
//!
//! [`derive_session_id`]: crate::hash::duplex_sponge::derive_session_id

use ark_ff::PrimeField;
use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, Read, SerializationError, Valid, Validate,
    Write,
};
use ark_std::rand::{CryptoRng, RngCore};

use super::{
    codec::{scalar_from_bytes, scalar_len, write_scalar},
    protocol::{commit, respond},
    relation::LinearRelation,
};
use crate::{
    error::Error,
    hash::duplex_sponge::{DuplexSponge, derive_session_id, squeeze_scalar},
};

/// The first field of the tag: this crate.
pub const APPLICATION: &str = "PCS";
/// The version of the tag format.
pub const TAG_VERSION: &str = "V01";
/// The revision of the drafts the transform follows: `draft-irtf-cfrg-sigma-protocols-04` with
/// `draft-irtf-cfrg-fiat-shamir-04`.
pub const REVISION: &str = "SIGMA04";
/// The flavor marker of compact NARG strings (Sigma -04 §5.1).
pub const FLAVOR: &str = "CMPT";

/// The tag of a proof for the relation `rel` under the context `ctx` (module docs):
/// `PCS-V01-SIGMA04-CMPT-with-{suite}-ctx-{hex(ctx)}`.
///
/// ```
/// use ark_bls12_381::G1Projective;
/// use predicate_credential_system::sigma::{GroupRelation, fiat_shamir};
///
/// let rel = GroupRelation::<G1Projective>::new();
/// assert_eq!(
///     fiat_shamir::tag(&rel, b"\x01\xab"),
///     b"PCS-V01-SIGMA04-CMPT-with-sigma-proofs_Shake128_BLS12381-ctx-01ab"
/// );
/// ```
#[must_use]
pub fn tag<R: LinearRelation>(rel: &R, ctx: &[u8]) -> Vec<u8> {
    compose_tag(&rel.suite_id(), ctx)
}

/// The tag for the ciphersuite identifier `suite` and the context `ctx`:
/// `PCS-V01-SIGMA04-CMPT-with-{suite}-ctx-{hex(ctx)}`.
#[must_use]
pub fn compose_tag(suite: &str, ctx: &[u8]) -> Vec<u8> {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut out =
        format!("{APPLICATION}-{TAG_VERSION}-{REVISION}-{FLAVOR}-with-{suite}-ctx-").into_bytes();
    out.reserve(2 * ctx.len());
    for byte in ctx {
        out.push(DIGITS[usize::from(byte >> 4)]);
        out.push(DIGITS[usize::from(byte & 0x0f)]);
    }
    out
}

/// `DeriveChallenge(tag, instance, commitment_bytes)` of Sigma -04 §5.2: the sponge initialized
/// with `DeriveSessionID(tag)` absorbs `SerializeLinearRelation(instance)` and
/// `commitment_bytes`, and the challenge is `DecodeField(Squeeze(N_s + 16), p, 1)`.
///
/// # Errors
/// The errors of [`LinearRelation::serialize_instance`].
pub fn derive_challenge<R: LinearRelation>(
    tag: &[u8],
    rel: &R,
    commitment_bytes: &[u8],
) -> Result<R::Scalar, Error> {
    let instance = rel.serialize_instance()?;
    let mut sponge = DuplexSponge::new(&derive_session_id(tag));
    sponge.absorb(&instance);
    sponge.absorb(commitment_bytes);
    Ok(squeeze_scalar(&mut sponge))
}

/// The Fiat-Shamir challenge of the commitment `A` under the context `ctx`:
/// [`derive_challenge`] with the [`tag`] of `ctx` and the serialized commitment.
///
/// A public function of public data. It is exposed so that the test harness can play a cheating
/// prover who picks its commitment first (the weak Fiat-Shamir attack must fail against it).
///
/// # Errors
/// [`Error::LengthMismatch`] if `commitment` does not have one element per equation, and the
/// errors of [`LinearRelation::serialize_instance`].
pub fn challenge<R: LinearRelation>(
    rel: &R,
    ctx: &[u8],
    commitment: &R::Image,
) -> Result<R::Scalar, Error> {
    derive_challenge(&tag(rel, ctx), rel, &rel.serialize_image(commitment)?)
}

/// A compact non-interactive proof `(c, z)`: the challenge and one response per witness
/// coordinate. No group element is transmitted.
///
/// Its encoding on the wire is the compact NARG string of Sigma -04 §5.5,
/// `Scalar.serialize([c]) ‖ Scalar.serialize(z)` with big-endian scalars ([`Self::to_narg`],
/// [`Self::serialize_compact`]): its length is fixed by the statement, which is why the decoders
/// take the number of responses as an argument and never read it from the wire. The canonical
/// encoding of this crate (`CanonicalSerialize`, [`crate::serialization`]) is self-describing:
/// `LE64(n) ‖ NARG string`, the number `n` of responses as a little-endian `u64` and then the
/// NARG string itself.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FSProof<F: PrimeField> {
    /// The challenge `c`.
    pub challenge: F,
    /// The responses `z_j = r_j + c·x_j`, in variable order.
    pub responses: Vec<F>,
}

impl<F: PrimeField> FSProof<F> {
    /// Size in bytes of the NARG string: `(1 + #responses)` scalars of `N_s` bytes.
    #[must_use]
    pub fn compact_size(&self) -> usize {
        scalar_len::<F>() * (1 + self.responses.len())
    }

    /// The NARG string `Scalar.serialize([c]) ‖ Scalar.serialize(z)` (Sigma -04 §5.5).
    #[must_use]
    pub fn to_narg(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(self.compact_size());
        write_scalar(&mut out, &self.challenge);
        for response in &self.responses {
            write_scalar(&mut out, response);
        }
        out
    }

    /// Reads a NARG string of exactly `num_responses` responses (`num_responses` from the
    /// statement, `rel.num_scalars()`, never from the wire), with canonical scalars and nothing
    /// left over (Sigma -04 §5.5, steps 2 to 5 of `VerifyCompact`).
    ///
    /// # Errors
    /// [`Error::LengthMismatch`] unless `narg` has exactly `(1 + num_responses) · N_s` bytes,
    /// [`Error::Serialization`] for a non-canonical scalar.
    pub fn from_narg(narg: &[u8], num_responses: usize) -> Result<Self, Error> {
        let ns = scalar_len::<F>();
        let expected = num_responses
            .checked_add(1)
            .and_then(|n| n.checked_mul(ns))
            .ok_or(Error::LengthMismatch {
                expected: usize::MAX,
                actual: narg.len(),
            })?;
        if narg.len() != expected {
            return Err(Error::LengthMismatch {
                expected,
                actual: narg.len(),
            });
        }
        let mut reader = narg;
        Self::deserialize_compact(&mut reader, num_responses)
    }

    /// Writes the NARG string.
    ///
    /// # Errors
    /// [`Error::Serialization`] if the writer fails.
    pub fn serialize_compact<W: Write>(&self, mut writer: W) -> Result<(), Error> {
        writer
            .write_all(&self.to_narg())
            .map_err(|e| Error::Serialization(e.to_string()))
    }

    /// Reads a NARG string of `num_responses` responses (fixed by the statement,
    /// `rel.num_scalars()`, never a number taken from the wire) from the front of `reader`.
    /// Scalars must be canonical. Bytes after the proof stay in the reader (the decoders of the
    /// messages refuse them).
    ///
    /// # Errors
    /// [`Error::Serialization`] on truncated input or a non-canonical scalar.
    pub fn deserialize_compact<R: Read>(
        mut reader: R,
        num_responses: usize,
    ) -> Result<Self, Error> {
        let challenge =
            read_scalar(&mut reader).map_err(|e| Error::Serialization(e.to_string()))?;
        // Not `with_capacity(num_responses)`: every response consumes input.
        let mut responses = Vec::new();
        for _ in 0..num_responses {
            responses
                .push(read_scalar(&mut reader).map_err(|e| Error::Serialization(e.to_string()))?);
        }
        Ok(Self {
            challenge,
            responses,
        })
    }
}

/// Reads one scalar of `N_s` bytes, strictly (Sigma -04 §8.2.2).
fn read_scalar<F: PrimeField, R: Read>(mut reader: R) -> Result<F, SerializationError> {
    let mut buf = vec![0u8; scalar_len::<F>()];
    reader.read_exact(&mut buf)?;
    scalar_from_bytes(&buf).ok_or(SerializationError::InvalidData)
}

/// `LE64(n) ‖ NARG string`.
impl<F: PrimeField> CanonicalSerialize for FSProof<F> {
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        (self.responses.len() as u64).serialize_with_mode(&mut writer, compress)?;
        writer.write_all(&self.to_narg())?;
        Ok(())
    }

    fn serialized_size(&self, _compress: Compress) -> usize {
        8 + self.compact_size()
    }
}

impl<F: PrimeField> Valid for FSProof<F> {
    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }
}

/// `LE64(n) ‖ NARG string`, with canonical scalars. The count `n` comes from the wire: nothing is
/// allocated ahead of the input that backs it.
impl<F: PrimeField> CanonicalDeserialize for FSProof<F> {
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let n = u64::deserialize_with_mode(&mut reader, compress, validate)?;
        let challenge = read_scalar(&mut reader)?;
        let mut responses = Vec::new();
        for _ in 0..n {
            responses.push(read_scalar(&mut reader)?);
        }
        Ok(Self {
            challenge,
            responses,
        })
    }
}

/// `ProveCompact` without the final serialization: commits, derives the challenge under `tag`
/// and responds.
fn prove_with_tag<R, Rng>(
    tag: &[u8],
    rel: &R,
    witness: &[R::Scalar],
    rng: &mut Rng,
) -> Result<FSProof<R::Scalar>, Error>
where
    R: LinearRelation,
    Rng: RngCore + CryptoRng + ?Sized,
{
    rel.validate()?;
    if !rel.is_satisfied_by(witness) {
        return Err(Error::WitnessDoesNotSatisfyRelation);
    }
    let (commitment, state) = commit(rel, rng)?;
    let challenge = derive_challenge(tag, rel, &rel.serialize_image(&commitment)?)?;
    let responses = respond(state, witness, &challenge)?;
    Ok(FSProof {
        challenge,
        responses,
    })
}

/// `π ← zkPoK_ctx{(rel, witness) ∈ R}`: commits, derives the challenge under the [`tag`] of
/// `ctx` and responds.
///
/// # Errors
/// [`Error::InvalidInstance`] if `rel` is not a valid instance (Sigma -04 §3.5), and
/// [`Error::WitnessDoesNotSatisfyRelation`] if `witness` does not satisfy `rel` (including a
/// wrong length): the honest prover is only defined on `(x, w) ∈ R`, and a proof for a false
/// statement would not verify anyway.
pub fn prove<R, Rng>(
    rel: &R,
    witness: &[R::Scalar],
    ctx: &[u8],
    rng: &mut Rng,
) -> Result<FSProof<R::Scalar>, Error>
where
    R: LinearRelation,
    Rng: RngCore + CryptoRng + ?Sized,
{
    prove_with_tag(&tag(rel, ctx), rel, witness, rng)
}

/// `ProveCompact(tag, instance, witness, rng)` of Sigma -04 §5.5 for an explicit `tag`: the NARG
/// string. The masks are drawn from `rng` with `Group.random_scalar` (§2.2: `N_s + 16` bytes
/// reduced by `DecodeField`).
///
/// [`prove`] is this function with the [`tag`] of a context. This form exists to run the draft's
/// test vectors and to talk to other implementations of the draft, which choose their own tags.
///
/// # Errors
/// As [`prove`].
pub fn prove_compact<R, Rng>(
    tag: &[u8],
    rel: &R,
    witness: &[R::Scalar],
    rng: &mut Rng,
) -> Result<Vec<u8>, Error>
where
    R: LinearRelation,
    Rng: RngCore + CryptoRng + ?Sized,
{
    prove_with_tag(tag, rel, witness, rng).map(|proof| proof.to_narg())
}

/// Verification of a parsed proof under `tag`: steps 1 and 6 to 8 of `VerifyCompact`.
fn verify_with_tag<R: LinearRelation>(tag: &[u8], rel: &R, proof: &FSProof<R::Scalar>) -> bool {
    if rel.validate().is_err() || proof.responses.len() != rel.num_scalars() {
        return false;
    }
    let Ok(commitment) = rel.recompute_commitment(&proof.challenge, &proof.responses) else {
        return false;
    };
    let Ok(commitment_bytes) = rel.serialize_image(&commitment) else {
        return false;
    };
    derive_challenge(tag, rel, &commitment_bytes).is_ok_and(|c| c == proof.challenge)
}

/// `Verify_FS(ctx, π)` for the statement `rel`: validates the instance, recomputes
/// `A' = φ(z) − c·Y` and accepts iff the challenge of `A'` under the [`tag`] of `ctx` is `c`.
///
/// Returns `false`, without panicking, on any malformed proof, in particular when the number of
/// responses differs from the number of witness coordinates. The scalars of an [`FSProof`] are
/// canonical by construction, and bytes are checked by its decoders ([`FSProof::from_narg`],
/// [`verify_compact`]). The witness-independent validity checks of the statement (`ValidTag`,
/// the public part of `VerifyPossess`, the subgroup checks of received elements) are the
/// caller's job, as is rebuilding `ctx` from public data.
#[must_use]
pub fn verify<R: LinearRelation>(rel: &R, ctx: &[u8], proof: &FSProof<R::Scalar>) -> bool {
    verify_with_tag(&tag(rel, ctx), rel, proof)
}

/// `VerifyCompact(tag, instance, narg_string)` of Sigma -04 §5.5 for an explicit `tag`: the
/// instance is valid, the NARG string has exactly `(1 + num_scalars) · N_s` bytes of canonical
/// scalars, and the challenge of the recomputed commitment is the one in the string.
///
/// The verifier of the protocol is [`verify`] (the [`tag`] of a context). This form exists to run
/// the draft's test vectors and to check proofs of other implementations of the draft.
#[must_use]
pub fn verify_compact<R: LinearRelation>(tag: &[u8], rel: &R, narg: &[u8]) -> bool {
    if rel.validate().is_err() {
        return false;
    }
    FSProof::from_narg(narg, rel.num_scalars()).is_ok_and(|proof| verify_with_tag(tag, rel, &proof))
}

#[cfg(test)]
mod tests {
    use ark_bls12_381::{Bls12_381, Fr, G1Projective, G2Projective};
    use ark_ec::PrimeGroup;
    use ark_ff::{BigInteger, Field, One, UniformRand};
    use rand::{SeedableRng, rngs::StdRng};

    use super::*;
    use crate::{
        serialization::WireFormat,
        sigma::relation::{GroupRelation, GtEquation, LinearEquation, PairingRelation},
    };

    fn statement(rng: &mut StdRng) -> (GroupRelation<G1Projective>, Vec<Fr>) {
        let g = G1Projective::generator();
        let h = g * Fr::rand(rng);
        let (x, y) = (Fr::rand(rng), Fr::rand(rng));
        let mut rel = GroupRelation::new();
        let (vx, vy) = (rel.alloc_scalar(), rel.alloc_scalar());
        rel.add_equation(LinearEquation::new(vec![(vx, g), (vy, h)], g * x + h * y))
            .unwrap();
        (rel, vec![x, y])
    }

    #[test]
    fn prove_verify_and_both_encodings() {
        let mut rng = StdRng::seed_from_u64(11);
        let (rel, w) = statement(&mut rng);
        let proof = prove(&rel, &w, b"ctx", &mut rng).unwrap();
        assert!(verify(&rel, b"ctx", &proof));
        assert!(!verify(&rel, b"ctx2", &proof));

        // the NARG string: c ‖ z, big-endian scalars, length fixed by the statement
        let narg = proof.to_narg();
        assert_eq!(narg.len(), 3 * 32);
        assert_eq!(narg.len(), proof.compact_size());
        let mut le = Vec::new();
        proof.challenge.serialize_compressed(&mut le).unwrap();
        le.reverse();
        assert_eq!(narg[..32], le[..], "the challenge is written big-endian");
        assert_eq!(FSProof::<Fr>::from_narg(&narg, 2).unwrap(), proof);
        assert!(verify_compact(&tag(&rel, b"ctx"), &rel, &narg));
        assert!(FSProof::<Fr>::from_narg(&narg, 1).is_err());
        assert!(FSProof::<Fr>::from_narg(&narg[..95], 2).is_err());
        assert!(FSProof::<Fr>::from_narg(&[narg.clone(), vec![0]].concat(), 2).is_err());
        let mut compact = Vec::new();
        proof.serialize_compact(&mut compact).unwrap();
        assert_eq!(compact, narg);
        let mut reader = &compact[..];
        let back = FSProof::<Fr>::deserialize_compact(&mut reader, 2).unwrap();
        assert!(reader.is_empty());
        assert_eq!(back, proof);
        // a non-canonical scalar (all ones) is rejected
        let mut bad = narg.clone();
        bad[..32].fill(0xff);
        assert!(FSProof::<Fr>::deserialize_compact(&bad[..], 2).is_err());
        assert!(!verify_compact(&tag(&rel, b"ctx"), &rel, &bad));

        // self-describing canonical encoding: LE64(n) ‖ NARG string
        let bytes = proof.to_bytes().unwrap();
        assert_eq!(bytes, [2u64.to_le_bytes().to_vec(), narg].concat());
        assert_eq!(FSProof::<Fr>::from_bytes(&bytes).unwrap(), proof);
    }

    #[test]
    fn the_tag_is_composed_as_documented() {
        assert_eq!(
            compose_tag("sigma-proofs_Shake128_BLS12381", b""),
            b"PCS-V01-SIGMA04-CMPT-with-sigma-proofs_Shake128_BLS12381-ctx-"
        );
        assert_eq!(
            compose_tag("x", &[0x00, 0x0f, 0xf0, 0xff]),
            b"PCS-V01-SIGMA04-CMPT-with-x-ctx-000ff0ff"
        );
        let mut rng = StdRng::seed_from_u64(12);
        let (rel, _) = statement(&mut rng);
        assert_eq!(
            tag(&rel, b"ab"),
            b"PCS-V01-SIGMA04-CMPT-with-sigma-proofs_Shake128_BLS12381-ctx-6162"
        );
    }

    // ----- the pairing extension ---------------------------------------------------------------

    /// A relation of the pairing extension over BLS12-381: a `G_1`, a `G_2` and a `G_T` equation
    /// sharing the variables `(x, y)`, with coefficients other than 1.
    fn extension_statement(rng: &mut StdRng) -> (PairingRelation<Bls12_381>, Vec<Fr>) {
        let (g1, g2) = (G1Projective::generator(), G2Projective::generator());
        let (x, y) = (Fr::rand(rng), Fr::rand(rng));
        let (p, h) = (g1 * Fr::rand(rng), g1 * Fr::rand(rng));
        let q = g2 * Fr::rand(rng);
        let (one, three) = (Fr::one(), Fr::from(3u64));
        let mut rel = PairingRelation::new();
        let (vx, vy) = (rel.alloc_scalar(), rel.alloc_scalar());
        rel.add_g1(LinearEquation::new(vec![(vx, p), (vy, h)], p * x + h * y))
            .unwrap();
        rel.add_g2(LinearEquation::dlog(vy, q, q * y)).unwrap();
        // e(P, Q)^{3x} · e(H, g̃)^y = e(P, Q)^{3x} e(H, g̃)^y, the image by its pairing preimages
        rel.add_gt(GtEquation {
            image: vec![(p * (three * x), q, one), (h, g2 * y, one)],
            terms: vec![(vx, p, q, three), (vy, h, g2, one)],
        })
        .unwrap();
        (rel, vec![x, y])
    }

    /// `s + p`, big-endian, for a canonical 32-byte `s` (the sum stays below `2^256`).
    fn plus_modulus(s: &[u8]) -> Vec<u8> {
        let p = Fr::MODULUS.to_bytes_be();
        let mut out = vec![0u8; 32];
        let mut carry = 0u16;
        for i in (0..32).rev() {
            let t = u16::from(s[i]) + u16::from(p[i]) + carry;
            out[i] = t as u8;
            carry = t >> 8;
        }
        assert_eq!(carry, 0, "2p < 2^256 for BLS12-381");
        out
    }

    #[test]
    fn the_extension_proves_verifies_and_rejects() {
        let mut rng = StdRng::seed_from_u64(13);
        let (rel, w) = extension_statement(&mut rng);
        assert!(!rel.is_g1_only());
        assert_eq!(rel.validate(), Ok(()));
        let suite = rel.suite_id();
        assert_eq!(suite, "pcs-sigma-pairing_Shake128_BLS12381");
        let t = tag(&rel, b"ctx");
        assert_eq!(
            t,
            format!("PCS-V01-SIGMA04-CMPT-with-{suite}-ctx-637478").into_bytes()
        );

        let proof = prove(&rel, &w, b"ctx", &mut rng).unwrap();
        assert!(verify(&rel, b"ctx", &proof));
        let narg = proof.to_narg();
        assert_eq!(narg.len(), 3 * 32);
        assert!(verify_compact(&t, &rel, &narg));

        // a wrong context
        for ctx in [&b"ctx2"[..], b"", b"ctx\0", b"CTX"] {
            assert!(!verify(&rel, ctx, &proof));
        }
        // a wrong flavor, the draft's ciphersuite (which this relation is not), another version,
        // another revision, another application
        for wrong in [
            format!("PCS-V01-SIGMA04-DSFS-with-{suite}-ctx-637478"),
            "PCS-V01-SIGMA04-CMPT-with-sigma-proofs_Shake128_BLS12381-ctx-637478".to_owned(),
            format!("PCS-V02-SIGMA04-CMPT-with-{suite}-ctx-637478"),
            format!("PCS-V01-SIGMA03-CMPT-with-{suite}-ctx-637478"),
            format!("XYZ-V01-SIGMA04-CMPT-with-{suite}-ctx-637478"),
            format!("PCS-V01-SIGMA04-CMPT-with-{suite}-ctx-"),
        ] {
            assert!(!verify_compact(wrong.as_bytes(), &rel, &narg), "{wrong}");
        }
        // trailing bytes, truncation, one response more or fewer, nothing
        assert!(!verify_compact(&t, &rel, &[narg.clone(), vec![0]].concat()));
        assert!(!verify_compact(&t, &rel, &narg[..narg.len() - 1]));
        assert!(!verify_compact(&t, &rel, &narg[..64]));
        assert!(!verify_compact(
            &t,
            &rel,
            &[narg.clone(), narg[64..].to_vec()].concat()
        ));
        assert!(!verify_compact(&t, &rel, &[]));
        assert!(matches!(
            FSProof::<Fr>::from_narg(&narg[..64], 2),
            Err(Error::LengthMismatch {
                expected: 96,
                actual: 64
            })
        ));
        let mut longer = proof.clone();
        longer.responses.push(Fr::one());
        assert!(!verify(&rel, b"ctx", &longer));
        // non-canonical scalars: each one re-encoded as s + p, the same value modulo p
        for at in [0, 32, 64] {
            let mut bad = narg.clone();
            bad[at..at + 32].copy_from_slice(&plus_modulus(&narg[at..at + 32]));
            assert!(!verify_compact(&t, &rel, &bad), "s + p at {at}");
            assert!(FSProof::<Fr>::from_narg(&bad, 2).is_err());
            let mut bad = narg.clone();
            bad[at..at + 32].fill(0xff);
            assert!(!verify_compact(&t, &rel, &bad), "2^256 − 1 at {at}");
        }
        // a changed response or challenge
        for at in [0, 32, 64] {
            let mut bad = narg.clone();
            bad[at + 31] ^= 1;
            assert!(!verify_compact(&t, &rel, &bad), "flipped bit at {at}");
        }
    }

    /// The instance of the extension binds every element of `G_1` and `G_2`, every coefficient
    /// and the variable of every term: a proof does not survive the change of one of them.
    #[test]
    fn the_extension_binds_every_part_of_the_statement() {
        let mut rng = StdRng::seed_from_u64(14);
        let (rel, w) = extension_statement(&mut rng);
        let proof = prove(&rel, &w, b"ctx", &mut rng).unwrap();
        let (d1, d2) = (G1Projective::generator(), G2Projective::generator());
        let rebuild = |g1: Vec<LinearEquation<G1Projective>>,
                       g2: Vec<LinearEquation<G2Projective>>,
                       gt: Vec<GtEquation<Bls12_381>>| {
            let mut out = PairingRelation::<Bls12_381>::new();
            out.alloc_scalars(2);
            g1.into_iter().for_each(|eq| out.add_g1(eq).unwrap());
            g2.into_iter().for_each(|eq| out.add_g2(eq).unwrap());
            gt.into_iter().for_each(|eq| out.add_gt(eq).unwrap());
            out
        };
        let (g1, g2, gt) = (
            rel.g1_linear_equations(),
            rel.g2_linear_equations(),
            rel.gt_linear_equations(),
        );
        assert_eq!(rebuild(g1.clone(), g2.clone(), gt.clone()), rel);
        let mut mutated = Vec::new();
        for k in 0..gt[0].terms.len() {
            let mut m = gt.clone();
            m[0].terms[k].1 += d1;
            mutated.push(("gt term P", rebuild(g1.clone(), g2.clone(), m)));
            let mut m = gt.clone();
            m[0].terms[k].2 += d2;
            mutated.push(("gt term Q", rebuild(g1.clone(), g2.clone(), m)));
            let mut m = gt.clone();
            m[0].terms[k].3 += Fr::one();
            mutated.push(("gt term coefficient", rebuild(g1.clone(), g2.clone(), m)));
        }
        for k in 0..gt[0].image.len() {
            let mut m = gt.clone();
            m[0].image[k].0 += d1;
            mutated.push(("gt image P", rebuild(g1.clone(), g2.clone(), m)));
            let mut m = gt.clone();
            m[0].image[k].1 += d2;
            mutated.push(("gt image Q", rebuild(g1.clone(), g2.clone(), m)));
        }
        // the same G_T value from other preimages: e(2P, Q/2) = e(P, Q)
        let half = Fr::from(2u64).inverse().unwrap();
        let mut m = gt.clone();
        let (p, q, c) = m[0].image[0];
        m[0].image[0] = (p + p, q * half, c);
        let rebalanced = rebuild(g1.clone(), g2.clone(), m);
        assert!(rebalanced.is_satisfied_by(&w), "the same statement in G_T");
        mutated.push(("gt image re-balanced", rebalanced));
        let mut m = g2.clone();
        m[0].terms[0].1 += d2;
        mutated.push(("g2 base", rebuild(g1.clone(), m, gt.clone())));
        let mut m = g2.clone();
        m[0].image[0].0 += d2;
        mutated.push(("g2 image", rebuild(g1.clone(), m, gt.clone())));
        let mut m = g1.clone();
        m[0].terms.swap(0, 1);
        mutated.push(("g1 terms swapped", rebuild(m, g2.clone(), gt.clone())));
        let mut m = gt.clone();
        m[0].terms[1].0 = m[0].terms[0].0;
        mutated.push(("gt variable", rebuild(g1.clone(), g2.clone(), m)));
        assert_eq!(mutated.len(), 2 * 3 + 2 * 2 + 1 + 2 + 1 + 1);
        for (label, other) in &mutated {
            assert_ne!(
                other.serialize_instance().unwrap(),
                rel.serialize_instance().unwrap(),
                "{label}"
            );
            assert!(!verify(other, b"ctx", &proof), "{label}");
        }
    }

    /// Distinct tag fields give distinct tags: a tag parses back into its fields (module docs,
    /// "Why `ctx` is in the tag").
    #[test]
    fn distinct_tag_fields_give_distinct_tags() {
        /// The inverse of `compose_tag` on the fixed prefix: the suite is everything up to the
        /// LAST `-ctx-`, the context the hexadecimal digits after it.
        fn parse(tag: &[u8]) -> Option<(String, Vec<u8>)> {
            let text = core::str::from_utf8(tag).ok()?;
            let rest = text.strip_prefix("PCS-V01-SIGMA04-CMPT-with-")?;
            let at = rest.rfind("-ctx-")?;
            let (suite, digits) = (&rest[..at], &rest[at + 5..]);
            if !digits.len().is_multiple_of(2)
                || !digits
                    .bytes()
                    .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
            {
                return None;
            }
            let ctx = (0..digits.len())
                .step_by(2)
                .map(|i| u8::from_str_radix(&digits[i..i + 2], 16).unwrap())
                .collect();
            Some((suite.to_owned(), ctx))
        }

        let suites = [
            "sigma-proofs_Shake128_BLS12381",
            "pcs-sigma-pairing_Shake128_BLS12381",
            "pcs-sigma-group_Shake128_BLS12381G2",
            "pcs-sigma-group_Shake128_BLS12381GT",
            // adversarial identifiers that contain the separator or digits
            "a-ctx-00",
            "a-ctx-",
            "a",
            "",
            "-ctx-",
        ];
        let contexts: [&[u8]; 8] = [
            b"",
            b"\x00",
            b"\x00\x00",
            b"-ctx-",
            b"ab",
            b"\xab",
            b"\x0a\x2d",
            &[0xff; 32],
        ];
        let mut seen = std::collections::BTreeMap::new();
        for suite in suites {
            for ctx in contexts {
                let tag = compose_tag(suite, ctx);
                assert!(tag.is_ascii(), "the tag is US-ASCII");
                assert_eq!(
                    parse(&tag),
                    Some((suite.to_owned(), ctx.to_vec())),
                    "{suite}"
                );
                if let Some(previous) = seen.insert(tag.clone(), (suite, ctx)) {
                    panic!("{previous:?} and {:?} share the tag", (suite, ctx));
                }
            }
        }
        assert_eq!(seen.len(), suites.len() * contexts.len());
        // ... and so do their session identifiers
        let sids: std::collections::BTreeSet<[u8; 32]> =
            seen.keys().map(|tag| derive_session_id(tag)).collect();
        assert_eq!(sids.len(), seen.len());
    }
}
