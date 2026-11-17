//! The crate-wide error type.
//!
//! The paper writes `⊥` for every failing algorithm. In this crate `⊥` is `Err(Error::..)` for
//! algorithms that produce a value (and `None` for [`KIPRF::eval`](crate::kiprf::KIPRF::eval)),
//! while verifiers return `bool` and never panic on adversarial input. The variants below name
//! the individual `⊥` cases so that callers and tests can tell them apart.

use ark_ec::hashing::HashToCurveError;
use ark_serialize::SerializationError;

/// Every way an algorithm of this crate can output `⊥`.
///
/// The type is `Clone + PartialEq + Eq` so that tests can assert on the exact failure; foreign
/// errors (serialization, hash-to-curve) are therefore carried as their display string.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum Error {
    // ----- sigma layer ---------------------------------------------------------------------
    /// The prover was asked to prove a statement its witness does not satisfy
    /// (`(x, w) ∉ R`; Def. "Sigma protocol" only defines the honest prover on `(x, w) ∈ R`).
    #[error("the witness does not satisfy the relation")]
    WitnessDoesNotSatisfyRelation,
    /// An equation refers to a witness coordinate that was never allocated in this relation.
    #[error("equation references scalar variable #{index}, but only {allocated} are allocated")]
    UnallocatedVariable {
        /// Index of the offending variable.
        index: usize,
        /// Number of variables allocated in the relation.
        allocated: usize,
    },
    /// A vector (witness, responses, message, generators, ...) has the wrong length.
    #[error("length mismatch: expected {expected}, got {actual}")]
    LengthMismatch {
        /// The length required by the statement.
        expected: usize,
        /// The length that was supplied.
        actual: usize,
    },
    /// A statement is not a valid instance (`ValidateInstance` of
    /// `draft-irtf-cfrg-sigma-protocols-04`, §3.5, or its analogue for the pairing extension of
    /// [`crate::sigma::relation`]), or its serialization is malformed. The payload names the
    /// failed check: a count or an index of `2^32` or more, an element index beyond the listed
    /// elements, a listed element that no equation uses, or truncated input.
    #[error("invalid instance: {0}")]
    InvalidInstance(&'static str),

    // ----- KI-PRF --------------------------------------------------------------------------
    /// `TagEval(K, s) = ⊥`: the tag is undefined at this point (Def. "Non-adaptive
    /// key-injective pseudorandom function", partial-domain case; e.g. `K + s = 0` for
    /// `Tag_DY`).
    #[error("the tag function is undefined at this point")]
    UndefinedTag,
    /// `ValidTag(T, s) = 0` (Def. "Sigma-friendly non-adaptive key-injective PRF"), e.g.
    /// `T = 1`.
    #[error("inadmissible tag encoding")]
    InvalidTag,

    // ----- credential base -----------------------------------------------------------------
    /// A key is outside its key space, e.g. a helper key outside the admissible key domain
    /// `V_pp` of the base (for `Σ-PS`: `Y ≠ 1`, `Ỹ ≠ 1` and `e(Y, g̃) = e(g_1, Ỹ)`;
    /// [`crate::pcreds::Protocol::helper_key`]); also a helper, a helper key or an evaluated
    /// request that belongs to another deployment or another helper.
    #[error("invalid key")]
    InvalidKey,
    /// A value is outside its message space, e.g. a ternary polynomial of the lattice
    /// instantiation with a coefficient outside `{-1, 0, 1}`.
    #[error("message outside the message space")]
    InvalidMessage,
    /// A credential does not verify, or is malformed.
    #[error("invalid credential")]
    InvalidCredential,
    /// A blinded pre-credential is malformed or does not unblind to a valid credential.
    #[error("invalid pre-credential")]
    InvalidPreCredential,
    /// An issuance encoding `C` is malformed or inadmissible.
    #[error("invalid issuance encoding")]
    InvalidIssuanceEncoding,

    // ----- protocol layer ------------------------------------------------------------------
    /// A Fiat-Shamir proof (`π_id`, `π_att`, `π_iss`, `π_prove`, or a stand-alone proof) does
    /// not verify.
    #[error("invalid proof")]
    InvalidProof,
    /// A credential request carries more attestations than the limit the helper set
    /// ([`crate::pcreds::Policy::with_max_attestations`]; there is none by default).
    #[error(
        "too many attestations: the policy verifies at most {max}, the request carries {actual}"
    )]
    TooManyAttestations {
        /// The cap of the policy.
        max: usize,
        /// The number of attestations in the request.
        actual: usize,
    },
    /// The helper's issuance record ([`crate::pcreds::IssuanceStore`]) failed; nothing was
    /// released.
    #[error("issuance store error: {0}")]
    Storage(String),
    /// The identifier does not belong to the user key it is used with (`id ≠ Tag(usk, x_0)`), or
    /// a user (or a pending attestation) belongs to another deployment.
    #[error("the identifier does not belong to the user key")]
    IdentifierMismatch,
    /// The issuance state does not belong to the user (or the deployment) it is used with
    /// (`Unblind`).
    #[error("the issuance state does not match the user key")]
    IssuanceStateMismatch,
    /// A threshold `0` would hand out credentials without any endorser; root users are admitted
    /// by the helper's explicit decision instead ([`crate::pcreds::Decision::Root`]).
    #[error("threshold 0 is not a valid policy")]
    ZeroThreshold,
    /// Received public parameters are not the output of the transparent `Setup` for their own
    /// deployment label.
    #[error("public parameters are not an output of Setup: {0}")]
    InvalidPublicParameters(&'static str),

    // ----- lattice instantiation (feature `lattice`) -----------------------------------------
    /// The helper key has answered `Q_max = 2^48` calls of `SampPre` (`BlindIssue` of `Σ-vSIS`):
    /// the issuance cap of the paper's post-quantum instantiation (§6.2.3, "Issuance cap"). The
    /// helper rotates its key (a new `KeyGen`) and publishes the new `hvk`; the key issues nothing
    /// from now on.
    #[cfg(feature = "lattice")]
    #[error("issuance cap reached: the helper key has answered Q_max = 2^48 preimage requests")]
    IssuanceCapReached,
    /// A failure inside the lattice backends (Jali or `ntru-trapdoor`) that is not one of the
    /// paper's `⊥`: a parameter set refused at load time, a prover that exhausted its restarts
    /// with fresh seeds, a sampler that exhausted its attempts. Carried as the backend's display
    /// string, like the other foreign errors.
    #[cfg(feature = "lattice")]
    #[error("lattice backend error: {0}")]
    LatticeBackend(String),

    // ----- encoding / hashing --------------------------------------------------------------
    /// An object handed to an algorithm contains a value that is NOT an element of the group its
    /// type stands for: a point that is not on the curve, or not in the prime-order subgroup
    /// (`ark_serialize::Valid::check` fails). The payload names the offending argument.
    ///
    /// Implementation note. In the paper every `t`, `id`, `Ĉ`, `σ*`, `hvk`, ... is a group
    /// element by definition. In code a value of type `E::G1` is only ASSUMED to be one:
    /// validated decoding ([`crate::serialization::from_bytes`], the compact decoders) guarantees
    /// it, but a value that was decoded without validation, from an uncompressed encoding, or assembled
    /// by hand need not be. The algorithms of [`crate::pcreds`] therefore re-validate what they
    /// receive from another party and do not depend on how it was built. This is load-bearing:
    /// pairing checks are blind to a component of small order in a `G_1` argument, and a Schnorr
    /// clause whose target carries a component of order 3 (the cofactor of BLS12-381 `G_1` is
    /// divisible by 3) is forgeable with probability 1/3 per attempt, which would let ONE
    /// attester pass for several and a requester endorse itself.
    #[error("not an element of its prime-order group (curve or subgroup check failed): {0}")]
    InvalidGroupElement(&'static str),
    /// A value the paper requires to be non-degenerate is the identity / zero
    /// ("verification must re-impose what the algebra drops").
    #[error("degenerate input: {0}")]
    DegenerateInput(&'static str),
    /// Canonical (de)serialization failed.
    #[error("serialization error: {0}")]
    Serialization(String),
    /// Bytes were left over after deserializing a value (non-canonical wire encoding).
    #[error("trailing bytes after the encoded value")]
    TrailingBytes,
    /// Hashing to the curve failed.
    #[error("hash-to-curve error: {0}")]
    HashToCurve(String),
}

impl From<SerializationError> for Error {
    fn from(e: SerializationError) -> Self {
        Self::Serialization(e.to_string())
    }
}

impl From<HashToCurveError> for Error {
    fn from(e: HashToCurveError) -> Self {
        Self::HashToCurve(e.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn foreign_errors_convert() {
        let e: Error = SerializationError::InvalidData.into();
        assert!(matches!(e, Error::Serialization(_)));
        let e: Error = HashToCurveError::MapToCurveError("no point".into()).into();
        assert_eq!(e, Error::HashToCurve("no point".into()));
    }

    #[test]
    fn display_is_informative() {
        let e = Error::LengthMismatch {
            expected: 3,
            actual: 2,
        };
        assert_eq!(e.to_string(), "length mismatch: expected 3, got 2");
    }
}
