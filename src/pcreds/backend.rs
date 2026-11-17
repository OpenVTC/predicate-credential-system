//! The interface between the protocol `Π_PCreds` and an instantiation of its building blocks.
//!
//! "The protocol uses a credential base `Σ` (Def. "Credential base") that certifies the user's
//! tag key `usk`, a key-injective PRF `Tag` (Def. "Key-injective PRF"), and an online
//! simulation-extractable NIZK" (§5.2). A [`Backend`] is one such triple, together with the
//! algebra its proofs run over: the protocol ([`crate::pcreds::Protocol`]) is written once,
//! generic over the backend, exactly as the protocol box of the paper is generic over `Σ`, `Tag`
//! and the NIZK. The pairing-based instantiations of §6 (`Σ-PS`, `Σ-BBS` with `Tag_DDH`,
//! `Tag_DY`, generalized Schnorr proofs) are [`crate::pcreds::pairing::PairingBackend`]; the
//! post-quantum instantiation (`Σ-vSIS`, `Tag_LWR`, Jali proofs) is `pcreds::lattice::LatticeBackend`
//! (feature `lattice`).
//!
//! | paper | here |
//! |---|---|
//! | `pp_Σ ← Σ.PGen(1^λ)`, `pp_Tag`; `H_id`, `H_req` into `X`, the rule `x_Q ≠ x_0` | [`Backend::setup`], [`Backend::identifier_point`], [`Backend::request_point`], [`Backend::same_point`] |
//! | `TagKeyGen`, `TagEval`, `t ∈ T` | [`Backend::tag_keygen`], [`Backend::tag`], [`Backend::check_tag`] |
//! | `Σ.KeyGen`, `V_pp` | [`Backend::keygen`], [`Backend::check_key`] |
//! | `Σ.PrepareIssue`, `Σ.BlindIssue`, `Σ.Unblind`, `Σ.Verify` | [`Backend::prepare_issue`], [`Backend::blind_issue`], [`Backend::unblind`], [`Backend::verify`] |
//! | `π_id` for `R_Tag` | [`Backend::prove_tag`], [`Backend::check_tag_proof`] |
//! | `Σ.ReRand` and `π_att` for `R_att` | [`Backend::prove_attestation`], [`Backend::check_attestation_proof`] |
//! | `π_iss` for `R_iss` | [`Backend::prove_issuance`], [`Backend::check_issuance_proof`] |
//! | `Σ.ReRand` and `π_prove` for `R_Possess` | [`Backend::prove_possession`], [`Backend::check_possession_proof`] |
//!
//! The verifiers of the backend run the public checks of the relations ("verification also runs
//! the public checks of the base's relations and rejects malformed encodings", §5.2) and
//! re-validate every value they receive, whatever way it was built; the protocol rebuilds every
//! proof context from public data and hands it in.

use core::fmt::Debug;

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, Write};
use ark_std::rand::{CryptoRng, RngCore};
use zeroize::{Zeroize, Zeroizing};

use crate::{error::Error, hash::Transcript};

/// The four proofs of the protocol, for the fixed-format encoding of a proof
/// ([`Backend::serialize_proof_compact`]): the shape of a proof is a constant of the backend and
/// of the relation (for the pairing backends, the number of responses, never a number taken from
/// the wire; for the lattice backend, a length that the decoder bounds by the kind's maximum
/// before it reads the proof).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ProofKind {
    /// `π_id` for `R_Tag` at `(id, x_0)`.
    Identifier,
    /// `π_att` for `R_att`.
    Attestation,
    /// `π_iss` for `R_iss`.
    Issuance,
    /// `π_prove` for `R_Possess`.
    Possession,
}

/// The leaves of the messages by their role, for the length bounds of the JSON forms of the
/// messages ([`Backend::max_leaf_bytes`], feature `serde`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Leaf {
    /// A tag: an identifier `id_Q` or an attestation tag `t`.
    Tag,
    /// A show `σ*`.
    Show,
    /// An issuance request `Ĉ`.
    Request,
    /// A pre-credential `σ̂`.
    PreCredential,
    /// A proof of the given kind.
    Proof(ProofKind),
}

/// The public statement `(vk, t, x)` of `R_att` (§5.2, "Relations"), without the show `σ*`,
/// which the prover creates with `ReRand`.
pub struct AttestationStatement<'a, Bk: Backend> {
    /// `vk = hvk`.
    pub vk: &'a Bk::VerificationKey,
    /// The attestation tag `t = Tag(usk_P, x)`.
    pub tag: &'a Bk::Tag,
    /// The recipient point `x = x_Q`.
    pub point: &'a Bk::Point,
}

/// The public statement `(vk, Ĉ, id)` of `R_iss` (§4.2, "Relations"), with the identifier
/// point `x_0 = H_id(⟨vk⟩)` of `((id, x_0), usk) ∈ R_Tag`, which the protocol derives from `vk`.
pub struct IssuanceStatement<'a, Bk: Backend> {
    /// `vk = hvk`.
    pub vk: &'a Bk::VerificationKey,
    /// The request `Ĉ = PrepareIssue(hvk, usk; τ)`.
    pub request: &'a Bk::Request,
    /// The identifier `id = Tag(usk, x_0)`.
    pub id: &'a Bk::Tag,
    /// The identifier point `x_0 = H_id(⟨vk⟩)`.
    pub x0: &'a Bk::Point,
}

// Written by hand: a derive would bound the marker type `Bk`.
impl<Bk: Backend> Clone for AttestationStatement<'_, Bk> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<Bk: Backend> Copy for AttestationStatement<'_, Bk> {}

impl<Bk: Backend> Debug for AttestationStatement<'_, Bk> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("AttestationStatement")
            .field("vk", self.vk)
            .field("tag", self.tag)
            .field("point", self.point)
            .finish()
    }
}

impl<Bk: Backend> Clone for IssuanceStatement<'_, Bk> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<Bk: Backend> Copy for IssuanceStatement<'_, Bk> {}

impl<Bk: Backend> Debug for IssuanceStatement<'_, Bk> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("IssuanceStatement")
            .field("vk", self.vk)
            .field("request", self.request)
            .field("id", self.id)
            .field("x0", self.x0)
            .finish()
    }
}

/// An instantiation of `Π_PCreds`: a credential base, a key-injective PRF and a NIZK for the
/// relations `R_Tag`, `R_att`, `R_iss` and `R_Possess`, which share the key `usk` across their
/// clauses (§5.2, "Relations").
///
/// The implementing type is a marker; the parameters of a deployment are [`Self::Params`]. The
/// associated types are the formats of the paper's objects. Secrets (`usk`, `sk`, `τ`, the
/// credential) are [`Zeroize`]; the protocol wraps them in types that wipe them on drop and
/// redact them in `Debug`.
///
/// Contract for implementors: the `check_*` functions are deterministic, never panic on
/// adversarial input, re-validate every value they are given (an object may have been decoded
/// without validation or assembled by hand) and report the reason of a rejection as an
/// [`Error`]; the `prove_*` functions refuse a witness that does not satisfy their relation
/// ([`Error::WitnessDoesNotSatisfyRelation`]) instead of producing a proof that cannot verify.
/// The public types that the verification of an attestation reads are `Send + Sync`, so that a
/// helper can verify the attestations of a request in parallel (feature `parallel`).
pub trait Backend: Sized + Clone + Debug + PartialEq + Eq + Send + Sync + 'static {
    /// The parameters of a deployment that the label determines: `pp_Σ` and `pp_Tag`.
    type Params: Clone
        + Debug
        + PartialEq
        + Eq
        + CanonicalSerialize
        + CanonicalDeserialize
        + Send
        + Sync;
    /// The user key `usk`: the key of the tag and the message the credential certifies.
    /// `Clone` so that a user can reuse its key with another helper of the deployment
    /// ([`crate::pcreds::Protocol::register_reusing`]); the protocol never copies it otherwise.
    type UserKey: Clone + Zeroize + CanonicalSerialize + CanonicalDeserialize;
    /// Evaluation points `x ∈ X`: the identifier point `x_0` and the recipient points `x_Q`.
    type Point: Clone
        + Debug
        + PartialEq
        + Eq
        + CanonicalSerialize
        + CanonicalDeserialize
        + Send
        + Sync;
    /// Tags `t ∈ T`: identifiers `id = Tag(usk, x_0)` and attestation tags.
    type Tag: Clone
        + Debug
        + PartialEq
        + Eq
        + CanonicalSerialize
        + CanonicalDeserialize
        + Send
        + Sync;
    /// The helper's verification key `hvk = vk`.
    type VerificationKey: Clone
        + Debug
        + PartialEq
        + Eq
        + CanonicalSerialize
        + CanonicalDeserialize
        + Send
        + Sync;
    /// The helper's issuing key `sk`.
    type SigningKey: Zeroize + CanonicalSerialize + CanonicalDeserialize;
    /// The issuance request `Ĉ = usk_hat`.
    type Request: Clone + Debug + PartialEq + Eq + CanonicalSerialize + CanonicalDeserialize;
    /// The issuance randomness `τ`, kept by the requester from `PrepareIssue` to `Unblind`.
    type IssuanceTape: Zeroize + CanonicalSerialize + CanonicalDeserialize;
    /// The pre-credential `σ̂ = BlindIssue(sk, Ĉ)`.
    type PreCredential: Clone + Debug + PartialEq + Eq + CanonicalSerialize + CanonicalDeserialize;
    /// The credential `σ`, private to its holder.
    type Credential: Clone + PartialEq + Eq + Zeroize + CanonicalSerialize + CanonicalDeserialize;
    /// The public credential encoding `σ*` of a show (empty for a base whose signatures do not
    /// re-randomize).
    type Show: Clone
        + Debug
        + PartialEq
        + Eq
        + CanonicalSerialize
        + CanonicalDeserialize
        + Send
        + Sync;
    /// A proof of the NIZK.
    type Proof: Clone
        + Debug
        + PartialEq
        + Eq
        + CanonicalSerialize
        + CanonicalDeserialize
        + Send
        + Sync;

    /// The name of the instantiation (base and tag); it enters the digest of `pp`, so that two
    /// instantiations under one deployment label never share a digest.
    fn name() -> String;

    /// The parameters of the deployment `label`. Deterministic (transparent setup).
    ///
    /// # Errors
    /// If a parameter cannot be derived.
    fn setup(label: &[u8]) -> Result<Self::Params, Error>;

    /// The checks of RECEIVED parameters that do not depend on how they were derived: every
    /// element valid, no degenerate generator, a tag under which `Register` terminates.
    ///
    /// # Errors
    /// [`Error::InvalidGroupElement`] or [`Error::DegenerateInput`].
    fn check_params(params: &Self::Params) -> Result<(), Error>;

    /// The point of `X` that the random oracle `H_id` assigns to an absorbed input: the protocol
    /// frames `⟨hvk⟩` into `transcript` (after the digest of `pp`), the backend maps its output
    /// to `X`. The identifier point of a helper key, `x_0 = H_id(⟨hvk⟩)`.
    fn identifier_point(params: &Self::Params, transcript: &Transcript) -> Self::Point;

    /// The point of `X` that the random oracle `H_req` assigns to an absorbed input: the
    /// protocol frames `⟨pp, hvk, id_Q, j_Q⟩` into `transcript`, the backend maps its output to
    /// `X`. Independent of [`Self::identifier_point`] (the transcripts belong to different
    /// oracles, and a backend that maps both into one oracle of its own separates them again).
    fn request_point(params: &Self::Params, transcript: &Transcript) -> Self::Point;

    /// Whether two points are the same element of `X`, the test of the rule "`j_Q` is the least
    /// nonnegative counter for which `x_Q ≠ x_0`". The default compares the values; a backend
    /// whose points stand for their oracle input compares the elements they define.
    fn same_point(params: &Self::Params, a: &Self::Point, b: &Self::Point) -> bool {
        let _ = params;
        a == b
    }

    /// `TagKeyGen(1^λ)`.
    fn tag_keygen<R: RngCore + CryptoRng + ?Sized>(
        params: &Self::Params,
        rng: &mut R,
    ) -> Self::UserKey;

    /// `TagEval(usk, x)`; `None` for `⊥`.
    fn tag(params: &Self::Params, usk: &Self::UserKey, point: &Self::Point) -> Option<Self::Tag>;

    /// `t ∈ T`, for a tag received from another party: re-validation of its encoding
    /// ([`Error::InvalidGroupElement`] with `what` as the name of the argument) and the range
    /// test ([`Error::InvalidTag`]).
    ///
    /// # Errors
    /// As described.
    fn check_tag(
        params: &Self::Params,
        tag: &Self::Tag,
        point: &Self::Point,
        what: &'static str,
    ) -> Result<(), Error>;

    /// `Σ.KeyGen(pp)`.
    fn keygen<R: RngCore + CryptoRng + ?Sized>(
        params: &Self::Params,
        rng: &mut R,
    ) -> (Self::VerificationKey, Self::SigningKey);

    /// `hvk ∈ V_pp`: re-validation ([`Error::InvalidGroupElement`]) and the admissible key
    /// domain of the base ([`Error::InvalidKey`]).
    ///
    /// # Errors
    /// As described.
    fn check_key(params: &Self::Params, vk: &Self::VerificationKey) -> Result<(), Error>;

    /// Whether `sk` is the issuing key behind `vk`.
    fn key_pair_matches(
        params: &Self::Params,
        vk: &Self::VerificationKey,
        sk: &Self::SigningKey,
    ) -> bool;

    /// The encoding of `sk` for a helper that stores it BEFORE it answers up to `n` more
    /// `BlindIssue` calls: a key that counts its issuances (the cap `Q_max` of the lattice
    /// backend) is encoded with its count advanced by `n`, so that a restart from the stored copy
    /// never reuses a unit of the cap. The default is the plain encoding, for keys without a
    /// count. In a buffer that is wiped on drop.
    ///
    /// # Errors
    /// [`Error::Serialization`] if the key cannot be serialized; [`Error::InvalidKey`] for a
    /// wiped key of a backend that refuses to encode one.
    fn signing_key_bytes_reserving(
        sk: &Self::SigningKey,
        n: u64,
    ) -> Result<Zeroizing<Vec<u8>>, Error> {
        let _ = n;
        super::types::secret_bytes(sk)
    }

    /// `Ĉ = Σ.PrepareIssue(hvk, usk; τ)` on ONE fresh sample of `τ`, which is returned with it.
    /// A `⊥` is not retried: "If `Ĉ = ⊥`, output `(CredentialRequestFailed, ssid)` and stop this
    /// call" (protocol box, `CredentialRequest`).
    ///
    /// # Errors
    /// [`Error::InvalidIssuanceEncoding`] if `PrepareIssue` gives `⊥` or a request that the
    /// verifier of `R_iss` would refuse.
    fn prepare_issue<R: RngCore + CryptoRng + ?Sized>(
        params: &Self::Params,
        vk: &Self::VerificationKey,
        usk: &Self::UserKey,
        rng: &mut R,
    ) -> Result<(Self::Request, Self::IssuanceTape), Error>;

    /// Refuses a key that has answered as many `BlindIssue` calls as it may: the lattice
    /// backend's cap `Q_max`, at which "the helper … rotates" its key (§5.2.3, "Issuance cap").
    /// The protocol asks before it records anything ([`crate::pcreds::Protocol::respond`]). The
    /// default accepts every key, for bases without a cap.
    ///
    /// # Errors
    /// The backend's refusal (the lattice backend: `Error::IssuanceCapReached`).
    fn check_issuance_capacity(sk: &Self::SigningKey) -> Result<(), Error> {
        let _ = sk;
        Ok(())
    }

    /// `σ̂ ← Σ.BlindIssue(sk, Ĉ)`. The protocol calls it after it has added the identifier to
    /// `I` ([`crate::pcreds::Protocol::respond`], as the protocol box: "adds `id_Q` to `I` and
    /// replies `(ssid, σ̂)` with `σ̂ ← BlindIssue(sk, Ĉ)`").
    ///
    /// # Errors
    /// [`Error::InvalidIssuanceEncoding`] if `BlindIssue` returns `⊥`; a backend's own refusals
    /// (the lattice backend: `Error::IssuanceCapReached` at the cap).
    fn blind_issue<R: RngCore + CryptoRng + ?Sized>(
        params: &Self::Params,
        sk: &Self::SigningKey,
        request: &Self::Request,
        rng: &mut R,
    ) -> Result<Self::PreCredential, Error>;

    /// `σ = Σ.Unblind(hvk, usk, σ̂, τ)` and the check `Σ.Verify(hvk, usk, σ) = 1` (§5.2,
    /// `CredentialRequestResponse`), failing closed: an answer of the helper that does not give
    /// a valid credential is noticed here.
    ///
    /// # Errors
    /// [`Error::InvalidGroupElement`] if `σ̂` is not well formed; [`Error::InvalidPreCredential`]
    /// if unblinding or verification fails.
    fn unblind(
        params: &Self::Params,
        vk: &Self::VerificationKey,
        usk: &Self::UserKey,
        pre: &Self::PreCredential,
        tau: &Self::IssuanceTape,
    ) -> Result<Self::Credential, Error>;

    /// `Σ.Verify(hvk, usk, σ)`, including the re-validation of `σ`.
    fn verify(
        params: &Self::Params,
        vk: &Self::VerificationKey,
        usk: &Self::UserKey,
        cred: &Self::Credential,
    ) -> bool;

    /// `π_id ← zkPoK_ctx{((t, x), usk) ∈ R_Tag}`.
    ///
    /// # Errors
    /// [`Error::InvalidTag`] if `t ∉ T`; [`Error::WitnessDoesNotSatisfyRelation`] if
    /// `t ≠ Tag(usk, x)`.
    fn prove_tag<R: RngCore + CryptoRng + ?Sized>(
        params: &Self::Params,
        tag: &Self::Tag,
        point: &Self::Point,
        usk: &Self::UserKey,
        ctx: &[u8],
        rng: &mut R,
    ) -> Result<Self::Proof, Error>;

    /// The check of `π_id` for `(t, x)` under `ctx`, for a tag that passed [`Self::check_tag`].
    ///
    /// # Errors
    /// [`Error::InvalidProof`].
    fn check_tag_proof(
        params: &Self::Params,
        tag: &Self::Tag,
        point: &Self::Point,
        ctx: &[u8],
        proof: &Self::Proof,
    ) -> Result<(), Error>;

    /// `σ* = Σ.ReRand(hvk, usk, σ; ω)` on fresh `ω`, and
    /// `π_att ← zkPoK_ctx{((hvk, σ*, t, x), (usk, σ, ω)) ∈ R_att}`.
    ///
    /// # Errors
    /// [`Error::WitnessDoesNotSatisfyRelation`] if `σ` is not a credential of `usk` under
    /// `hvk`, or `t ≠ Tag(usk, x)`.
    fn prove_attestation<R: RngCore + CryptoRng + ?Sized>(
        params: &Self::Params,
        statement: &AttestationStatement<'_, Self>,
        usk: &Self::UserKey,
        cred: &Self::Credential,
        ctx: &[u8],
        rng: &mut R,
    ) -> Result<(Self::Show, Self::Proof), Error>;

    /// The check of `π_att` for `(hvk, σ*, t, x)` under `ctx`, for a key that passed
    /// [`Self::check_key`] and a tag that passed [`Self::check_tag`]: the public checks of
    /// `R_Possess` on `σ*` ([`Error::InvalidGroupElement`], [`Error::InvalidCredential`]), then
    /// the proof ([`Error::InvalidProof`]).
    ///
    /// # Errors
    /// As described.
    fn check_attestation_proof(
        params: &Self::Params,
        statement: &AttestationStatement<'_, Self>,
        show: &Self::Show,
        ctx: &[u8],
        proof: &Self::Proof,
    ) -> Result<(), Error>;

    /// `π_iss ← zkPoK_ctx{((hvk, Ĉ, id), (usk, τ)) ∈ R_iss}`.
    ///
    /// # Errors
    /// [`Error::WitnessDoesNotSatisfyRelation`] if the witness does not satisfy the relation.
    fn prove_issuance<R: RngCore + CryptoRng + ?Sized>(
        params: &Self::Params,
        statement: &IssuanceStatement<'_, Self>,
        usk: &Self::UserKey,
        tau: &Self::IssuanceTape,
        ctx: &[u8],
        rng: &mut R,
    ) -> Result<Self::Proof, Error>;

    /// The check of `π_iss` for `(hvk, Ĉ, id)` under `ctx`, for a key that passed
    /// [`Self::check_key`] and an identifier that passed [`Self::check_tag`]: the public checks
    /// of `R_PrepareIssue` on `Ĉ` ([`Error::InvalidGroupElement`],
    /// [`Error::InvalidIssuanceEncoding`]), then the proof ([`Error::InvalidProof`]).
    ///
    /// # Errors
    /// As described.
    fn check_issuance_proof(
        params: &Self::Params,
        statement: &IssuanceStatement<'_, Self>,
        ctx: &[u8],
        proof: &Self::Proof,
    ) -> Result<(), Error>;

    /// `σ* = Σ.ReRand(hvk, usk, σ; ω)` on fresh `ω`, and
    /// `π_prove ← zkPoK_ctx{((hvk, σ*), (usk, σ, ω)) ∈ R_Possess}`.
    ///
    /// # Errors
    /// [`Error::WitnessDoesNotSatisfyRelation`] if `σ` is not a credential of `usk`.
    fn prove_possession<R: RngCore + CryptoRng + ?Sized>(
        params: &Self::Params,
        vk: &Self::VerificationKey,
        usk: &Self::UserKey,
        cred: &Self::Credential,
        ctx: &[u8],
        rng: &mut R,
    ) -> Result<(Self::Show, Self::Proof), Error>;

    /// The check of `π_prove` for `(hvk, σ*)` under `ctx`, for a key that passed
    /// [`Self::check_key`]: the public checks of `R_Possess` ([`Error::InvalidGroupElement`],
    /// [`Error::InvalidCredential`]), then the proof ([`Error::InvalidProof`]).
    ///
    /// # Errors
    /// As described.
    fn check_possession_proof(
        params: &Self::Params,
        vk: &Self::VerificationKey,
        show: &Self::Show,
        ctx: &[u8],
        proof: &Self::Proof,
    ) -> Result<(), Error>;

    /// Size in bytes of the fixed-format encoding of `proof`.
    fn proof_compact_size(proof: &Self::Proof) -> usize;

    /// An upper bound on the canonical encoding of a leaf of a message, in bytes, at least the
    /// size of every valid leaf of that role. The JSON decoders of the messages (feature
    /// `serde`) refuse a text longer than the multibase form of this many bytes before they
    /// decode it ([`crate::serialization::max_multibase_len`]): base58btc takes time quadratic
    /// in the length of a string, which a bound per leaf keeps linear in the length of a message.
    /// The default, `usize::MAX`, bounds nothing.
    fn max_leaf_bytes(leaf: Leaf) -> usize {
        let _ = leaf;
        usize::MAX
    }

    /// Writes the fixed-format encoding of a proof of the given kind.
    ///
    /// # Errors
    /// [`Error::LengthMismatch`] if the proof does not have the shape the kind implies;
    /// [`Error::Serialization`] if the writer fails.
    fn serialize_proof_compact<W: Write>(
        kind: ProofKind,
        proof: &Self::Proof,
        writer: W,
    ) -> Result<(), Error>;

    /// Reads the fixed-format encoding of a proof of the given kind, with validation.
    ///
    /// # Errors
    /// [`Error::Serialization`] on truncated, malformed or non-canonical input.
    fn deserialize_proof_compact<R: Read>(kind: ProofKind, reader: R)
    -> Result<Self::Proof, Error>;
}
