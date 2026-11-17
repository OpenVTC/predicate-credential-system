//! The objects of `Π_PCreds` (§5.2): public parameters, the helper's key and state, users,
//! credentials, the issuance state, and the messages of the interfaces of `F_PCreds`.
//!
//! | paper | here |
//! |---|---|
//! | `pp = (pp_Σ, H_id, H_req, H_1)` | [`PublicParameters`] (the oracles are fixed functions of the deployment label) |
//! | the threshold policy `Pol_k` | [`Policy`] |
//! | `hvk`, checked once: "users return `⊥` if `hvk ∉ V_pp`", and its identifier point `x_0 = H_id(⟨hvk⟩)` | [`HelperKey`] |
//! | the helper: `(hvk, sk)` and the set `I` of issued identifiers | [`Helper`], [`IssuanceStore`], [`IssuanceRecord`] |
//! | a user registered with a helper: `usk_P`, `id_P = Tag(usk_P, x_0)` | [`User`] |
//! | the credential `σ` | [`Credential`] |
//! | `τ`, kept from `PrepareIssue` to `Unblind` | [`IssuanceState`] |
//! | `(ssid, id_Q, π_id)` | [`AttestationRequest`] |
//! | `att = (t_{P→Q}, σ*, π_att)` | [`Attestation`] |
//! | `(ssid, id_Q, att⃗, Ĉ, π_iss)` | [`CredentialRequest`] |
//! | the helper's retained `(ssid, id_Q, Ĉ)`, `N''` and `v` | [`EvaluatedRequest`] |
//! | `d ∈ {policy, root}` | [`Decision`] |
//! | `(ssid, Fail)`, `(ssid, issued)`, `(ssid, σ̂)` | [`Reply`] |
//! | `π = (σ*, π_prove)` on a message `m` | [`MembershipProof`] |
//!
//! Public objects derive the canonical (self-describing) serialization, and the messages also
//! have the fixed-format compact encoding of [`super::codec`] and, with the feature `serde`, a
//! structured JSON form (encoded by derive, decoded by the strict decoders of
//! [`crate::serialization`]). Secrets are wiped on drop, print
//! as `<redacted>`, and are not `Clone` (the credential excepted, as a backup may be wanted);
//! their encodings live in buffers that are wiped on drop.
//!
//! # Validity of received objects
//!
//! Implementation note. The messages have public fields, so a value of these types can be built
//! in any way: decoded with validation (the decoders of this crate), decoded WITHOUT validation,
//! or assembled by hand. **The algorithms of [`Protocol`](super::Protocol) do not rely on
//! validated decoding**: every algorithm that consumes an object of another party re-validates
//! it (curve and prime-order subgroup of every group element) before anything else.

use core::fmt;
use std::collections::BTreeSet;

use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, Read, SerializationError, Valid, Validate,
    Write,
};
use zeroize::{Zeroize, Zeroizing};

use super::backend::Backend;
use crate::error::Error;

/// The compressed canonical encoding of a SECRET in a buffer that is wiped on drop. The buffer
/// is sized up front, so it never moves and no unwiped copy is left behind.
pub(crate) fn secret_bytes<V: CanonicalSerialize + ?Sized>(
    value: &V,
) -> Result<Zeroizing<Vec<u8>>, Error> {
    let mut bytes = Zeroizing::new(Vec::with_capacity(value.compressed_size()));
    value.serialize_compressed(&mut *bytes)?;
    Ok(bytes)
}

// ---------------------------------------------------------------------------------------------
// Parameters and policy
// ---------------------------------------------------------------------------------------------

/// The public parameters `pp = (pp_Σ, H_id, H_req, H_1)` (protocol box, `Setup`). The
/// identifier point is not part of `pp`: "once the helper publishes `hvk`, set
/// `x_0 = H_id(⟨hvk⟩)`" ([`HelperKey::identifier_point`]).
///
/// Implementation note: `H_id`, `H_req` and `H_1` are fixed functions of the deployment label
/// ([`crate::hash`], [`super::Protocol::identifier_point`], [`super::Protocol::recipient_point`]),
/// so the label stands for them here. `Setup` is transparent: every field is determined by the
/// label, and [`Protocol::from_public_parameters`](super::Protocol::from_public_parameters)
/// accepts a received value only if it is what `Setup` derives from the label it carries.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct PublicParameters<Bk: Backend> {
    /// The deployment label; it determines the oracles `H_id`, `H_req` and `H_1` and every
    /// parameter.
    pub label: Vec<u8>,
    /// The parameters of the instantiation: `pp_Σ` and `pp_Tag`.
    pub params: Bk::Params,
}

/// The threshold policy `Pol_k`: "accepts iff `|E| ≥ k`" (Theorem "Security of `Π_PCreds`"),
/// for a threshold `k ≥ 1`, the HELPER's input. The helper evaluates it on the set `N''` of the
/// distinct tags of the valid attestations of a request (protocol box: "`v = valid` iff
/// `|N''| ≥ k`"), whatever number of attestations the request carries: a request with more than
/// `k` attestations is evaluated like any other, and its duplicates and invalid attestations
/// count for nothing.
///
/// Implementation notes, not part of the paper:
///
/// * **`k ≥ 1`.** "The threshold policy never accepts a first request" (Remark "Root users and
///   chaining") only because `k ≥ 1`; a threshold `0` would issue to every requester with a
///   valid issuance proof. [`Policy::threshold`] refuses it ([`Error::ZeroThreshold`]); root
///   users are admitted by the helper's explicit [`Decision::Root`].
/// * **An optional resource limit.** The helper verifies every attestation a request carries,
///   and the requester chooses their number, so the work of one request has no bound of its own.
///   A helper that wants one sets it with [`Self::with_max_attestations`]: a request with more
///   attestations is then refused before any of them is verified
///   ([`Error::TooManyAttestations`]). This is an operational limit like a maximum message size,
///   outside `Pol_k`, and there is none by default; a limit far above `k` costs honest
///   requesters nothing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Policy {
    threshold: usize,
    max_attestations: Option<usize>,
}

impl Policy {
    /// `Pol_k`, with no limit on the number of attestations of a request.
    ///
    /// # Errors
    /// [`Error::ZeroThreshold`] for `k = 0`.
    pub fn threshold(k: usize) -> Result<Self, Error> {
        if k == 0 {
            return Err(Error::ZeroThreshold);
        }
        Ok(Self {
            threshold: k,
            max_attestations: None,
        })
    }

    /// The same policy, with a helper that refuses requests carrying more than `max`
    /// attestations before it verifies any (an operational limit, not part of `Pol_k`).
    ///
    /// # Errors
    /// [`Error::DegenerateInput`] if `max < k`, under which no request could be valid.
    pub fn with_max_attestations(self, max: usize) -> Result<Self, Error> {
        if max < self.threshold {
            return Err(Error::DegenerateInput(
                "the limit on attestations is below the threshold",
            ));
        }
        Ok(Self {
            max_attestations: Some(max),
            ..self
        })
    }

    /// The threshold `k`.
    #[must_use]
    pub fn k(&self) -> usize {
        self.threshold
    }

    /// The largest number of attestations a request may carry, if the helper set a limit.
    #[must_use]
    pub fn max_attestations(&self) -> Option<usize> {
        self.max_attestations
    }

    /// `Pol_k` on the number of distinct valid tags: `valid` iff `|N''| ≥ k`.
    #[must_use]
    pub fn accepts(&self, distinct: usize) -> bool {
        distinct >= self.threshold
    }
}

// ---------------------------------------------------------------------------------------------
// The helper
// ---------------------------------------------------------------------------------------------

/// A helper key `hvk` that has passed the admissibility check `hvk ∈ V_pp` under ONE deployment,
/// with its identifier point `x_0 = H_id(⟨hvk⟩)` ("once the helper publishes `hvk`, set
/// `x_0 = H_id(⟨hvk⟩)`"; "each helper key determines its own identifier point"). Every algorithm
/// takes the key in this form, so that each party checks a helper key, and derives its `x_0`,
/// once ([`Protocol::helper_key`](super::Protocol::helper_key); "users return `⊥` if
/// `hvk ∉ V_pp`"). It is not decodable: whoever receives `hvk` checks it.
pub struct HelperKey<Bk: Backend> {
    pub(super) vk: Bk::VerificationKey,
    pub(super) digest: [u8; 32],
    /// `x_0 = H_id(⟨hvk⟩)`, a function of `vk` and the deployment.
    pub(super) x0: Bk::Point,
    /// The fingerprint of `vk` under the deployment, which binds users and pending requests to
    /// this key; a function of `vk` and the deployment.
    pub(super) fingerprint: [u8; 32],
}

impl<Bk: Backend> HelperKey<Bk> {
    /// The verification key, e.g. to publish it.
    #[must_use]
    pub fn vk(&self) -> &Bk::VerificationKey {
        &self.vk
    }

    /// The digest of the public parameters under which the key was checked.
    #[must_use]
    pub fn parameters_digest(&self) -> &[u8; 32] {
        &self.digest
    }

    /// The identifier point `x_0 = H_id(⟨hvk⟩)` of this key, at which the identifiers of its
    /// users are evaluated.
    #[must_use]
    pub fn identifier_point(&self) -> &Bk::Point {
        &self.x0
    }

    /// The fingerprint of the key under its deployment (a digest of `pp` and `hvk`): the value
    /// that binds a [`User`] and a pending attestation request to this key.
    #[must_use]
    pub fn fingerprint(&self) -> &[u8; 32] {
        &self.fingerprint
    }
}

// Written by hand: derives would bound the marker type `Bk` needlessly.
impl<Bk: Backend> Clone for HelperKey<Bk> {
    fn clone(&self) -> Self {
        Self {
            vk: self.vk.clone(),
            digest: self.digest,
            x0: self.x0.clone(),
            fingerprint: self.fingerprint,
        }
    }
}

/// Compares the key and the deployment; `x_0` and the fingerprint are functions of the two.
impl<Bk: Backend> PartialEq for HelperKey<Bk> {
    fn eq(&self, other: &Self) -> bool {
        self.vk == other.vk && self.digest == other.digest
    }
}

impl<Bk: Backend> Eq for HelperKey<Bk> {}

impl<Bk: Backend> fmt::Debug for HelperKey<Bk> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("HelperKey").field(&self.vk).finish()
    }
}

/// The set `I` of identifiers the helper has issued to (protocol box: "initialize the set of
/// issued identifiers `I ← ∅`"), behind which a deployment may put its own storage.
///
/// Remark "Concurrency": "an honest helper records its first issuance to an identifier before
/// releasing the response". [`Protocol::respond`](super::Protocol::respond) answers `issued` if
/// [`Self::contains`] knows the identifier. Otherwise it adds the identifier with
/// [`Self::record`] and only then runs `BlindIssue` (protocol box: "Otherwise it adds `id_Q` to
/// `I` and replies `(ssid, σ̂)` with `σ̂ ← BlindIssue(sk, Ĉ)`"). It answers `issued` if the record
/// finds the identifier recorded already, and returns an error, running nothing, if the store
/// fails. A `BlindIssue` that fails after the record leaves the identifier in `I`, as in the
/// paper.
///
/// [`Self::record`] is a test-and-set: an implementation on storage shared by several helper
/// processes makes it atomic (insert-if-absent), so that two processes cannot both see an
/// identifier as new, and makes it durable before it returns `Ok(true)`; it fails rather than
/// forget. Identifiers enter as their canonical compressed encoding.
pub trait IssuanceStore {
    /// Whether `id` is in `I`.
    ///
    /// # Errors
    /// [`Error::Storage`] if the store cannot answer.
    fn contains(&self, id: &[u8]) -> Result<bool, Error>;

    /// Adds `id` to `I` if it is absent: `Ok(true)` if it was absent and is now recorded,
    /// durably; `Ok(false)` if it was recorded before. Atomic.
    ///
    /// # Errors
    /// [`Error::Storage`] if the store cannot answer or cannot record.
    fn record(&mut self, id: &[u8]) -> Result<bool, Error>;
}

/// The default [`IssuanceStore`]: `I` in memory, canonically serializable so that a helper can
/// persist it between runs. Deterministic encoding (the identifiers in order).
///
/// Implementation note: kept in memory only, `I` does not survive a restart, and "at most once
/// per identifier" would then hold per process only. Persist the record (with the helper's
/// key, [`Helper::to_bytes`]) after every issuance and before the reply leaves, or implement
/// [`IssuanceStore`] on durable storage.
#[derive(Clone, Debug, Default, PartialEq, Eq, CanonicalSerialize)]
pub struct IssuanceRecord {
    ids: BTreeSet<Vec<u8>>,
}

/// Nothing to check beyond the decoder: the identifiers are byte strings.
impl Valid for IssuanceRecord {
    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }
}

/// Decodes the encoding of a record: the count, then the identifiers in STRICTLY increasing
/// order, which is how the record is encoded. Implementation note: the decoder of a set in
/// arkworks collects its elements, so an encoding that lists them out of order or twice would
/// decode as well, and one record would have several encodings; this one refuses them
/// ([`crate::serialization`], "every accepted byte string is the unique encoding of the value it
/// decodes to").
impl CanonicalDeserialize for IssuanceRecord {
    fn deserialize_with_mode<R: Read>(
        reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let ids = Vec::<Vec<u8>>::deserialize_with_mode(reader, compress, validate)?;
        if !ids.windows(2).all(|pair| pair[0] < pair[1]) {
            return Err(SerializationError::InvalidData);
        }
        Ok(Self {
            ids: ids.into_iter().collect(),
        })
    }
}

impl IssuanceRecord {
    /// The empty record.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// The number of identifiers issued to.
    #[must_use]
    pub fn len(&self) -> usize {
        self.ids.len()
    }

    /// Whether nobody has been issued to.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.ids.is_empty()
    }

    /// The encodings of the identifiers issued to, in order.
    pub fn iter(&self) -> impl Iterator<Item = &[u8]> {
        self.ids.iter().map(Vec::as_slice)
    }
}

impl IssuanceStore for IssuanceRecord {
    fn contains(&self, id: &[u8]) -> Result<bool, Error> {
        Ok(self.ids.contains(id))
    }

    fn record(&mut self, id: &[u8]) -> Result<bool, Error> {
        Ok(self.ids.insert(id.to_vec()))
    }
}

/// The helper: `hvk`, its issuing key `sk`, the policy `Pol_k` and the set `I` of issued
/// identifiers (protocol box, "Helper").
///
/// Secret: `sk` is wiped on drop; not `Clone`; redacted in `Debug`.
///
/// Implementation note: **the helper belongs to ONE deployment.** Its key records the digest of
/// the `pp` it was generated (or restored) under, and every algorithm of the helper refuses it
/// under another `pp` ([`Error::InvalidKey`]). Nothing else ties a key to a deployment: a
/// credential of `Σ-PS` is a signature under `hvk` and nothing more, so a helper that served two
/// deployment labels with one key would certify, in each of them, users of the other.
pub struct Helper<Bk: Backend, S = IssuanceRecord> {
    pub(super) key: HelperKey<Bk>,
    pub(super) sk: Bk::SigningKey,
    pub(super) policy: Policy,
    pub(super) store: S,
}

impl<Bk: Backend, S> Helper<Bk, S> {
    /// `hvk`, to publish.
    #[must_use]
    pub fn key(&self) -> &HelperKey<Bk> {
        &self.key
    }

    /// The policy `Pol_k`.
    #[must_use]
    pub fn policy(&self) -> &Policy {
        &self.policy
    }

    /// The set `I` of issued identifiers.
    #[must_use]
    pub fn store(&self) -> &S {
        &self.store
    }

    /// The encoding `pp-digest ‖ hvk ‖ sk` (compressed canonical form) of the helper's KEY, in a
    /// buffer that is wiped on drop; [`Protocol::restore_helper`](super::Protocol::restore_helper)
    /// is the way back. The policy and the store are kept separately.
    ///
    /// # Errors
    /// [`Error::Serialization`] if a component cannot be serialized.
    pub fn to_bytes(&self) -> Result<Zeroizing<Vec<u8>>, Error> {
        let size = self.key.digest.compressed_size()
            + self.key.vk.compressed_size()
            + self.sk.compressed_size();
        let mut bytes = Zeroizing::new(Vec::with_capacity(size));
        self.key.digest.serialize_compressed(&mut *bytes)?;
        self.key.vk.serialize_compressed(&mut *bytes)?;
        self.sk.serialize_compressed(&mut *bytes)?;
        Ok(bytes)
    }

    /// [`Self::to_bytes`] with the issuance count of a key that counts its issuances ADVANCED by
    /// `n` ([`Backend::signing_key_bytes_reserving`]; the lattice backend's cap `Q_max`): what a
    /// helper stores BEFORE it answers up to `n` more requests, so that a restart from the stored
    /// copy never reuses a unit of the cap. Store again before the key has answered `n`. For a
    /// key without a count, the plain encoding.
    ///
    /// # Errors
    /// [`Error::Serialization`] if a component cannot be serialized; the errors of
    /// [`Backend::signing_key_bytes_reserving`].
    pub fn to_bytes_reserving(&self, n: u64) -> Result<Zeroizing<Vec<u8>>, Error> {
        let sk = Bk::signing_key_bytes_reserving(&self.sk, n)?;
        let size = self.key.digest.compressed_size() + self.key.vk.compressed_size() + sk.len();
        let mut bytes = Zeroizing::new(Vec::with_capacity(size));
        self.key.digest.serialize_compressed(&mut *bytes)?;
        self.key.vk.serialize_compressed(&mut *bytes)?;
        bytes.extend_from_slice(&sk);
        Ok(bytes)
    }
}

impl<Bk: Backend, S> Drop for Helper<Bk, S> {
    fn drop(&mut self) {
        self.sk.zeroize();
    }
}

impl<Bk: Backend, S> fmt::Debug for Helper<Bk, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Helper")
            .field("key", &self.key)
            .field("sk", &"<redacted>")
            .field("policy", &self.policy)
            .finish_non_exhaustive()
    }
}

// ---------------------------------------------------------------------------------------------
// Users, credentials, the issuance state
// ---------------------------------------------------------------------------------------------

/// A user registered with ONE helper key: its key `usk` and identifier `id = Tag(usk, x_0)` at
/// that key's identifier point `x_0 = H_id(⟨hvk⟩)` (protocol box, `Register`: "user `P`, not yet
/// registered with this helper"), in the deployment with the parameter digest it carries.
///
/// Secret: `usk` is wiped on drop; not `Clone`; redacted in `Debug`. Built by
/// [`Protocol::register`](super::Protocol::register), from a key
/// ([`Protocol::user`](super::Protocol::user)), or from the key of a registration with another
/// helper ([`Protocol::register_reusing`](super::Protocol::register_reusing)), so `id` always
/// belongs to `usk` and the key; the encoding ([`Self::to_bytes`]) is as secret as `usk`.
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct User<Bk: Backend> {
    pub(super) usk: Bk::UserKey,
    pub(super) id: Bk::Tag,
    pub(super) digest: [u8; 32],
    /// The fingerprint of the helper key the user registered with
    /// ([`HelperKey::fingerprint`]).
    pub(super) helper: [u8; 32],
}

impl<Bk: Backend> User<Bk> {
    /// The identifier `id = Tag(usk, x_0)`.
    #[must_use]
    pub fn id(&self) -> &Bk::Tag {
        &self.id
    }

    /// The digest of the public parameters of the user's deployment.
    #[must_use]
    pub fn parameters_digest(&self) -> &[u8; 32] {
        &self.digest
    }

    /// The fingerprint of the helper key the user registered with ([`HelperKey::fingerprint`]).
    #[must_use]
    pub fn helper_fingerprint(&self) -> &[u8; 32] {
        &self.helper
    }

    /// The secret key `usk`. For callers that run the backend directly (the soundness harness
    /// compares it with an extracted witness).
    #[must_use]
    pub fn expose_key(&self) -> &Bk::UserKey {
        &self.usk
    }

    /// The encoding `usk ‖ id ‖ pp-digest ‖ helper-fingerprint` in a buffer that is wiped on
    /// drop. The way back is
    /// [`WireFormat::from_bytes`](crate::serialization::WireFormat::from_bytes), followed by
    /// [`Protocol::check_user`](super::Protocol::check_user) for a value read from storage.
    ///
    /// Implementation note: this inherent method takes precedence over the blanket
    /// [`WireFormat::to_bytes`](crate::serialization::WireFormat::to_bytes), which would return
    /// the same bytes in a plain `Vec<u8>` that nobody wipes.
    ///
    /// # Errors
    /// [`Error::Serialization`] if a component cannot be serialized.
    pub fn to_bytes(&self) -> Result<Zeroizing<Vec<u8>>, Error> {
        secret_bytes(self)
    }
}

impl<Bk: Backend> Drop for User<Bk> {
    fn drop(&mut self) {
        self.usk.zeroize();
    }
}

impl<Bk: Backend> fmt::Debug for User<Bk> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("User")
            .field("usk", &"<redacted>")
            .field("id", &self.id)
            .finish_non_exhaustive()
    }
}

/// A credential `σ` of a user under `hvk`. Private to its holder: wiped on drop, redacted in
/// `Debug`. Obtained from [`Protocol::unblind`](super::Protocol::unblind), which verifies it, or
/// through [`Protocol::credential`](super::Protocol::credential) from a value of the backend.
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct Credential<Bk: Backend> {
    pub(super) inner: Bk::Credential,
}

impl<Bk: Backend> Credential<Bk> {
    /// The credential of the base.
    #[must_use]
    pub fn as_inner(&self) -> &Bk::Credential {
        &self.inner
    }

    /// The encoding of the credential in a buffer that is wiped on drop. The way back is
    /// [`WireFormat::from_bytes`](crate::serialization::WireFormat::from_bytes), followed by
    /// [`Protocol::verify_credential`](super::Protocol::verify_credential) for a value read
    /// from storage.
    ///
    /// # Errors
    /// [`Error::Serialization`] if the credential cannot be serialized.
    pub fn to_bytes(&self) -> Result<Zeroizing<Vec<u8>>, Error> {
        secret_bytes(self)
    }
}

impl<Bk: Backend> Clone for Credential<Bk> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<Bk: Backend> PartialEq for Credential<Bk> {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl<Bk: Backend> Eq for Credential<Bk> {}

impl<Bk: Backend> Drop for Credential<Bk> {
    fn drop(&mut self) {
        self.inner.zeroize();
    }
}

impl<Bk: Backend> fmt::Debug for Credential<Bk> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Credential(<redacted>)")
    }
}

/// What the requester keeps between its request and the helper's reply: `τ`, and the
/// identifier and deployment the request was made for. Secret: wiped on drop, not `Clone`,
/// redacted in `Debug`; it can be stored until the helper answers ([`Self::to_bytes`]), and its
/// encoding is as secret as `τ`.
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct IssuanceState<Bk: Backend> {
    pub(super) tau: Bk::IssuanceTape,
    pub(super) owner: Bk::Tag,
    pub(super) digest: [u8; 32],
}

impl<Bk: Backend> IssuanceState<Bk> {
    /// The encoding `τ ‖ id ‖ pp-digest` in a buffer that is wiped on drop. The way back is
    /// [`WireFormat::from_bytes`](crate::serialization::WireFormat::from_bytes).
    ///
    /// # Errors
    /// [`Error::Serialization`] if a component cannot be serialized.
    pub fn to_bytes(&self) -> Result<Zeroizing<Vec<u8>>, Error> {
        secret_bytes(self)
    }

    /// The issuance randomness `τ`. For callers that run the backend directly (the soundness
    /// harness runs the interactive protocol on the witness `(usk, τ)` of `π_iss`).
    #[must_use]
    pub fn expose_tape(&self) -> &Bk::IssuanceTape {
        &self.tau
    }
}

impl<Bk: Backend> Drop for IssuanceState<Bk> {
    fn drop(&mut self) {
        self.tau.zeroize();
    }
}

impl<Bk: Backend> fmt::Debug for IssuanceState<Bk> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("IssuanceState(<redacted>)")
    }
}

// ---------------------------------------------------------------------------------------------
// Messages
// ---------------------------------------------------------------------------------------------

/// The message `(id_Q, π_id)` of an attestation request, sent to the owner of a contact name
/// under a sub-session `ssid` (protocol box, `AttestationRequest` step (i)).
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(bound = "", rename_all = "camelCase"))]
pub struct AttestationRequest<Bk: Backend> {
    /// `id_Q`.
    #[cfg_attr(feature = "serde", serde(with = "crate::serialization::canonical"))]
    pub id: Bk::Tag,
    /// `π_id`.
    #[cfg_attr(feature = "serde", serde(with = "crate::serialization::canonical"))]
    pub proof: Bk::Proof,
}

/// An attestation `att = (t_{P→Q}, σ*, π_att)` (protocol box, `AttestationRequestResponse`
/// step (iii)). Its proof has no session context ("its statement fixes the recipient through
/// `x_Q`, and the attestation may be used in several credential requests").
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(bound = "", rename_all = "camelCase"))]
pub struct Attestation<Bk: Backend> {
    /// The attestation tag `t_{P→Q} = Tag(usk_P, x_Q)`.
    #[cfg_attr(feature = "serde", serde(with = "crate::serialization::canonical"))]
    pub tag: Bk::Tag,
    /// The show `σ*`.
    #[cfg_attr(feature = "serde", serde(with = "crate::serialization::canonical"))]
    pub show: Bk::Show,
    /// `π_att`.
    #[cfg_attr(feature = "serde", serde(with = "crate::serialization::canonical"))]
    pub proof: Bk::Proof,
}

/// The message `(id_Q, att⃗, Ĉ, π_iss)` of a credential request, sent to the helper under a
/// sub-session `ssid` (protocol box, `CredentialRequest` step (iii)).
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(bound = "", rename_all = "camelCase"))]
pub struct CredentialRequest<Bk: Backend> {
    /// `id_Q`.
    #[cfg_attr(feature = "serde", serde(with = "crate::serialization::canonical"))]
    pub id: Bk::Tag,
    /// `att⃗`, the stored attestations the requester selected.
    pub attestations: Vec<Attestation<Bk>>,
    /// `Ĉ`.
    #[cfg_attr(feature = "serde", serde(with = "crate::serialization::canonical"))]
    pub request: Bk::Request,
    /// `π_iss`.
    #[cfg_attr(feature = "serde", serde(with = "crate::serialization::canonical"))]
    pub proof: Bk::Proof,
}

/// The helper's decision `d ∈ {policy, root}` of `CredentialRequestResponse`; `Root` "admits
/// the requester as a root user" and issues regardless of the policy value (Remark "Root users
/// and chaining").
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Decision {
    /// `d = policy`: issue iff the policy accepts the request.
    Policy,
    /// `d = root`: admit the requester as a root user.
    Root,
}

/// What the helper retains of a credential request it has checked (protocol box,
/// `CredentialRequest`, the helper's steps (i) and (ii)): `(ssid, id_Q, Ĉ)`, the set `N''` of
/// distinct tags of valid attestations, and the policy value `v`. Built only by
/// [`Protocol::evaluate_request`](super::Protocol::evaluate_request), consumed by
/// [`Protocol::respond`](super::Protocol::respond), bound to the helper that evaluated it.
///
/// Implementation note: deliberately not decodable. A helper that wants to answer later keeps
/// the [`CredentialRequest`] and evaluates it again; a stored "valid" flag would be an
/// admission that nobody checked.
#[derive(Debug)]
pub struct EvaluatedRequest<Bk: Backend> {
    pub(super) fingerprint: [u8; 32],
    pub(super) ssid: Vec<u8>,
    pub(super) id: Bk::Tag,
    pub(super) request: Bk::Request,
    pub(super) tags: Vec<Bk::Tag>,
    pub(super) valid: bool,
}

impl<Bk: Backend> EvaluatedRequest<Bk> {
    /// The sub-session `ssid` of the request.
    #[must_use]
    pub fn ssid(&self) -> &[u8] {
        &self.ssid
    }

    /// The requester's identifier `id_Q`.
    #[must_use]
    pub fn id(&self) -> &Bk::Tag {
        &self.id
    }

    /// `N''`: the distinct tags of the valid attestations, in the order of the request.
    #[must_use]
    pub fn tags(&self) -> &[Bk::Tag] {
        &self.tags
    }

    /// The policy value `v`: whether `|N''| ≥ k`.
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.valid
    }
}

/// The helper's reply to a credential request (protocol box, `CredentialRequestResponse`).
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(bound = "", rename_all = "camelCase"))]
pub enum Reply<Bk: Backend> {
    /// `(ssid, Fail)`: the policy rejects and the request is not a root admission.
    Fail,
    /// `(ssid, issued)`: the identifier has been issued to before.
    Issued,
    /// `(ssid, σ̂)` with `σ̂ ← BlindIssue(sk, Ĉ)`.
    PreCredential(
        #[cfg_attr(feature = "serde", serde(with = "crate::serialization::canonical"))]
        Bk::PreCredential,
    ),
}

/// Tags of the canonical encoding of [`Reply`]: one byte, then the pre-credential.
const REPLY_FAIL: u8 = 0;
const REPLY_ISSUED: u8 = 1;
const REPLY_PRE_CREDENTIAL: u8 = 2;

impl<Bk: Backend> CanonicalSerialize for Reply<Bk> {
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        match self {
            Self::Fail => REPLY_FAIL.serialize_with_mode(writer, compress),
            Self::Issued => REPLY_ISSUED.serialize_with_mode(writer, compress),
            Self::PreCredential(pre) => {
                REPLY_PRE_CREDENTIAL.serialize_with_mode(&mut writer, compress)?;
                pre.serialize_with_mode(writer, compress)
            }
        }
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        1 + match self {
            Self::Fail | Self::Issued => 0,
            Self::PreCredential(pre) => pre.serialized_size(compress),
        }
    }
}

impl<Bk: Backend> Valid for Reply<Bk> {
    fn check(&self) -> Result<(), SerializationError> {
        match self {
            Self::Fail | Self::Issued => Ok(()),
            Self::PreCredential(pre) => pre.check(),
        }
    }
}

impl<Bk: Backend> CanonicalDeserialize for Reply<Bk> {
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        match u8::deserialize_with_mode(&mut reader, compress, validate)? {
            REPLY_FAIL => Ok(Self::Fail),
            REPLY_ISSUED => Ok(Self::Issued),
            REPLY_PRE_CREDENTIAL => Ok(Self::PreCredential(
                Bk::PreCredential::deserialize_with_mode(reader, compress, validate)?,
            )),
            _ => Err(SerializationError::InvalidData),
        }
    }
}

/// A membership proof `π = (σ*, π_prove)` on a message `m` (protocol box, `Prove`), posted
/// anonymously.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(bound = "", rename_all = "camelCase"))]
pub struct MembershipProof<Bk: Backend> {
    /// `σ*`.
    #[cfg_attr(feature = "serde", serde(with = "crate::serialization::canonical"))]
    pub show: Bk::Show,
    /// `π_prove`.
    #[cfg_attr(feature = "serde", serde(with = "crate::serialization::canonical"))]
    pub proof: Bk::Proof,
}
