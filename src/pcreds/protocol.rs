//! The protocol `Π_PCreds` of §4.2 (protocol box), for the threshold policy `Pol_k`, generic
//! over an instantiation of its building blocks ([`Backend`]).
//!
//! | protocol box | here |
//! |---|---|
//! | `Setup`: `pp = (pp_Σ, H_id, H_req, H_1)` | [`Protocol::setup`]; [`Protocol::from_public_parameters`] for a received `pp` |
//! | "Users return `⊥` if `hvk ∉ V_pp`. All parties derive `x_0 = H_id(⟨hvk⟩)`." | [`Protocol::helper_key`] |
//! | `Helper`: `(hvk, sk) ← KeyGen(pp)`, `I ← ∅` | [`Protocol::helper_keygen`]; [`Protocol::restore_helper`], [`Protocol::helper_from_key_pair`] |
//! | `Register` (i): reuse `usk_P`, or sample `usk_P ← TagKeyGen(1^λ)` | [`Protocol::register_reusing`], [`Protocol::user`]; [`Protocol::register`] |
//! | `Register` (ii): `id_P = Tag(usk_P, x_0)`, `RegisterFailed` if `id_P = ⊥` | [`Protocol::register`], [`Protocol::user`] ([`Error::UndefinedTag`]) |
//! | `ContactRegister` | none: routes are kept by the contact service (§4.1, "Communication and disclosure") |
//! | `AttestationRequest` (i): `π_id` under `(ssid, P̃)` | [`Protocol::request_attestation`] |
//! | `AttestationRequest` (ii): the owner checks `id_Q ∈ T` and `π_id`, retains the request | [`Protocol::receive_attestation_request`] → [`PendingAttestation`] |
//! | `AttestationRequestResponse`: retrieve the pending request, `t = Tag(usk_P, x_Q)`, `σ* = ReRand(…)`, `π_att` | [`Protocol::attest`], which consumes the [`PendingAttestation`] |
//! | … on the reply, `Q` checks `t ∈ T` and `π_att` | [`Protocol::check_attestation`], [`Protocol::verify_attestation`] |
//! | `CredentialRequest`: `Ĉ = PrepareIssue(hvk, usk_Q; τ)`, `CredentialRequestFailed` if `Ĉ = ⊥`, `π_iss` under `(ssid, att⃗)` | [`Protocol::request_credential`] |
//! | … the helper checks `id_Q ∈ T` and `π_iss`, computes `N''` and `v` | [`Protocol::evaluate_request`] → [`EvaluatedRequest`] |
//! | `CredentialRequestResponse`: `Fail`, `issued`, or `I ← I ∪ {id_Q}` and `σ̂ ← BlindIssue(sk, Ĉ)` | [`Protocol::respond`], which consumes the [`EvaluatedRequest`] |
//! | … `Q`: `σ_Q = Unblind(…)`, check `Verify(hvk, usk_Q, σ_Q)` | [`Protocol::unblind`], which consumes the [`IssuanceState`] |
//! | `Prove`: `σ* = ReRand(…)`, `π_prove` under `m` | [`Protocol::prove`] |
//! | `Verify` | [`Protocol::verify`] ([`Protocol::check_membership`] names the reason) |
//! | application contexts (implementation note for OpenVTC, not in the paper): `π_att` under the caller's `app`, `π_iss` under the context of each attestation and its own `app` | [`Protocol::attest_in_context`], [`Protocol::check_attestation_in_context`], [`Protocol::verify_attestation_in_context`], [`Protocol::request_credential_in_context`], [`Protocol::evaluate_request_in_context`] |
//!
//! The calls of `F_PCreds` that keep state between the messages (the attester's pending
//! request, the requester's stored attestations and retained acknowledgements, the helper's
//! pending request) are values the caller holds: [`PendingAttestation`], the [`Attestation`]s,
//! [`IssuanceState`], [`EvaluatedRequest`]. "Pending state is consumed on completion": the
//! algorithm that completes a call takes its pending state by value. Delivery, contact routing
//! and the bulletin board are the application's.
//!
//! # Implementation notes
//!
//! None of these changes what honest parties compute; each records a rule the code keeps.
//!
//! * **One deployment and one helper key per object.** [`HelperKey`], [`Helper`], [`User`],
//!   [`PendingAttestation`] and [`IssuanceState`] carry the digest of the `pp` they belong to,
//!   and every algorithm refuses them under another `pp` ([`Error::InvalidKey`],
//!   [`Error::IdentifierMismatch`], [`Error::IssuanceStateMismatch`]). A [`User`] and a
//!   [`PendingAttestation`] also carry the fingerprint of the helper key they belong to
//!   ([`HelperKey::fingerprint`]): an identifier is an evaluation at the identifier point of ONE
//!   key, and the algorithms refuse a user or a pending request with another key
//!   ([`Error::IdentifierMismatch`]). A user that registers with several helper keys of a
//!   deployment holds one [`User`] per key ([`Protocol::register_reusing`]). A helper's key
//!   serves one deployment: a credential of `Σ-PS` is a signature under `hvk` and nothing else.
//! * **Keys are checked once.** A helper key enters every algorithm as a [`HelperKey`], which
//!   only [`Protocol::helper_key`] (`hvk ∈ V_pp`) and the helper's own key generation produce,
//!   with its identifier point `x_0 = H_id(⟨hvk⟩)`.
//! * **Received objects are re-validated.** Every identifier, tag, show, request and
//!   pre-credential that comes from another party is checked (curve and prime-order subgroup of
//!   every group element, and `t ∈ T`) before anything is computed from it, whatever way it was
//!   built. Without this a tag shifted by a point of small order would be a "distinct" tag, and
//!   one source could count as several.
//! * **`π_id` gates attestations.** [`Protocol::attest`] takes the [`PendingAttestation`] that
//!   [`Protocol::receive_attestation_request`] returns after checking `π_id`: an attester never
//!   attests for an identifier whose ownership was not proven, so nobody but the owner of
//!   `id_Q` learns the attester's (deterministic) tag for `id_Q`.
//! * **Issuance runs on the evaluated request.** [`Protocol::respond`] takes the
//!   [`EvaluatedRequest`] that [`Protocol::evaluate_request`] built from a checked `π_iss`, and
//!   runs `BlindIssue` on exactly its `Ĉ`. An evaluated request is bound to the helper that
//!   evaluated it.
//! * **`Pol_k` with `k ≥ 1`** ([`Policy`]), evaluated on any number of attestations; a helper
//!   may set an operational limit on that number ([`Policy::with_max_attestations`]).
//! * **The issuance record is written before `BlindIssue` runs**, as in the protocol box ("adds
//!   `id_Q` to `I` and replies `(ssid, σ̂)` with `σ̂ ← BlindIssue(sk, Ĉ)`") and Remark
//!   "Concurrency": [`Protocol::respond`] records `id_Q` in the helper's [`IssuanceStore`] with
//!   one atomic test-and-set and runs `BlindIssue` only if that record succeeded. Nothing runs
//!   if the store fails, and on storage shared by several helper processes no identifier is
//!   issued to twice. A key at its issuance cap (the lattice backend's `Q_max`, where the paper's
//!   helper rotates its key) is refused before anything is recorded
//!   ([`Backend::check_issuance_capacity`]).
//! * **Attestations are verified at most once each**, and the attestations of a tag already
//!   counted not at all ([`Protocol::evaluate_request`]); with the feature `parallel` they are
//!   verified in parallel, in batches no wider than the rayon pool.
//! * **`Unblind` fails closed**: it verifies the credential it is about to return.
//! * **No restart loops.** `Register` samples one key and `PrepareIssue` one `τ`, and a `⊥` ends
//!   the call (`RegisterFailed`, `CredentialRequestFailed`), as in the protocol box. A
//!   [`Protocol`] exists only for parameters that passed [`Backend::check_params`], which
//!   refuses a tag instance under which every evaluation is `⊥`.
//! * **Plain Fiat–Shamir.** The theorem of the paper assumes an online simulation-extractable
//!   NIZK; the pairing instantiation compiles its sigma protocols with plain Fiat–Shamir
//!   (extraction by rewinding).

use core::fmt;
use std::collections::BTreeMap;

use ark_std::rand::{CryptoRng, RngCore};
use zeroize::Zeroize;

use super::{
    backend::{AttestationStatement, Backend, IssuanceStatement},
    types::{
        Attestation, AttestationRequest, Credential, CredentialRequest, Decision, EvaluatedRequest,
        Helper, HelperKey, IssuanceRecord, IssuanceState, IssuanceStore, MembershipProof, Policy,
        PublicParameters, Reply, User,
    },
};
use crate::{error::Error, serialization};

/// The public parameters `pp` and the algorithms of `Π_PCreds` for the instantiation `Bk`.
///
/// A value of this type exists only for parameters that passed the checks of `Setup`
/// ([`Backend::check_params`]); it carries the digest of `pp` that leads every proof context.
pub struct Protocol<Bk: Backend> {
    pub(super) pp: PublicParameters<Bk>,
    pub(super) digest: [u8; 32],
}

impl<Bk: Backend> Clone for Protocol<Bk> {
    fn clone(&self) -> Self {
        Self {
            pp: self.pp.clone(),
            digest: self.digest,
        }
    }
}

impl<Bk: Backend> fmt::Debug for Protocol<Bk> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Protocol")
            .field("backend", &Bk::name())
            .field("label", &String::from_utf8_lossy(&self.pp.label))
            .field("digest", &self.digest)
            .finish_non_exhaustive()
    }
}

/// An attestation request that its addressee has checked and retained (protocol box,
/// `AttestationRequest` step (ii)): `(ssid, P̃, id_Q)` with a verified `π_id`, under one helper
/// key. Built only by [`Protocol::receive_attestation_request`]; [`Protocol::attest`] answers it
/// and consumes it ("retrieve the pending request"; "pending state is consumed on completion").
///
/// Implementation note: deliberately neither decodable nor `Clone`, like [`EvaluatedRequest`].
/// An attester that answers later keeps the [`AttestationRequest`] and receives it again.
pub struct PendingAttestation<Bk: Backend> {
    ssid: Vec<u8>,
    contact: Vec<u8>,
    id: Bk::Tag,
    digest: [u8; 32],
    helper: [u8; 32],
}

impl<Bk: Backend> PendingAttestation<Bk> {
    /// The sub-session `ssid` of the request.
    #[must_use]
    pub fn ssid(&self) -> &[u8] {
        &self.ssid
    }

    /// The contact name `P̃` through which the request arrived.
    #[must_use]
    pub fn contact(&self) -> &[u8] {
        &self.contact
    }

    /// The requester's identifier `id_Q`, whose ownership `π_id` proved.
    #[must_use]
    pub fn id(&self) -> &Bk::Tag {
        &self.id
    }

    /// The fingerprint of the helper key under which `π_id` was checked
    /// ([`HelperKey::fingerprint`]).
    #[must_use]
    pub fn helper_fingerprint(&self) -> &[u8; 32] {
        &self.helper
    }
}

impl<Bk: Backend> fmt::Debug for PendingAttestation<Bk> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PendingAttestation")
            .field("ssid", &self.ssid)
            .field("contact", &self.contact)
            .field("id", &self.id)
            .finish_non_exhaustive()
    }
}

// ---------------------------------------------------------------------------------------------
// Setup
// ---------------------------------------------------------------------------------------------

impl<Bk: Backend> Protocol<Bk> {
    /// `Setup` for the deployment `label`, without any check.
    fn derive_parameters(label: &[u8]) -> Result<PublicParameters<Bk>, Error> {
        Ok(PublicParameters {
            label: label.to_vec(),
            params: Bk::setup(label)?,
        })
    }

    /// The checks every constructor runs, then the digest of `pp`.
    fn assemble(pp: PublicParameters<Bk>) -> Result<Self, Error> {
        Bk::check_params(&pp.params)?;
        let digest = pp.digest()?;
        Ok(Self { pp, digest })
    }

    /// `Setup`: `pp = (pp_Σ, H_id, H_req, H_1)` for the deployment `label`. Transparent: every
    /// parameter is derived from the label, and the oracles are fixed functions of it.
    ///
    /// # Errors
    /// The errors of [`Backend::setup`] and [`Backend::check_params`].
    pub fn setup(label: &[u8]) -> Result<Self, Error> {
        Self::assemble(Self::derive_parameters(label)?)
    }

    /// `Setup` with parameters of the instantiation that are NOT the ones [`Backend::setup`]
    /// derives from the label, e.g. the IETF-compatible generators of `Σ-BBS`, which depend on
    /// the helper's key and therefore exist only after it. The parameters enter the digest of
    /// `pp`, so every proof and every oracle `H_id`, `H_req` is bound to them.
    ///
    /// WARNING: the soundness of a base rests on how its parameters were generated (whoever
    /// knows a discrete-logarithm relation among the generators of `Σ-BBS` shows credentials it
    /// does not have). Pass only parameters that are transparently derived and that YOU
    /// computed; for received parameters use [`Self::from_public_parameters_with_params`].
    ///
    /// # Errors
    /// The errors of [`Backend::check_params`].
    pub fn setup_with_params(label: &[u8], params: Bk::Params) -> Result<Self, Error> {
        Self::assemble(PublicParameters {
            label: label.to_vec(),
            params,
        })
    }

    /// Rebuilds the protocol from RECEIVED public parameters. `Setup` is transparent, so a
    /// received `pp` is accepted only if it passes the checks of `Setup` AND equals what `Setup`
    /// derives from the label it carries. Parameters that are merely well formed are not good
    /// enough: generators with a known discrete-logarithm relation look like any others.
    ///
    /// # Errors
    /// [`Error::InvalidPublicParameters`] if the parameters are not the derived ones; the errors
    /// of `Setup`.
    pub fn from_public_parameters(pp: PublicParameters<Bk>) -> Result<Self, Error> {
        let derived = Self::derive_parameters(&pp.label)?;
        if pp.params != derived.params {
            return Err(Error::InvalidPublicParameters(
                "the parameters are not derived from the label",
            ));
        }
        Self::assemble(pp)
    }

    /// [`Self::from_public_parameters`] for a deployment that was set up with
    /// [`Self::setup_with_params`]: the received `pp` is accepted only if its parameters equal
    /// `expected`, which the caller derived on its own (for `Σ-BBS` in its IETF form: from the
    /// helper's key and the header).
    ///
    /// # Errors
    /// As [`Self::from_public_parameters`].
    pub fn from_public_parameters_with_params(
        pp: PublicParameters<Bk>,
        expected: &Bk::Params,
    ) -> Result<Self, Error> {
        if &pp.params != expected {
            return Err(Error::InvalidPublicParameters(
                "the parameters are not the expected ones",
            ));
        }
        Self::assemble(pp)
    }

    /// The public parameters `pp`, e.g. to publish them ([`Self::from_public_parameters`] is the
    /// way back).
    #[must_use]
    pub fn public_parameters(&self) -> &PublicParameters<Bk> {
        &self.pp
    }

    /// The deployment label.
    #[must_use]
    pub fn label(&self) -> &[u8] {
        &self.pp.label
    }

    /// The parameters of the instantiation: `pp_Σ` and `pp_Tag`.
    #[must_use]
    pub fn params(&self) -> &Bk::Params {
        &self.pp.params
    }

    /// The digest of `pp` that leads every proof context.
    #[must_use]
    pub fn parameters_digest(&self) -> &[u8; 32] {
        &self.digest
    }
}

// ---------------------------------------------------------------------------------------------
// The helper's key, users
// ---------------------------------------------------------------------------------------------

impl<Bk: Backend> Protocol<Bk> {
    /// The [`HelperKey`] of `vk` under this deployment, with its identifier point
    /// `x_0 = H_id(⟨hvk⟩)` and its fingerprint, WITHOUT the check `hvk ∈ V_pp`.
    fn key_of(&self, vk: Bk::VerificationKey) -> Result<HelperKey<Bk>, Error> {
        let x0 = self.identifier_point(&vk)?;
        let fingerprint = self.helper_fingerprint(&vk)?;
        Ok(HelperKey {
            vk,
            digest: self.digest,
            x0,
            fingerprint,
        })
    }

    /// Helper: `(hvk, sk) ← KeyGen(pp)` and `I ← ∅`, under the policy `Pol_k`.
    ///
    /// # Panics
    /// If the backend cannot serialize the verification key it has just generated (a broken
    /// backend; the backends of this crate always can).
    pub fn helper_keygen<R: RngCore + CryptoRng + ?Sized>(
        &self,
        policy: Policy,
        rng: &mut R,
    ) -> Helper<Bk> {
        self.helper_keygen_with_store(policy, IssuanceRecord::new(), rng)
    }

    /// [`Self::helper_keygen`] with the set `I` kept in `store`.
    ///
    /// # Panics
    /// As [`Self::helper_keygen`].
    pub fn helper_keygen_with_store<S: IssuanceStore, R: RngCore + CryptoRng + ?Sized>(
        &self,
        policy: Policy,
        store: S,
        rng: &mut R,
    ) -> Helper<Bk, S> {
        let (vk, mut sk) = Bk::keygen(&self.pp.params, rng);
        match self.key_of(vk) {
            // From here on `sk` is owned by the helper, which wipes it on drop.
            Ok(key) => Helper {
                key,
                sk,
                policy,
                store,
            },
            Err(e) => {
                sk.zeroize();
                panic!("the backend cannot serialize the key it generated: {e}")
            }
        }
    }

    /// Restores a helper from the encoding of its key ([`Helper::to_bytes`]), its policy and its
    /// store. Accepted only for a key of THIS deployment, an admissible `hvk`, and an `sk` that
    /// belongs to it.
    ///
    /// # Errors
    /// [`Error::Serialization`] or [`Error::TrailingBytes`] for a malformed encoding;
    /// [`Error::InvalidKey`] for a key of another deployment, an inadmissible `hvk`, or an `sk`
    /// that does not belong to it.
    pub fn restore_helper<S: IssuanceStore>(
        &self,
        bytes: &[u8],
        policy: Policy,
        store: S,
    ) -> Result<Helper<Bk, S>, Error> {
        use ark_serialize::CanonicalDeserialize;
        let mut reader = bytes;
        let digest = <[u8; 32]>::deserialize_compressed(&mut reader)?;
        let vk = Bk::VerificationKey::deserialize_compressed(&mut reader)?;
        let mut sk = Bk::SigningKey::deserialize_compressed(&mut reader)?;
        if !reader.is_empty() {
            sk.zeroize();
            return Err(Error::TrailingBytes);
        }
        if digest != self.digest {
            sk.zeroize();
            return Err(Error::InvalidKey);
        }
        self.checked_helper(vk, sk, policy, store)
    }

    /// A helper from a key pair that exists BEFORE the public parameters of this deployment,
    /// e.g. the key of a `Σ-BBS` deployment with IETF-compatible generators, whose parameters
    /// depend on the key ([`crate::pcreds::pairing::ietf`]). Accepted only for an admissible
    /// `hvk` and an `sk` that belongs to it; the helper is bound to THIS deployment from now on.
    /// Use one key pair per deployment.
    ///
    /// # Errors
    /// [`Error::InvalidGroupElement`] or [`Error::InvalidKey`] for an inadmissible `hvk`;
    /// [`Error::InvalidKey`] for an `sk` that does not belong to it. The key is wiped then.
    pub fn helper_from_key_pair<S: IssuanceStore>(
        &self,
        vk: Bk::VerificationKey,
        sk: Bk::SigningKey,
        policy: Policy,
        store: S,
    ) -> Result<Helper<Bk, S>, Error> {
        self.checked_helper(vk, sk, policy, store)
    }

    /// The checks of a helper key that this deployment did not generate: `hvk ∈ V_pp` and `sk`
    /// belongs to `hvk`; then the helper, bound to this deployment. `sk` is wiped on every
    /// failure.
    fn checked_helper<S>(
        &self,
        vk: Bk::VerificationKey,
        mut sk: Bk::SigningKey,
        policy: Policy,
        store: S,
    ) -> Result<Helper<Bk, S>, Error> {
        let checked = Bk::check_key(&self.pp.params, &vk).and_then(|()| {
            if Bk::key_pair_matches(&self.pp.params, &vk, &sk) {
                Ok(())
            } else {
                Err(Error::InvalidKey)
            }
        });
        let key = match checked.and_then(|()| self.key_of(vk)) {
            Ok(key) => key,
            Err(e) => {
                sk.zeroize();
                return Err(e);
            }
        };
        Ok(Helper {
            key,
            sk,
            policy,
            store,
        })
    }

    /// Checks a received helper key, `hvk ∈ V_pp` ("users return `⊥` if `hvk ∉ V_pp`"), once,
    /// and derives its identifier point `x_0 = H_id(⟨hvk⟩)` ("all parties derive `x_0`").
    ///
    /// # Errors
    /// [`Error::InvalidGroupElement`] if `vk` is not well formed; [`Error::InvalidKey`] if it is
    /// not admissible; [`Error::Serialization`] if it cannot be serialized.
    pub fn helper_key(&self, vk: &Bk::VerificationKey) -> Result<HelperKey<Bk>, Error> {
        Bk::check_key(&self.pp.params, vk)?;
        self.key_of(vk.clone())
    }

    /// [`Error::InvalidKey`] unless `hvk` was checked under this deployment.
    fn check_helper_key(&self, hvk: &HelperKey<Bk>) -> Result<(), Error> {
        if hvk.digest == self.digest {
            Ok(())
        } else {
            Err(Error::InvalidKey)
        }
    }

    /// `Register` with the helper key `hvk`, for a user with no key yet: one sample
    /// `usk ← TagKeyGen(1^λ)`, then `id = Tag(usk, x_0)` at the key's identifier point
    /// `x_0 = H_id(⟨hvk⟩)`. "If `id_P = ⊥`, return `(RegisterFailed, ⊥)`": no new key is drawn.
    ///
    /// # Errors
    /// [`Error::InvalidKey`] for a key of another deployment; [`Error::UndefinedTag`] for
    /// `RegisterFailed`, when `Tag(usk, x_0) = ⊥` (only `Tag_DY` has such points: `usk = −x_0`,
    /// with probability `1/p`); the key is wiped then.
    pub fn register<R: RngCore + CryptoRng + ?Sized>(
        &self,
        hvk: &HelperKey<Bk>,
        rng: &mut R,
    ) -> Result<User<Bk>, Error> {
        self.check_helper_key(hvk)?;
        let usk = Bk::tag_keygen(&self.pp.params, rng);
        self.user(hvk, usk)
    }

    /// `Register` with the helper key `hvk` for a user registered with another helper key of
    /// this deployment: "Reuse `usk_P` if previously sampled by `TagKeyGen` under the same tag
    /// parameters". The identifier is another one: "each helper key determines its own
    /// identifier point".
    ///
    /// # Errors
    /// [`Error::InvalidKey`] for a key of another deployment; [`Error::IdentifierMismatch`] for
    /// a user of another deployment; [`Error::UndefinedTag`] for `RegisterFailed`
    /// (`Tag(usk, x_0) = ⊥`).
    pub fn register_reusing(
        &self,
        hvk: &HelperKey<Bk>,
        user: &User<Bk>,
    ) -> Result<User<Bk>, Error> {
        self.check_helper_key(hvk)?;
        if user.digest != self.digest {
            return Err(Error::IdentifierMismatch);
        }
        self.user(hvk, user.usk.clone())
    }

    /// The user with the GIVEN key under the helper key `hvk`, e.g. a key derived from a seed:
    /// `id = Tag(usk, x_0)` at `x_0 = H_id(⟨hvk⟩)`.
    ///
    /// # Errors
    /// [`Error::InvalidKey`] for a key of another deployment; [`Error::UndefinedTag`] if
    /// `Tag(usk, x_0) = ⊥`. The key is wiped on every error.
    pub fn user(&self, hvk: &HelperKey<Bk>, mut usk: Bk::UserKey) -> Result<User<Bk>, Error> {
        if let Err(e) = self.check_helper_key(hvk) {
            usk.zeroize();
            return Err(e);
        }
        match Bk::tag(&self.pp.params, &usk, &hvk.x0) {
            Some(id) => Ok(User {
                usk,
                id,
                digest: self.digest,
                helper: hvk.fingerprint,
            }),
            None => {
                usk.zeroize();
                Err(Error::UndefinedTag)
            }
        }
    }

    /// Checks a user read back from storage: it belongs to this deployment and to the helper key
    /// `hvk`, and its identifier is `Tag(usk, x_0)` at the key's identifier point.
    ///
    /// # Errors
    /// [`Error::InvalidKey`] for a key of another deployment; [`Error::IdentifierMismatch`]
    /// otherwise.
    pub fn check_user(&self, hvk: &HelperKey<Bk>, user: &User<Bk>) -> Result<(), Error> {
        self.check_helper_key(hvk)?;
        self.owns(hvk, user)?;
        if Bk::tag(&self.pp.params, &user.usk, &hvk.x0).as_ref() == Some(&user.id) {
            Ok(())
        } else {
            Err(Error::IdentifierMismatch)
        }
    }

    /// [`Error::IdentifierMismatch`] unless `user` belongs to this deployment and registered with
    /// the helper key `hvk`.
    fn owns(&self, hvk: &HelperKey<Bk>, user: &User<Bk>) -> Result<(), Error> {
        if user.digest == self.digest && user.helper == hvk.fingerprint {
            Ok(())
        } else {
            Err(Error::IdentifierMismatch)
        }
    }
}

// ---------------------------------------------------------------------------------------------
// AttestationRequest and AttestationRequestResponse
// ---------------------------------------------------------------------------------------------

impl<Bk: Backend> Protocol<Bk> {
    /// Requester `Q`:
    /// `π_id ← NIZKProve_{R_Tag^ctx}(((id_Q, x_0), (ssid, P̃)), usk_Q)` at the identifier point
    /// `x_0` of `hvk`, the message `(id_Q, π_id)` for the owner of the contact name `P̃`
    /// (`contact`).
    ///
    /// # Errors
    /// [`Error::InvalidKey`] for a key of another deployment; [`Error::IdentifierMismatch`] for
    /// a user of another deployment or helper key; the errors of the proof.
    pub fn request_attestation<R: RngCore + CryptoRng + ?Sized>(
        &self,
        hvk: &HelperKey<Bk>,
        user: &User<Bk>,
        ssid: &[u8],
        contact: &[u8],
        rng: &mut R,
    ) -> Result<AttestationRequest<Bk>, Error> {
        self.check_helper_key(hvk)?;
        self.owns(hvk, user)?;
        let ctx = self.identifier_context(ssid, contact);
        let proof = Bk::prove_tag(&self.pp.params, &user.id, &hvk.x0, &user.usk, &ctx, rng)?;
        Ok(AttestationRequest {
            id: user.id.clone(),
            proof,
        })
    }

    /// The owner `P` of the contact name `P̃`, on an attestation request under the helper key
    /// `hvk`: checks `id_Q ∈ T` and `π_id` for `(id_Q, x_0)` under the context `(ssid, P̃)`, and
    /// retains the request.
    ///
    /// # Errors
    /// [`Error::InvalidKey`] for a key of another deployment; [`Error::InvalidGroupElement`] or
    /// [`Error::InvalidTag`] for an inadmissible `id_Q`; [`Error::InvalidProof`] if `π_id` does
    /// not verify.
    pub fn receive_attestation_request(
        &self,
        hvk: &HelperKey<Bk>,
        request: &AttestationRequest<Bk>,
        ssid: &[u8],
        contact: &[u8],
    ) -> Result<PendingAttestation<Bk>, Error> {
        self.check_helper_key(hvk)?;
        Bk::check_tag(&self.pp.params, &request.id, &hvk.x0, "id_Q")?;
        let ctx = self.identifier_context(ssid, contact);
        Bk::check_tag_proof(&self.pp.params, &request.id, &hvk.x0, &ctx, &request.proof)?;
        Ok(PendingAttestation {
            ssid: ssid.to_vec(),
            contact: contact.to_vec(),
            id: request.id.clone(),
            digest: self.digest,
            helper: hvk.fingerprint,
        })
    }

    /// Whether `request` is a valid attestation request under `(ssid, P̃)` and the helper key
    /// `hvk`.
    #[must_use]
    pub fn verify_attestation_request(
        &self,
        hvk: &HelperKey<Bk>,
        request: &AttestationRequest<Bk>,
        ssid: &[u8],
        contact: &[u8],
    ) -> bool {
        self.receive_attestation_request(hvk, request, ssid, contact)
            .is_ok()
    }

    /// Attester `P`, answering a pending request, which it consumes: `t_{P→Q} = Tag(usk_P, x_Q)`,
    /// `σ* = ReRand(hvk, usk_P, σ_P; ω)` and `π_att`.
    ///
    /// The attester holds the credential `cred` (protocol box: "check that it holds a
    /// credential"); a credential that does not belong to `(attester, hvk)` makes the prover
    /// refuse or yields an attestation that no verifier accepts.
    ///
    /// # Errors
    /// [`Error::InvalidKey`] for a key of another deployment; [`Error::IdentifierMismatch`] for
    /// an attester of another deployment or helper key, or a pending request received under
    /// another one; [`Error::UndefinedTag`] if `Tag(usk_P, x_Q) = ⊥` (`Tag_DY`:
    /// `usk_P = −x_Q`); the errors of the proof. The pending request is consumed in every case.
    pub fn attest<R: RngCore + CryptoRng + ?Sized>(
        &self,
        hvk: &HelperKey<Bk>,
        attester: &User<Bk>,
        cred: &Credential<Bk>,
        pending: PendingAttestation<Bk>,
        rng: &mut R,
    ) -> Result<Attestation<Bk>, Error> {
        self.attest_at(hvk, attester, cred, pending, None, rng)
    }

    /// [`Self::attest`] under the application context `app` (implementation note for OpenVTC,
    /// not in the paper): `π_att` is bound to `app` ([`Self::attestation_context_in`]), so the
    /// attestation verifies under `app` only ([`Self::check_attestation_in_context`]). Its tag
    /// does not depend on `app`: one attester counts once for a recipient, whatever contexts
    /// its attestations carry.
    ///
    /// # Errors
    /// Those of [`Self::attest`].
    pub fn attest_in_context<R: RngCore + CryptoRng + ?Sized>(
        &self,
        hvk: &HelperKey<Bk>,
        attester: &User<Bk>,
        cred: &Credential<Bk>,
        pending: PendingAttestation<Bk>,
        app: &[u8],
        rng: &mut R,
    ) -> Result<Attestation<Bk>, Error> {
        self.attest_at(hvk, attester, cred, pending, Some(app), rng)
    }

    /// [`Self::attest`] under the application context `app`, if any.
    fn attest_at<R: RngCore + CryptoRng + ?Sized>(
        &self,
        hvk: &HelperKey<Bk>,
        attester: &User<Bk>,
        cred: &Credential<Bk>,
        pending: PendingAttestation<Bk>,
        app: Option<&[u8]>,
        rng: &mut R,
    ) -> Result<Attestation<Bk>, Error> {
        self.check_helper_key(hvk)?;
        self.owns(hvk, attester)?;
        if pending.digest != self.digest || pending.helper != hvk.fingerprint {
            return Err(Error::IdentifierMismatch);
        }
        let xq = self.recipient_point_at(&hvk.vk, &hvk.x0, &pending.id)?;
        let tag = Bk::tag(&self.pp.params, &attester.usk, &xq).ok_or(Error::UndefinedTag)?;
        let ctx = self.attestation_context_in(&hvk.vk, app)?;
        let statement = AttestationStatement {
            vk: &hvk.vk,
            tag: &tag,
            point: &xq,
        };
        let (show, proof) = Bk::prove_attestation(
            &self.pp.params,
            &statement,
            &attester.usk,
            &cred.inner,
            &ctx,
            rng,
        )?;
        Ok(Attestation { tag, show, proof })
    }

    /// Recipient `Q` (and helper): the check of an attestation for `id_Q`, with the reason for a
    /// rejection: `id_Q ∈ T`, `t ∈ T`, the public checks of `R_Possess` on `σ*`, and `π_att` at
    /// the recipient point `x_Q`. A function of public data; never panics.
    ///
    /// # Errors
    /// [`Error::InvalidKey`] for a key of another deployment; [`Error::InvalidGroupElement`] or
    /// [`Error::InvalidTag`] for an inadmissible identifier or tag; [`Error::InvalidCredential`]
    /// if `σ*` fails the public checks; [`Error::InvalidProof`] if `π_att` does not verify.
    pub fn check_attestation(
        &self,
        hvk: &HelperKey<Bk>,
        id_q: &Bk::Tag,
        att: &Attestation<Bk>,
    ) -> Result<(), Error> {
        self.check_attestation_for(hvk, id_q, att, None)
    }

    /// [`Self::check_attestation`] under the application context `app` (implementation note for
    /// OpenVTC, not in the paper), which the verifier takes from its own copy of the public
    /// data: an attestation made under another context, or under none, is refused.
    ///
    /// # Errors
    /// Those of [`Self::check_attestation`].
    pub fn check_attestation_in_context(
        &self,
        hvk: &HelperKey<Bk>,
        id_q: &Bk::Tag,
        att: &Attestation<Bk>,
        app: &[u8],
    ) -> Result<(), Error> {
        self.check_attestation_for(hvk, id_q, att, Some(app))
    }

    /// Whether `att` is a valid attestation for `id_Q` ([`Self::check_attestation`]).
    #[must_use]
    pub fn verify_attestation(
        &self,
        hvk: &HelperKey<Bk>,
        id_q: &Bk::Tag,
        att: &Attestation<Bk>,
    ) -> bool {
        self.check_attestation(hvk, id_q, att).is_ok()
    }

    /// Whether `att` is a valid attestation for `id_Q` under the application context `app`
    /// ([`Self::check_attestation_in_context`]).
    #[must_use]
    pub fn verify_attestation_in_context(
        &self,
        hvk: &HelperKey<Bk>,
        id_q: &Bk::Tag,
        att: &Attestation<Bk>,
        app: &[u8],
    ) -> bool {
        self.check_attestation_in_context(hvk, id_q, att, app)
            .is_ok()
    }

    /// [`Self::check_attestation`] under the application context `app`, if any.
    fn check_attestation_for(
        &self,
        hvk: &HelperKey<Bk>,
        id_q: &Bk::Tag,
        att: &Attestation<Bk>,
        app: Option<&[u8]>,
    ) -> Result<(), Error> {
        self.check_helper_key(hvk)?;
        Bk::check_tag(&self.pp.params, id_q, &hvk.x0, "id_Q")?;
        let xq = self.recipient_point_at(&hvk.vk, &hvk.x0, id_q)?;
        self.check_attestation_at(&hvk.vk, &xq, att, app)
    }

    /// The check of an attestation at the recipient point `x_Q`, for a checked key, under the
    /// application context `app`, if any.
    fn check_attestation_at(
        &self,
        vk: &Bk::VerificationKey,
        xq: &Bk::Point,
        att: &Attestation<Bk>,
        app: Option<&[u8]>,
    ) -> Result<(), Error> {
        Bk::check_tag(&self.pp.params, &att.tag, xq, "t")?;
        let ctx = self.attestation_context_in(vk, app)?;
        let statement = AttestationStatement {
            vk,
            tag: &att.tag,
            point: xq,
        };
        Bk::check_attestation_proof(&self.pp.params, &statement, &att.show, &ctx, &att.proof)
    }

    /// `N''` of [`Self::evaluate_request`]: the distinct tags of the valid attestations at
    /// `x_Q`, in the order of the attestations that made them count, verifying each attestation
    /// at most once and none of a tag already counted, the `i`-th under the application context
    /// `apps[i]` if there are contexts (one per attestation).
    fn valid_distinct_tags(
        &self,
        vk: &Bk::VerificationKey,
        xq: &Bk::Point,
        attestations: &[Attestation<Bk>],
        apps: Option<&[&[u8]]>,
    ) -> Result<Vec<Bk::Tag>, Error> {
        // the attestations of each distinct tag (by its encoding), in their order
        let mut groups: Vec<Vec<usize>> = Vec::new();
        let mut by_tag: BTreeMap<Vec<u8>, usize> = BTreeMap::new();
        for (i, att) in attestations.iter().enumerate() {
            let encoded = serialization::to_bytes(&att.tag)?;
            let group = *by_tag.entry(encoded).or_insert_with(|| {
                groups.push(Vec::new());
                groups.len() - 1
            });
            groups[group].push(i);
        }
        // rounds: the next untried attestation of every tag that has not counted yet
        let mut next = vec![0usize; groups.len()];
        let mut counted: Vec<Option<usize>> = vec![None; groups.len()];
        loop {
            let round: Vec<(usize, usize)> = groups
                .iter()
                .enumerate()
                .filter(|&(group, _)| counted[group].is_none())
                .filter_map(|(group, members)| members.get(next[group]).map(|&i| (group, i)))
                .collect();
            if round.is_empty() {
                break;
            }
            let verdicts = self.verify_round(vk, xq, attestations, apps, &round);
            for (&(group, i), valid) in round.iter().zip(verdicts) {
                if valid {
                    counted[group] = Some(i);
                } else {
                    next[group] += 1;
                }
            }
        }
        let mut found: Vec<usize> = counted.into_iter().flatten().collect();
        found.sort_unstable();
        Ok(found
            .into_iter()
            .map(|i| attestations[i].tag.clone())
            .collect())
    }

    /// The verdicts of one round of [`Self::valid_distinct_tags`], one after the other.
    #[cfg(not(feature = "parallel"))]
    fn verify_round(
        &self,
        vk: &Bk::VerificationKey,
        xq: &Bk::Point,
        attestations: &[Attestation<Bk>],
        apps: Option<&[&[u8]]>,
        round: &[(usize, usize)],
    ) -> Vec<bool> {
        round
            .iter()
            .map(|&(_, i)| {
                let app = apps.map(|apps| apps[i]);
                self.check_attestation_at(vk, xq, &attestations[i], app)
                    .is_ok()
            })
            .collect()
    }

    /// The verdicts of one round of [`Self::valid_distinct_tags`], on the rayon pool of the
    /// calling thread (the global pool, unless the call runs inside `ThreadPool::install`), in
    /// batches of the pool's width `n`: a batch holds at most `n` verifications, so at most `n`
    /// run at once. One parallel iterator over the whole round would not respect this bound:
    /// rayon lets a thread that waits inside one verification (Jali is parallel too) start
    /// another.
    #[cfg(feature = "parallel")]
    fn verify_round(
        &self,
        vk: &Bk::VerificationKey,
        xq: &Bk::Point,
        attestations: &[Attestation<Bk>],
        apps: Option<&[&[u8]]>,
        round: &[(usize, usize)],
    ) -> Vec<bool> {
        use rayon::prelude::*;
        let width = rayon::current_num_threads().max(1);
        round
            .chunks(width)
            .flat_map(|batch| {
                batch
                    .par_iter()
                    .map(|&(_, i)| {
                        let app = apps.map(|apps| apps[i]);
                        self.check_attestation_at(vk, xq, &attestations[i], app)
                            .is_ok()
                    })
                    .collect::<Vec<_>>()
            })
            .collect()
    }
}

// ---------------------------------------------------------------------------------------------
// CredentialRequest and CredentialRequestResponse
// ---------------------------------------------------------------------------------------------

impl<Bk: Backend> Protocol<Bk> {
    /// Requester `Q`: `Ĉ = PrepareIssue(hvk, usk_Q; τ)` on one fresh `τ`, and
    /// `π_iss ← NIZKProve_{R_iss^ctx}(((hvk, Ĉ, id_Q), (ssid, att⃗)), (usk_Q, τ))`, for the
    /// attestations the requester selected (protocol box: "every tag in `N'` names a stored
    /// attestation"). Returns the message for the helper and the state for [`Self::unblind`].
    ///
    /// # Errors
    /// [`Error::InvalidKey`] for a key of another deployment; [`Error::IdentifierMismatch`] for
    /// a user of another deployment or helper key; [`Error::InvalidIssuanceEncoding`] for
    /// `CredentialRequestFailed`, when `PrepareIssue` gives `⊥` (it is not retried); the errors
    /// of the proof.
    pub fn request_credential<R: RngCore + CryptoRng + ?Sized>(
        &self,
        hvk: &HelperKey<Bk>,
        user: &User<Bk>,
        attestations: Vec<Attestation<Bk>>,
        ssid: &[u8],
        rng: &mut R,
    ) -> Result<(CredentialRequest<Bk>, IssuanceState<Bk>), Error> {
        self.request_credential_at(hvk, user, attestations, ssid, None, None, rng)
    }

    /// [`Self::request_credential`] with application contexts (implementation note for OpenVTC,
    /// not in the paper): `π_iss` is also bound to the context `att_apps[j]` of each attestation,
    /// one per attestation and in their order, and to the request's own context `app`
    /// ([`Self::issuance_context_in`]). The helper evaluates the request under the same contexts
    /// ([`Self::evaluate_request_in_context`]), which it takes from its own copy of the public
    /// data.
    ///
    /// # Errors
    /// [`Error::LengthMismatch`] if `att_apps` does not hold one context per attestation, and
    /// those of [`Self::request_credential`].
    #[allow(clippy::too_many_arguments)]
    pub fn request_credential_in_context<R: RngCore + CryptoRng + ?Sized>(
        &self,
        hvk: &HelperKey<Bk>,
        user: &User<Bk>,
        attestations: Vec<Attestation<Bk>>,
        att_apps: &[&[u8]],
        ssid: &[u8],
        app: &[u8],
        rng: &mut R,
    ) -> Result<(CredentialRequest<Bk>, IssuanceState<Bk>), Error> {
        self.request_credential_at(
            hvk,
            user,
            attestations,
            ssid,
            Some(att_apps),
            Some(app),
            rng,
        )
    }

    /// [`Self::request_credential`] under the application contexts `att_apps` and `app`, if any.
    #[allow(clippy::too_many_arguments)]
    fn request_credential_at<R: RngCore + CryptoRng + ?Sized>(
        &self,
        hvk: &HelperKey<Bk>,
        user: &User<Bk>,
        attestations: Vec<Attestation<Bk>>,
        ssid: &[u8],
        att_apps: Option<&[&[u8]]>,
        app: Option<&[u8]>,
        rng: &mut R,
    ) -> Result<(CredentialRequest<Bk>, IssuanceState<Bk>), Error> {
        self.check_helper_key(hvk)?;
        self.owns(hvk, user)?;
        let (request, tau) = Bk::prepare_issue(&self.pp.params, &hvk.vk, &user.usk, rng)?;
        // From here on τ is owned by the state, which wipes it on every exit.
        let state = IssuanceState {
            tau,
            owner: user.id.clone(),
            digest: self.digest,
        };
        let ctx = self.issuance_context_in(&hvk.vk, ssid, &attestations, att_apps, app)?;
        let statement = IssuanceStatement {
            vk: &hvk.vk,
            request: &request,
            id: &user.id,
            x0: &hvk.x0,
        };
        let proof = Bk::prove_issuance(
            &self.pp.params,
            &statement,
            &user.usk,
            &state.tau,
            &ctx,
            rng,
        )?;
        Ok((
            CredentialRequest {
                id: user.id.clone(),
                attestations,
                request,
                proof,
            },
            state,
        ))
    }

    /// Helper, on a credential request: checks `id_Q ∈ T` and `π_iss` for `(hvk, Ĉ, id_Q)` under
    /// `(ssid, att⃗)`, with the tag clause at the identifier point `x_0` of its key, retains
    /// `(ssid, id_Q, Ĉ)`, and computes the set `N''` of the distinct tags of the valid
    /// attestations at `x_Q` and the policy value `v = [|N''| ≥ k]` (protocol box, the helper's
    /// steps (i) and (ii)).
    ///
    /// Each attestation is verified at most once, and one whose tag is already in `N''` is not
    /// verified at all: the attestations of a tag are tried in their order until one verifies.
    /// `N''` lists the tags in the order of the attestations that made them count. With the
    /// feature `parallel`, each round of candidates (the next untried attestation of every tag
    /// not yet counted) is verified on the rayon pool of the calling thread, in batches no wider
    /// than the pool, so that at most as many verifications run at once as the pool has threads
    /// (a lattice attestation holds up to about 0.7 GB while it is verified); the result is the
    /// same as without the feature.
    ///
    /// # Errors
    /// [`Error::InvalidKey`] for a helper of another deployment; [`Error::TooManyAttestations`]
    /// above the helper's limit on attestations, if it set one; [`Error::InvalidGroupElement`]
    /// or [`Error::InvalidTag`] for an inadmissible `id_Q`; [`Error::InvalidIssuanceEncoding`]
    /// if `Ĉ` fails the public checks; [`Error::InvalidProof`] if `π_iss` does not verify.
    pub fn evaluate_request<S>(
        &self,
        helper: &Helper<Bk, S>,
        message: &CredentialRequest<Bk>,
        ssid: &[u8],
    ) -> Result<EvaluatedRequest<Bk>, Error> {
        self.evaluate_request_at(helper, message, ssid, None, None)
    }

    /// [`Self::evaluate_request`] under application contexts (implementation note for OpenVTC,
    /// not in the paper), which the helper takes from its own copy of the public data, never
    /// from the requester: `π_iss` under `att_apps` and `app`
    /// ([`Self::issuance_context_in`]), and each attestation under its own context
    /// `att_apps[j]` ([`Self::check_attestation_in_context`]). An attestation made under
    /// another context does not count, and a request proved under other contexts is refused.
    ///
    /// # Errors
    /// [`Error::LengthMismatch`] if `att_apps` does not hold one context per attestation, and
    /// those of [`Self::evaluate_request`].
    pub fn evaluate_request_in_context<S>(
        &self,
        helper: &Helper<Bk, S>,
        message: &CredentialRequest<Bk>,
        ssid: &[u8],
        att_apps: &[&[u8]],
        app: &[u8],
    ) -> Result<EvaluatedRequest<Bk>, Error> {
        self.evaluate_request_at(helper, message, ssid, Some(att_apps), Some(app))
    }

    /// [`Self::evaluate_request`] under the application contexts `att_apps` and `app`, if any.
    fn evaluate_request_at<S>(
        &self,
        helper: &Helper<Bk, S>,
        message: &CredentialRequest<Bk>,
        ssid: &[u8],
        att_apps: Option<&[&[u8]]>,
        app: Option<&[u8]>,
    ) -> Result<EvaluatedRequest<Bk>, Error> {
        let key = &helper.key;
        self.check_helper_key(key)?;
        if let Some(max) = helper.policy.max_attestations()
            && message.attestations.len() > max
        {
            return Err(Error::TooManyAttestations {
                max,
                actual: message.attestations.len(),
            });
        }
        // (i) id_Q ∈ T and π_iss under (ssid, att⃗)
        Bk::check_tag(&self.pp.params, &message.id, &key.x0, "id_Q")?;
        let ctx = self.issuance_context_in(&key.vk, ssid, &message.attestations, att_apps, app)?;
        let statement = IssuanceStatement {
            vk: &key.vk,
            request: &message.request,
            id: &message.id,
            x0: &key.x0,
        };
        Bk::check_issuance_proof(&self.pp.params, &statement, &ctx, &message.proof)?;
        // (ii) N'': the distinct tags of the valid attestations at x_Q
        let xq = self.recipient_point_at(&key.vk, &key.x0, &message.id)?;
        let tags = self.valid_distinct_tags(&key.vk, &xq, &message.attestations, att_apps)?;
        let valid = helper.policy.accepts(tags.len());
        Ok(EvaluatedRequest {
            fingerprint: key.fingerprint,
            ssid: ssid.to_vec(),
            id: message.id.clone(),
            request: message.request.clone(),
            tags,
            valid,
        })
    }

    /// Helper, `CredentialRequestResponse` on its decision `d`, consuming the pending request:
    /// `Fail` if `v = invalid` and `d ≠ root`; `issued` if `id_Q ∈ I`; otherwise
    /// `I ← I ∪ {id_Q}` and the reply `σ̂` with `σ̂ ← BlindIssue(sk, Ĉ)`, in this order.
    ///
    /// Implementation notes on the order (Remark "Concurrency": "an honest helper records its
    /// first issuance to an identifier before releasing the response"). The record is one
    /// test-and-set ([`IssuanceStore::record`]), and `BlindIssue` runs only if it succeeded: if
    /// another process recorded `id_Q` since the check `id_Q ∈ I`, the reply is `issued`, and if
    /// the store fails, nothing runs. An identifier stays in `I` when `BlindIssue` fails after the
    /// record, as in the paper. A key at its issuance cap is refused before the record
    /// ([`Backend::check_issuance_capacity`]): the paper's helper rotates its key at the cap, so
    /// its old key never answers, and the identifier can still be issued to by a helper process
    /// whose copy of the key has capacity left.
    ///
    /// # Errors
    /// [`Error::InvalidKey`] for a helper of another deployment or a request evaluated by
    /// another helper; the refusal of [`Backend::check_issuance_capacity`] (the lattice backend:
    /// `Error::IssuanceCapReached`); the errors of the store; [`Error::InvalidIssuanceEncoding`]
    /// if `BlindIssue` returns `⊥`, and the other refusals of the backend's `BlindIssue`.
    pub fn respond<S: IssuanceStore, R: RngCore + CryptoRng + ?Sized>(
        &self,
        helper: &mut Helper<Bk, S>,
        request: EvaluatedRequest<Bk>,
        decision: Decision,
        rng: &mut R,
    ) -> Result<Reply<Bk>, Error> {
        self.check_helper_key(&helper.key)?;
        if request.fingerprint != helper.key.fingerprint {
            return Err(Error::InvalidKey);
        }
        if !request.valid && decision != Decision::Root {
            return Ok(Reply::Fail);
        }
        let id = serialization::to_bytes(&request.id)?;
        if helper.store.contains(&id)? {
            return Ok(Reply::Issued);
        }
        Bk::check_issuance_capacity(&helper.sk)?;
        if !helper.store.record(&id)? {
            // issued to by another process since the check above
            return Ok(Reply::Issued);
        }
        let pre = Bk::blind_issue(&self.pp.params, &helper.sk, &request.request, rng)?;
        Ok(Reply::PreCredential(pre))
    }

    /// Requester, on `σ̂`, consuming the state of its request:
    /// `σ_Q = Unblind(hvk, usk_Q, σ̂, τ)`, checked with `Verify(hvk, usk_Q, σ_Q)` (fails closed).
    ///
    /// # Errors
    /// [`Error::InvalidKey`] for a key of another deployment; [`Error::IdentifierMismatch`] for
    /// a user of another deployment or helper key; [`Error::IssuanceStateMismatch`] if `state`
    /// belongs to another user or deployment; [`Error::InvalidGroupElement`] or
    /// [`Error::InvalidPreCredential`] if unblinding or verification fails. The state is
    /// consumed (and `τ` wiped) in every case.
    pub fn unblind(
        &self,
        hvk: &HelperKey<Bk>,
        user: &User<Bk>,
        pre: &Bk::PreCredential,
        state: IssuanceState<Bk>,
    ) -> Result<Credential<Bk>, Error> {
        self.check_helper_key(hvk)?;
        self.owns(hvk, user)?;
        if state.digest != self.digest || state.owner != user.id {
            return Err(Error::IssuanceStateMismatch);
        }
        let inner = Bk::unblind(&self.pp.params, &hvk.vk, &user.usk, pre, &state.tau)?;
        Ok(Credential { inner })
    }

    /// The credential `inner` of the base, accepted only if it verifies for `(hvk, user)`.
    ///
    /// # Errors
    /// [`Error::InvalidKey`], [`Error::IdentifierMismatch`] as for [`Self::unblind`];
    /// [`Error::InvalidCredential`] if `inner` does not verify; it is wiped then.
    pub fn credential(
        &self,
        hvk: &HelperKey<Bk>,
        user: &User<Bk>,
        inner: Bk::Credential,
    ) -> Result<Credential<Bk>, Error> {
        // From here on the credential wipes itself on every exit.
        let cred = Credential { inner };
        self.check_helper_key(hvk)?;
        self.owns(hvk, user)?;
        if Bk::verify(&self.pp.params, &hvk.vk, &user.usk, &cred.inner) {
            Ok(cred)
        } else {
            Err(Error::InvalidCredential)
        }
    }

    /// `Verify(hvk, usk, σ)` of the base, for a user and key of this deployment.
    #[must_use]
    pub fn verify_credential(
        &self,
        hvk: &HelperKey<Bk>,
        user: &User<Bk>,
        cred: &Credential<Bk>,
    ) -> bool {
        self.check_helper_key(hvk).is_ok()
            && self.owns(hvk, user).is_ok()
            && Bk::verify(&self.pp.params, &hvk.vk, &user.usk, &cred.inner)
    }
}

// ---------------------------------------------------------------------------------------------
// Prove and Verify
// ---------------------------------------------------------------------------------------------

impl<Bk: Backend> Protocol<Bk> {
    /// `Prove`: `σ* = ReRand(hvk, usk_P, σ_P; ω)` and
    /// `π_prove ← NIZKProve_{R_Possess^ctx}(((hvk, σ*), m), (usk_P, σ_P, ω))`; the membership
    /// proof `π = (σ*, π_prove)` on the message `m`, to be posted anonymously.
    ///
    /// # Errors
    /// [`Error::InvalidKey`] for a key of another deployment; [`Error::IdentifierMismatch`] for
    /// a user of another deployment or helper key; the errors of the proof.
    pub fn prove<R: RngCore + CryptoRng + ?Sized>(
        &self,
        hvk: &HelperKey<Bk>,
        user: &User<Bk>,
        cred: &Credential<Bk>,
        message: &[u8],
        rng: &mut R,
    ) -> Result<MembershipProof<Bk>, Error> {
        self.check_helper_key(hvk)?;
        self.owns(hvk, user)?;
        let ctx = self.prove_context(&hvk.vk, message)?;
        let (show, proof) =
            Bk::prove_possession(&self.pp.params, &hvk.vk, &user.usk, &cred.inner, &ctx, rng)?;
        Ok(MembershipProof { show, proof })
    }

    /// `Verify` of a membership proof on `m`, with the reason for a rejection. A function of
    /// public data; never panics.
    ///
    /// # Errors
    /// [`Error::InvalidKey`] for a key of another deployment; [`Error::InvalidGroupElement`] or
    /// [`Error::InvalidCredential`] if `σ*` fails the public checks; [`Error::InvalidProof`] if
    /// `π_prove` does not verify for `m`.
    pub fn check_membership(
        &self,
        hvk: &HelperKey<Bk>,
        message: &[u8],
        proof: &MembershipProof<Bk>,
    ) -> Result<(), Error> {
        self.check_helper_key(hvk)?;
        let ctx = self.prove_context(&hvk.vk, message)?;
        Bk::check_possession_proof(&self.pp.params, &hvk.vk, &proof.show, &ctx, &proof.proof)
    }

    /// `Verify` of a membership proof on `m` ([`Self::check_membership`]).
    #[must_use]
    pub fn verify(&self, hvk: &HelperKey<Bk>, message: &[u8], proof: &MembershipProof<Bk>) -> bool {
        self.check_membership(hvk, message, proof).is_ok()
    }
}
