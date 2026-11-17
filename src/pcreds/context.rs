//! The digest of `pp`, the Fiat–Shamir contexts of the four proofs, and the oracles `H_id` and
//! `H_req`.
//!
//! | paper | here |
//! |---|---|
//! | `π_id ← NIZKProve_{R_Tag^ctx}(((id_Q, x_0), (ssid, P̃)), usk_Q)` | [`Protocol::identifier_context`] |
//! | `π_att ← NIZKProve_{R_att}(…)`, "the proof has no context" | [`Protocol::attestation_context`] |
//! | `π_iss ← NIZKProve_{R_iss^ctx}(((hvk, Ĉ, id_Q), (ssid, att⃗)), …)` | [`Protocol::issuance_context`] |
//! | `π_prove ← NIZKProve_{R_Possess^ctx}(((hvk, σ*), m), …)` | [`Protocol::prove_context`] |
//! | `x_0 = H_id(⟨hvk⟩)` | [`Protocol::identifier_point`] |
//! | `x_Q = H_req(⟨pp, hvk, id_Q, j_Q⟩)`, "`j_Q` is the least nonnegative counter for which `x_Q ≠ x_0`" | [`Protocol::recipient_point`] |
//!
//! Implementation notes (the paper gives the tuples, not their encoding):
//!
//! * **A verifier always REBUILDS its context** from the public statement and never takes one
//!   from the prover; a verifier that accepts a context supplied alongside the proof "verifies a
//!   proof bound to nothing". The functions are public because they are functions of public
//!   data, and because a test harness that plays a cheating prover needs the challenge an honest
//!   verifier will compute.
//! * The contexts and oracle inputs are [`Transcript`] digests: every component is an
//!   injectively framed item, values in their compressed canonical encoding. With the oracle
//!   suffix first:
//!
//!   | digest | oracle suffix | items |
//!   |---|---|---|
//!   | `pp` | `/PCREDS-PP` | `label`, `backend` (the name of the instantiation), `params` |
//!   | `π_id` | `/PCREDS-CTX-ID` | `pp` (the digest), `ssid`, `contact` |
//!   | `π_att` | `/PCREDS-CTX-ATT` | `pp`, `hvk`, then with an application context `app` |
//!   | `π_iss` | `/PCREDS-CTX-ISS` | `pp`, `hvk`, `ssid`, `count`, then one item `att` per attestation, then with application contexts one item `att-app` per attestation and `app` |
//!   | `π_prove` | `/PCREDS-CTX-PROVE` | `pp`, `hvk`, `message` |
//!   | `H_id` | `/PCREDS-HID` | `pp`, `hvk` |
//!   | `H_req` | `/PCREDS-HREQ` | `pp`, `hvk`, `id`, `counter` |
//! * **Application contexts (implementation note for OpenVTC, not in the paper).**
//!   [`Protocol::attestation_context_in`] and [`Protocol::issuance_context_in`] append the
//!   caller's application contexts as the last items, and without them give the paper's
//!   contexts byte for byte. The `_in_context` entry points of [`Protocol`] use them.
//! * **One oracle per proof.** The four proofs are transcripts of four different oracles, so a
//!   proof made for one role never verifies in another, whatever the statements are.
//! * **`pp` leads.** `pp` enters as its digest, computed once per instance, and it covers the
//!   deployment label and the name of the instantiation: the algebraic parameters alone do not
//!   determine the deployment (`pp_Σ` of `Σ-PS` is empty), while `H_1` has no deployment input
//!   of its own ([`crate::hash`]). In `H_id` the digest stands for the oracle being part of
//!   `pp`: the paper's input is `⟨hvk⟩` alone, under an oracle of the deployment.
//! * **The oracles map through the backend.** `H_id` and `H_req` frame their inputs here; the
//!   backend maps the transcript to a point of `X` ([`Backend::identifier_point`],
//!   [`Backend::request_point`]): a scalar for the pairing-based tags, a matrix
//!   `H_mat(label ‖ d)` under a label of its own for each oracle for `Tag_LWR`.
//! * **`hvk` is part of the statement** of `π_att`, `π_iss` and `π_prove` ("`(hvk, σ*, t, x_Q)`",
//!   "`(hvk, Ĉ, id_Q)`", "`(hvk, σ*)`"), so it enters their contexts. Fiat–Shamir absorbs every
//!   base and target of a relation ([`crate::sigma::fiat_shamir`]), but the clauses of `Σ-BBS`
//!   for `Ĉ` do not mention `vk`: without this item an issuance proof of `Σ-BBS` would not be
//!   bound to the key it was made for.

use super::{Protocol, backend::Backend, types::Attestation};
use crate::{error::Error, hash::Transcript};

/// Oracle suffix of the digest of `pp`.
pub(crate) const PP_SUFFIX: &[u8] = b"/PCREDS-PP";
/// Oracle suffix of the context of `π_id`.
const IDENTIFIER_SUFFIX: &[u8] = b"/PCREDS-CTX-ID";
/// Oracle suffix of the context of `π_att`.
const ATTESTATION_SUFFIX: &[u8] = b"/PCREDS-CTX-ATT";
/// Oracle suffix of the context of `π_iss`.
const ISSUANCE_SUFFIX: &[u8] = b"/PCREDS-CTX-ISS";
/// Oracle suffix of the context of `π_prove`.
const PROVE_SUFFIX: &[u8] = b"/PCREDS-CTX-PROVE";
/// Oracle suffix of `H_id`.
const IDENTIFIER_POINT_SUFFIX: &[u8] = b"/PCREDS-HID";
/// Oracle suffix of `H_req`.
const REQUEST_SUFFIX: &[u8] = b"/PCREDS-HREQ";
/// Oracle suffix of the fingerprint that binds users, pending requests and evaluated requests
/// to a helper key.
const HELPER_SUFFIX: &[u8] = b"/PCREDS-HELPER";

impl<Bk: Backend> super::types::PublicParameters<Bk> {
    /// The digest of `pp` that leads every context: the deployment label (which stands for
    /// `H_id`, `H_req` and `H_1`), the name of the instantiation and its parameters, each as a
    /// framed item in its canonical encoding.
    ///
    /// # Errors
    /// [`Error::Serialization`] if a parameter cannot be serialized.
    pub fn digest(&self) -> Result<[u8; 32], Error> {
        let mut transcript = Transcript::new(PP_SUFFIX);
        transcript.append_bytes(b"label", &self.label);
        transcript.append_bytes(b"backend", Bk::name().as_bytes());
        transcript.append_serializable(b"params", &self.params)?;
        Ok(transcript.digest())
    }
}

impl<Bk: Backend> Protocol<Bk> {
    /// A transcript of the oracle `suffix` that starts with `pp`.
    fn transcript(&self, suffix: &[u8]) -> Transcript {
        let mut transcript = Transcript::new(suffix);
        transcript.append_bytes(b"pp", &self.digest);
        transcript
    }

    /// The context `(ssid, P̃)` of `π_id`, under which the requester proves ownership of its
    /// identifier to the owner of the contact name `P̃`.
    #[must_use]
    pub fn identifier_context(&self, ssid: &[u8], contact: &[u8]) -> [u8; 32] {
        let mut transcript = self.transcript(IDENTIFIER_SUFFIX);
        transcript.append_bytes(b"ssid", ssid);
        transcript.append_bytes(b"contact", contact);
        transcript.digest()
    }

    /// The context of `π_att`: no session context, as in the paper; `pp` and `hvk` only.
    ///
    /// # Errors
    /// [`Error::Serialization`] if `hvk` cannot be serialized.
    pub fn attestation_context(&self, vk: &Bk::VerificationKey) -> Result<[u8; 32], Error> {
        self.attestation_context_in(vk, None)
    }

    /// The context of `π_att` extended by an APPLICATION CONTEXT `app` (implementation note for
    /// OpenVTC, not in the paper): the caller's bytes, such as the deployment's statement
    /// metadata, a validity window or a serial, appended after `hvk` as one framed item `app`.
    /// The attester and every verifier supply the same bytes, and a verifier takes them from
    /// its own copy of the public data, never from the prover. This is the paper's first remedy
    /// for replay (Remark "Attestations are standing endorsements": a context in the
    /// attestation challenge).
    ///
    /// `None` gives exactly [`Self::attestation_context`], so attestations made without an
    /// application context are unchanged. `Some(&[])` is a context of its own, distinct from
    /// `None`: the item is appended, and it is empty.
    ///
    /// # Errors
    /// [`Error::Serialization`] if `hvk` cannot be serialized.
    pub fn attestation_context_in(
        &self,
        vk: &Bk::VerificationKey,
        app: Option<&[u8]>,
    ) -> Result<[u8; 32], Error> {
        let mut transcript = self.transcript(ATTESTATION_SUFFIX);
        transcript.append_serializable(b"hvk", vk)?;
        if let Some(app) = app {
            transcript.append_bytes(b"app", app);
        }
        Ok(transcript.digest())
    }

    /// The context `(ssid, att⃗)` of `π_iss`. The attestations enter one by one, in order, each
    /// completely (`t`, `σ*` and `π_att`), after their number.
    ///
    /// # Errors
    /// [`Error::Serialization`] if a component cannot be serialized.
    pub fn issuance_context(
        &self,
        vk: &Bk::VerificationKey,
        ssid: &[u8],
        attestations: &[Attestation<Bk>],
    ) -> Result<[u8; 32], Error> {
        self.issuance_context_in(vk, ssid, attestations, None, None)
    }

    /// The context `(ssid, att⃗)` of `π_iss` extended by application contexts (implementation
    /// note for OpenVTC, not in the paper): after the attestations, an item `att-apps` holding
    /// their number, the context `app_j` of each attestation in order, each as an item
    /// `att-app`, and then the request's own context `app` (such as an audience), as an item
    /// `app`.
    ///
    /// `att_apps` binds `π_iss` to the contexts under which the helper checks the attestations,
    /// so that a requester cannot have an attestation checked under one context and prove under
    /// another. It holds one context per attestation. `None` for both gives exactly
    /// [`Self::issuance_context`]. As with `app`, `Some` is distinct from `None` whatever it
    /// holds: the `att-apps` item is appended for `Some`, also with no attestations, so a
    /// `π_iss` proved without application contexts never verifies under the context API.
    ///
    /// # Errors
    /// [`Error::LengthMismatch`] if `att_apps` does not hold one context per attestation, and
    /// [`Error::Serialization`] if a component cannot be serialized.
    pub fn issuance_context_in(
        &self,
        vk: &Bk::VerificationKey,
        ssid: &[u8],
        attestations: &[Attestation<Bk>],
        att_apps: Option<&[&[u8]]>,
        app: Option<&[u8]>,
    ) -> Result<[u8; 32], Error> {
        if let Some(apps) = att_apps
            && apps.len() != attestations.len()
        {
            return Err(Error::LengthMismatch {
                expected: attestations.len(),
                actual: apps.len(),
            });
        }
        let mut transcript = self.transcript(ISSUANCE_SUFFIX);
        transcript.append_serializable(b"hvk", vk)?;
        transcript.append_bytes(b"ssid", ssid);
        transcript.append_u64(b"count", attestations.len() as u64);
        for attestation in attestations {
            transcript.append_serializable(b"att", attestation)?;
        }
        if let Some(apps) = att_apps {
            transcript.append_u64(b"att-apps", apps.len() as u64);
            for att_app in apps {
                transcript.append_bytes(b"att-app", att_app);
            }
        }
        if let Some(app) = app {
            transcript.append_bytes(b"app", app);
        }
        Ok(transcript.digest())
    }

    /// The context `m` of `π_prove`.
    ///
    /// # Errors
    /// [`Error::Serialization`] if `hvk` cannot be serialized.
    pub fn prove_context(
        &self,
        vk: &Bk::VerificationKey,
        message: &[u8],
    ) -> Result<[u8; 32], Error> {
        let mut transcript = self.transcript(PROVE_SUFFIX);
        transcript.append_serializable(b"hvk", vk)?;
        transcript.append_bytes(b"message", message);
        Ok(transcript.digest())
    }

    /// The identifier point `x_0 = H_id(⟨hvk⟩)` of the helper key `vk` ("once the helper
    /// publishes `hvk`, set `x_0 = H_id(⟨hvk⟩)`, using its canonical encoding"). Every
    /// [`HelperKey`](super::HelperKey) carries its own ([`HelperKey::identifier_point`]); this is
    /// the oracle itself, for any key.
    ///
    /// [`HelperKey::identifier_point`]: super::HelperKey::identifier_point
    ///
    /// # Errors
    /// [`Error::Serialization`] if `hvk` cannot be serialized.
    pub fn identifier_point(&self, vk: &Bk::VerificationKey) -> Result<Bk::Point, Error> {
        let mut transcript = self.transcript(IDENTIFIER_POINT_SUFFIX);
        transcript.append_serializable(b"hvk", vk)?;
        Ok(Bk::identifier_point(&self.pp.params, &transcript))
    }

    /// The recipient point `x_Q = H_req(⟨pp, hvk, id_Q, j_Q⟩)`, where `j_Q` is the least
    /// nonnegative counter for which `x_Q ≠ x_0`, for the identifier point `x_0 = H_id(⟨hvk⟩)`
    /// of the same key.
    ///
    /// # Errors
    /// [`Error::Serialization`] if `hvk` or `id` cannot be serialized.
    pub fn recipient_point(
        &self,
        vk: &Bk::VerificationKey,
        id: &Bk::Tag,
    ) -> Result<Bk::Point, Error> {
        let x0 = self.identifier_point(vk)?;
        self.recipient_point_at(vk, &x0, id)
    }

    /// [`Self::recipient_point`] for a key whose identifier point `x0` is known.
    pub(super) fn recipient_point_at(
        &self,
        vk: &Bk::VerificationKey,
        x0: &Bk::Point,
        id: &Bk::Tag,
    ) -> Result<Bk::Point, Error> {
        let mut base = self.transcript(REQUEST_SUFFIX);
        base.append_serializable(b"hvk", vk)?;
        base.append_serializable(b"id", id)?;
        for counter in 0u64.. {
            let mut transcript = base.clone();
            transcript.append_u64(b"counter", counter);
            let point = Bk::request_point(&self.pp.params, &transcript);
            if !Bk::same_point(&self.pp.params, &point, x0) {
                return Ok(point);
            }
        }
        unreachable!("the counter does not overflow")
    }

    /// The fingerprint of a helper key under this deployment: what binds a
    /// [`User`](super::User), a [`PendingAttestation`](super::PendingAttestation) and an
    /// [`EvaluatedRequest`](super::EvaluatedRequest) to a helper key.
    pub(super) fn helper_fingerprint(&self, vk: &Bk::VerificationKey) -> Result<[u8; 32], Error> {
        let mut transcript = self.transcript(HELPER_SUFFIX);
        transcript.append_serializable(b"hvk", vk)?;
        Ok(transcript.digest())
    }
}
