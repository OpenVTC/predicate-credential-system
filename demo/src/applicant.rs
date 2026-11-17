//! The applicant's PCS engine (inside the applicant's VTA, design §13 C7): a fresh `usk` per
//! application under the current period, the attestation requests, verification of every
//! attestation on receipt (§13 C5), and the request the VTC evaluates.

use predicate_credential_system::pcreds::{AttestationRequest, User};
use rand::{CryptoRng, RngCore};

use crate::{
    ProtoError,
    meta::{ProofContext, StatementMeta, id_binding},
    scheme::{Bk, G1, point_text, scalar_text},
    token::verify_spend,
    vetter::HiddenAttestation,
    vtc::{Submission, Vtc},
};

/// A request for a vetting statement (`vetting/request`): the applicant's `(id_Q, π_id)` for the
/// applicant's period, under a fresh session `ssid` and through the vetter's contact name, so
/// that it cannot be answered in another session or by another vetter.
#[derive(Debug, Clone)]
pub struct VettingRequest {
    pub period: String,
    pub ssid: Vec<u8>,
    pub request: AttestationRequest<Bk>,
}

pub struct ApplicantEngine {
    period: String,
    user: User<Bk>,
    pub join_did: String,
    held: Vec<HiddenAttestation>,
}

impl ApplicantEngine {
    /// A fresh `usk` for this application, registered under the VTC's current period. The
    /// application lives in that period: its identifier is `Tag(usk, x_0)` at the identifier
    /// point of the period's helper key.
    pub fn new<R: RngCore + CryptoRng>(
        vtc: &Vtc,
        join_did: &str,
        rng: &mut R,
    ) -> Result<Self, ProtoError> {
        let period = vtc.current_period().to_string();
        let user = vtc.pcreds().register(vtc.hvk(&period)?, rng)?;
        Ok(Self {
            period,
            user,
            join_did: join_did.to_string(),
            held: Vec::new(),
        })
    }

    pub fn id(&self) -> &G1 {
        self.user.id()
    }

    pub fn period(&self) -> &str {
        &self.period
    }

    pub fn held(&self) -> usize {
        self.held.len()
    }

    /// Ask the vetter reached through `contact` for a statement.
    pub fn vetting_request<R: RngCore + CryptoRng>(
        &self,
        vtc: &Vtc,
        contact: &str,
        rng: &mut R,
    ) -> Result<VettingRequest, ProtoError> {
        let mut ssid = [0u8; 16];
        rng.fill_bytes(&mut ssid);
        let request = vtc.pcreds().request_attestation(
            vtc.hvk(&self.period)?,
            &self.user,
            &ssid,
            contact.as_bytes(),
            rng,
        )?;
        Ok(VettingRequest {
            period: self.period.clone(),
            ssid: ssid.to_vec(),
            request,
        })
    }

    /// A metadata template the vetter completes. The token fields are the vetter's to fill.
    pub fn statement_meta(&self, vtc: &Vtc, base: StatementMeta) -> StatementMeta {
        StatementMeta {
            community: vtc.community.clone(),
            requirements_digest: vtc.requirements_digest().to_string(),
            ..base
        }
    }

    /// Check an attestation on receipt, so that `no-token` or a bad attestation shows up at the
    /// session and not at submit.
    pub fn receive(&mut self, vtc: &Vtc, att: HiddenAttestation) -> Result<(), ProtoError> {
        self.check(vtc, &att)?;
        self.held.push(att);
        Ok(())
    }

    /// Every check [`Self::receive`] makes, with no change to what is held.
    fn check(&self, vtc: &Vtc, att: &HiddenAttestation) -> Result<(), ProtoError> {
        if att.period != self.period {
            return Err(ProtoError::AttestationRejected(format!(
                "made under period {}, not this application's {}",
                att.period, self.period
            )));
        }
        let hvk = vtc
            .hvk(&self.period)
            .map_err(|e| ProtoError::AttestationRejected(e.to_string()))?;
        let app = att.meta.context_bytes()?;
        vtc.pcreds()
            .check_attestation_in_context(hvk, self.id(), &att.attestation, &app)
            .map_err(|e| ProtoError::AttestationRejected(e.to_string()))?;
        if att.meta.token_label != att.token.label
            || att.meta.token_serial != scalar_text(&att.token.serial)?
        {
            return Err(ProtoError::AttestationRejected(
                "token does not match its statement".into(),
            ));
        }
        let tvk = vtc
            .tokens
            .tvk(&att.token.label)
            .ok_or_else(|| ProtoError::AttestationRejected("token label is not live".into()))?;
        if !verify_spend(tvk, &att.token) {
            return Err(ProtoError::AttestationRejected(
                "token signature does not verify".into(),
            ));
        }
        Ok(())
    }

    /// Replace what a vetter vetted again: same tag, newer attestation. The new one is checked
    /// first, so that one that fails leaves the old one held.
    pub fn replace(&mut self, vtc: &Vtc, att: HiddenAttestation) -> Result<(), ProtoError> {
        self.check(vtc, &att)?;
        let tag = att.attestation.tag;
        self.held.retain(|h| h.attestation.tag != tag);
        self.held.push(att);
        Ok(())
    }

    /// Build the submission from every held attestation that is still usable, that is whose
    /// token label is live, one per tag (the VTC refuses a request with two attestations of one
    /// tag).
    pub fn submit<R: RngCore + CryptoRng>(
        &self,
        vtc: &Vtc,
        challenge: &str,
        rng: &mut R,
    ) -> Result<Submission, ProtoError> {
        let live = vtc.tokens.live_labels();
        let mut usable: Vec<&HiddenAttestation> = Vec::new();
        for h in &self.held {
            if live.contains(&h.token.label)
                && !usable
                    .iter()
                    .any(|u| u.attestation.tag == h.attestation.tag)
            {
                usable.push(h);
            }
        }
        self.submit_attestations(vtc, challenge, &usable, rng)
    }

    /// The submission over exactly `usable`, in order and unchecked: a credential request under
    /// the session `ssid = challenge`, bound to the metadata of every statement and to the
    /// proof context. The VTC only evaluates it and never answers it with a credential (design
    /// §13 C4), so the issuance state is dropped. [`Self::submit`] calls it with the usable
    /// held attestations, and tests call it as an ADVERSARY HOOK with others.
    #[doc(hidden)]
    pub fn submit_attestations<R: RngCore + CryptoRng>(
        &self,
        vtc: &Vtc,
        challenge: &str,
        usable: &[&HiddenAttestation],
        rng: &mut R,
    ) -> Result<Submission, ProtoError> {
        let atts: Vec<_> = usable.iter().map(|h| h.attestation.clone()).collect();
        let apps: Vec<Vec<u8>> = usable
            .iter()
            .map(|h| h.meta.context_bytes())
            .collect::<Result<_, _>>()?;
        let app_refs: Vec<&[u8]> = apps.iter().map(Vec::as_slice).collect();
        let app0 = ProofContext {
            challenge: challenge.to_string(),
            audience: vtc.audience().to_string(),
            join_did: self.join_did.clone(),
            id_binding: id_binding(
                &point_text(self.id())?,
                &vtc.community,
                vtc.requirements_digest(),
                &self.join_did,
            ),
        }
        .context_bytes()?;
        let (request, _state) = vtc.pcreds().request_credential_in_context(
            vtc.hvk(&self.period)?,
            &self.user,
            atts,
            &app_refs,
            challenge.as_bytes(),
            &app0,
            rng,
        )?;
        Ok(Submission {
            period: self.period.clone(),
            join_did: self.join_did.clone(),
            challenge: challenge.to_string(),
            statements: usable
                .iter()
                .map(|h| (h.meta.clone(), h.token.clone()))
                .collect(),
            request,
        })
    }
}
