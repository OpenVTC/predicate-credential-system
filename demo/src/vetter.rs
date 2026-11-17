//! The vetter's PCS engine, i.e. what runs inside the vetter's VTA (design §13 C7): one key and
//! one root credential per period, the token bucket, attest, refresh and withdraw. openvtc would
//! only drive these.

use std::collections::BTreeMap;

use predicate_credential_system::{
    Error as PcsError,
    pcreds::{Attestation, Backend, Credential, PendingAttestation, User},
    sigma::FSProof,
};
use rand::{CryptoRng, RngCore};

use crate::{
    ProtoError,
    applicant::VettingRequest,
    meta::StatementMeta,
    scheme::{Bk, Fr, G1, point_text, scalar_text},
    token::{Reservation, TokenSpend, TokenWallet},
    vtc::{Vtc, enrolment_ssid, withdraw_context},
};

/// An attestation as the applicant receives it (`vetting/attestation/0.1`).
#[derive(Debug, Clone)]
pub struct HiddenAttestation {
    /// The period whose helper key the attestation is under: the applicant's.
    pub period: String,
    /// The `ssid` of the vetting session it answers, which the applicant names to ask for a
    /// refresh.
    pub session: Vec<u8>,
    pub attestation: Attestation<Bk>,
    pub meta: StatementMeta,
    pub token: TokenSpend,
}

/// What a vetter holds for one period: the user it is under the period's helper key (which
/// holds, and wipes on drop, its key for the period), and its root credential.
struct Enrolment {
    user: User<Bk>,
    cred: Credential<Bk>,
}

/// A statement this vetter made, kept so that it can be attested again without a new session
/// (design §4.3).
struct Logged {
    session: Vec<u8>,
    meta: StatementMeta,
}

pub struct VetterEngine {
    pub member: String,
    enrolments: BTreeMap<String, Enrolment>,
    wallet: TokenWallet,
    /// A limit below the community's drip, kept here and never sent anywhere (§5.1).
    pub personal_limit: Option<usize>,
    attested: usize,
    log: Vec<Logged>,
}

impl VetterEngine {
    pub fn new(member: &str) -> Self {
        Self {
            member: member.to_string(),
            enrolments: BTreeMap::new(),
            wallet: TokenWallet::new(),
            personal_limit: None,
            attested: 0,
            log: Vec::new(),
        }
    }

    /// The vetter's identifier under `period`, if it holds a credential for it.
    pub fn id(&self, period: &str) -> Option<&G1> {
        self.enrolments.get(period).map(|e| e.user.id())
    }

    /// Every identifier the vetter holds, one per period.
    pub fn ids(&self) -> impl Iterator<Item = &G1> {
        self.enrolments.values().map(|e| e.user.id())
    }

    /// Root request for the VTC's current period, with a key drawn for that period. Nothing
    /// needs a key to outlive its period, since a request never spans two (module `scheme`),
    /// and a key that is ever recovered then links the tags of one period, not of a career
    /// (design §18.2).
    pub fn enroll<R: RngCore + CryptoRng>(
        &mut self,
        vtc: &mut Vtc,
        rng: &mut R,
    ) -> Result<(), ProtoError> {
        let period = vtc.current_period().to_string();
        let ssid = enrolment_ssid(&vtc.community, &self.member, &period);
        let hvk = vtc.hvk(&period)?.clone();
        let usk = <Bk as Backend>::tag_keygen(vtc.pcreds().params(), rng);
        let user = vtc.pcreds().user(&hvk, usk)?;
        let (message, state) =
            vtc.pcreds()
                .request_credential(&hvk, &user, Vec::new(), &ssid, rng)?;
        let pre = vtc.issue_vetter_root(&self.member, &period, &message, rng)?;
        let cred = vtc.pcreds().unblind(&hvk, &user, &pre, state)?;
        self.enrolments.insert(period, Enrolment { user, cred });
        Ok(())
    }

    /// One scheduled drip fetch: unconditional, `r` tokens.
    pub fn drip<R: RngCore + CryptoRng>(
        &mut self,
        vtc: &mut Vtc,
        tick: u32,
        label: &str,
        r: usize,
        rng: &mut R,
    ) -> Result<(), ProtoError> {
        let tvk = vtc
            .tokens
            .tvk(label)
            .ok_or_else(|| ProtoError::LabelNotLive(label.to_string()))?
            .clone();
        let reqs = self
            .wallet
            .prepare(&tvk, label, &self.member, tick, r, rng)?;
        let pres = vtc.drip(&self.member, tick, label, &reqs, rng)?;
        self.wallet.receive(&tvk, &pres)?;
        self.wallet.expire(vtc.tokens.live_labels());
        Ok(())
    }

    /// Tokens whose label closed are gone, and so are the keys of periods that are no longer
    /// live. The log of statements stays, for refreshes.
    pub fn expire(&mut self, vtc: &Vtc) {
        self.wallet.expire(vtc.tokens.live_labels());
        self.enrolments.retain(|period, _| vtc.is_live(period));
    }

    pub fn tokens_held(&self) -> usize {
        self.wallet.held()
    }

    pub fn tokens_free(&self) -> usize {
        self.wallet.free()
    }

    /// Accepting a `vetting/request` reserves a token (§5.2), or declines `atCapacity`.
    pub fn accept(
        &mut self,
        prefer_label: Option<&str>,
        next_tick: u32,
    ) -> Result<Reservation, ProtoError> {
        if self.personal_limit.is_some_and(|l| self.attested >= l) {
            return Err(ProtoError::AtCapacity {
                available_from: next_tick,
            });
        }
        self.wallet
            .reserve(prefer_label)
            .ok_or(ProtoError::AtCapacity {
                available_from: next_tick,
            })
    }

    pub fn decline(&mut self, r: &Reservation) {
        self.wallet.release(r);
    }

    /// Attest for the applicant of `request` after the human check: check its `π_id` under the
    /// applicant's period, bind the reserved token's serial and the statement metadata into
    /// the attestation's context, attest with this vetter's credential of that period, and only
    /// then spend the token, so that a failed attestation leaves it reserved, not lost.
    pub fn attest<R: RngCore + CryptoRng>(
        &mut self,
        vtc: &Vtc,
        reservation: &Reservation,
        request: &VettingRequest,
        meta: StatementMeta,
        rng: &mut R,
    ) -> Result<HiddenAttestation, ProtoError> {
        let pending = self.receive(vtc, request)?;
        let (attestation, meta) = self.sign(
            vtc,
            request,
            pending,
            &reservation.label,
            &reservation.serial,
            meta,
            rng,
        )?;
        let token = self.wallet.spend(reservation, rng)?;
        Ok(self.record(request, attestation, meta, token))
    }

    /// ADVERSARY HOOK for tests: attest with a token of the caller's choosing, e.g. one already
    /// spent. An honest engine never does this, and the VTC's spent set is what stops it.
    #[doc(hidden)]
    pub fn attest_with_token<R: RngCore + CryptoRng>(
        &mut self,
        vtc: &Vtc,
        token: TokenSpend,
        request: &VettingRequest,
        meta: StatementMeta,
        rng: &mut R,
    ) -> Result<HiddenAttestation, ProtoError> {
        let pending = self.receive(vtc, request)?;
        let (attestation, meta) = self.sign(
            vtc,
            request,
            pending,
            &token.label,
            &token.serial,
            meta,
            rng,
        )?;
        Ok(self.record(request, attestation, meta, token))
    }

    /// The credential of a live period.
    fn enrolment(&self, vtc: &Vtc, period: &str) -> Result<&Enrolment, ProtoError> {
        vtc.hvk(period)?;
        self.enrolments
            .get(period)
            .ok_or_else(|| ProtoError::NoCredentialForPeriod(period.to_string()))
    }

    /// The request's `π_id`, checked under the applicant's period and this vetter's contact
    /// name, before any token is spent.
    fn receive(
        &self,
        vtc: &Vtc,
        request: &VettingRequest,
    ) -> Result<PendingAttestation<Bk>, ProtoError> {
        self.enrolment(vtc, &request.period)?;
        Ok(vtc.pcreds().receive_attestation_request(
            vtc.hvk(&request.period)?,
            &request.request,
            &request.ssid,
            self.member.as_bytes(),
        )?)
    }

    /// The attestation, bound to `meta` completed with the token's label and serial. Fallible,
    /// and touches no state.
    #[allow(clippy::too_many_arguments)]
    fn sign<R: RngCore + CryptoRng>(
        &self,
        vtc: &Vtc,
        request: &VettingRequest,
        pending: PendingAttestation<Bk>,
        token_label: &str,
        token_serial: &Fr,
        mut meta: StatementMeta,
        rng: &mut R,
    ) -> Result<(Attestation<Bk>, StatementMeta), ProtoError> {
        meta.token_label = token_label.to_string();
        meta.token_serial = scalar_text(token_serial)?;
        let app = meta.context_bytes()?;
        let enrolment = self.enrolment(vtc, &request.period)?;
        let attestation = vtc.pcreds().attest_in_context(
            vtc.hvk(&request.period)?,
            &enrolment.user,
            &enrolment.cred,
            pending,
            &app,
            rng,
        )?;
        Ok((attestation, meta))
    }

    /// Infallible: count and log a signed attestation.
    fn record(
        &mut self,
        request: &VettingRequest,
        attestation: Attestation<Bk>,
        meta: StatementMeta,
        token: TokenSpend,
    ) -> HiddenAttestation {
        self.attested += 1;
        self.log.push(Logged {
            session: request.ssid.clone(),
            meta: meta.clone(),
        });
        HiddenAttestation {
            period: request.period.clone(),
            session: request.ssid.clone(),
            attestation,
            meta,
            token,
        }
    }

    /// Refresh: the statement this vetter made in the session `session`, attested again for a
    /// new request of the same applicant, with a fresh token and no new human check (design
    /// §4.3). After a rotation the new request is under the new period, with a new identifier,
    /// so the attestation has a new tag: tags under different helper keys are unlinkable, which
    /// is why a request never mixes periods, and so why one vetter cannot count twice in one.
    /// The vetter's client knows the applicant by the session the refresh request arrives on.
    /// There is no transport here, so the prototype names the session by its `ssid`.
    pub fn refresh<R: RngCore + CryptoRng>(
        &mut self,
        vtc: &Vtc,
        session: &[u8],
        request: &VettingRequest,
        rng: &mut R,
    ) -> Result<HiddenAttestation, ProtoError> {
        let meta = self
            .log
            .iter()
            .rev()
            .find(|l| l.session == session)
            .map(|l| l.meta.clone())
            .ok_or(ProtoError::NoSuchStatement)?;
        let reservation = self.accept(None, 0)?;
        match self.attest(vtc, &reservation, request, meta, rng) {
            Ok(att) => {
                self.attested -= 1; // a refresh is not a new vetting
                Ok(att)
            }
            Err(e) => {
                // `attest` spends the token only once the attestation is made, so it is still
                // reserved here and goes back to the free pool.
                self.wallet.release(&reservation);
                Err(e)
            }
        }
    }

    /// Withdraw one statement: the tag `t = Tag(usk, x_Q)` at the applicant's recipient point
    /// under `period`, and a proof of knowledge of the key behind it that does not link to this
    /// vetter's identifier (§4.4).
    pub fn withdraw<R: RngCore + CryptoRng>(
        &self,
        vtc: &Vtc,
        period: &str,
        applicant_id: &G1,
        rng: &mut R,
    ) -> Result<(G1, FSProof<Fr>), ProtoError> {
        let enrolment = self.enrolment(vtc, period)?;
        let hvk = vtc.hvk(period)?;
        let params = vtc.pcreds().params();
        let xq = vtc.pcreds().recipient_point(hvk.vk(), applicant_id)?;
        let tag = <Bk as Backend>::tag(params, enrolment.user.expose_key(), &xq)
            .ok_or(PcsError::UndefinedTag)?;
        let ctx = withdraw_context(&vtc.community, period, &point_text(applicant_id)?);
        let proof =
            <Bk as Backend>::prove_tag(params, &tag, &xq, enrolment.user.expose_key(), &ctx, rng)?;
        Ok((tag, proof))
    }
}
