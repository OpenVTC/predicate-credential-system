//! The VTC as PCS *helper*: issues vetter credentials and tokens, evaluates the applicants'
//! requests, and hands VTI's counting rule the same `StatementFacts` it gets today, with the
//! vetter's tag where the vetter's DID used to be (design §2).

use std::{
    collections::{BTreeMap, HashMap, HashSet},
    sync::Mutex,
};

use chrono::{DateTime, NaiveTime, Utc};
use predicate_credential_system::{
    pcreds::{
        Backend, CredentialRequest, Decision as PcsDecision, Helper, HelperKey, Policy, Reply,
    },
    sigma::FSProof,
};
use rand::{CryptoRng, RngCore};
use serde::Serialize;
use vta_sdk::{
    protocols::vetting::{VettingMethod, VettingRelationship, VettingRequirements},
    vetting::requirements::{Evaluation, StatementFacts, evaluate},
};

use crate::{
    ProtoError,
    meta::{ProofContext, StatementMeta, id_binding},
    scheme::{
        Bk, Fr, G1, Pcreds, deployment_label, event_token_label, monthly_token_label, point_text,
        scalar_text,
    },
    token::{SpendOutcome, TokenIssuer, TokenRequest, TokenSpend},
};

/// The join submission's hidden-vetting part (`submit/0.3 vettingProof`, design §8).
#[derive(Debug, Clone)]
pub struct Submission {
    /// The period of the applicant's identifier: the request is under its helper key.
    pub period: String,
    pub join_did: String,
    pub challenge: String,
    /// One per attestation of `request`, in the same order.
    pub statements: Vec<(StatementMeta, TokenSpend)>,
    /// `(id_Q, att⃗, Ĉ, π_iss)` under the session `ssid = challenge`, bound to the metadata of
    /// every statement and to the proof context.
    pub request: CredentialRequest<Bk>,
}

/// One row of `VettingFacts.statements`, as the VTC builds it today, with `issuer` = the tag.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct StatementRecord {
    pub id: String,
    pub issuer: String,
    pub verified: bool,
    pub eligible: bool,
    pub revoked: bool,
    pub method: VettingMethod,
    pub declared_relationship: VettingRelationship,
    pub counted: bool,
    pub failures: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct Decision {
    pub evaluation: Evaluation,
    pub statements: Vec<StatementRecord>,
}

/// What the VTC keeps per statement of an application: the facts it counted and its own
/// failure codes, keyed by the statement's metadata digest.
#[derive(Debug, Clone)]
struct Kept {
    facts: StatementFacts,
    tag: String,
    verified: bool,
    method: VettingMethod,
    relationship: VettingRelationship,
    failures: Vec<String>,
}

/// One live vetter period: its helper (the key pair and the set `I` of identifiers issued to),
/// and the members enrolled under it.
struct Period {
    name: String,
    helper: Helper<Bk>,
    /// One lock per signing key (§13 C3).
    lock: Mutex<()>,
    /// member → PCS identifier under this period's key: one root credential per member and
    /// period.
    enrolled: HashMap<String, String>,
}

impl Period {
    /// A fresh helper key for `name`. Its policy `Pol_k` has a `k` that no request reaches, so
    /// that the policy path never issues: every credential under a period's key is a root
    /// admission behind the grant check, and an applicant's request is only ever evaluated
    /// (design §13 C4).
    fn new<R: RngCore + CryptoRng>(
        pcreds: &Pcreds,
        name: &str,
        rng: &mut R,
    ) -> Result<Self, ProtoError> {
        Ok(Self {
            name: name.to_string(),
            helper: pcreds.helper_keygen(Policy::threshold(usize::MAX)?, rng),
            lock: Mutex::new(()),
            enrolled: HashMap::new(),
        })
    }
}

/// The most attestations [`Vtc::submit`] verifies in one request. Every attestation costs a
/// pairing check, so a request is refused above this before any is verified. The helper's own
/// `Policy::with_max_attestations` cannot carry it, since the period policy's `k` is
/// `usize::MAX` (see [`Period::new`]).
pub const MAX_ATTESTATIONS: usize = 64;

/// The `ssid` of a root request: the community, the member and the period. The VTC rebuilds it
/// for the member that submits, so that a root request is bound to that member.
pub fn enrolment_ssid(community: &str, member: &str, period: &str) -> Vec<u8> {
    let mut ssid = b"openvtc/hidden-vetting/enrol/0.1\0".to_vec();
    for part in [community, member, period] {
        ssid.extend((part.len() as u64).to_le_bytes());
        ssid.extend(part.as_bytes());
    }
    ssid
}

pub struct Vtc {
    pub community: String,
    audience: String,
    pcreds: Pcreds,
    /// Live vetter periods, current first.
    periods: Vec<Period>,
    grants: HashSet<String>,
    pub tokens: TokenIssuer,
    current_token_label: String,
    events: HashMap<String, HashSet<String>>,
    withdrawn: HashSet<(String, String)>,
    applications: HashMap<String, BTreeMap<String, Kept>>,
    challenges: HashSet<String>,
    requirements: VettingRequirements,
    requirements_digest: String,
}

impl Vtc {
    pub fn new<R: RngCore + CryptoRng>(
        community: &str,
        period: &str,
        requirements: serde_json::Value,
        rng: &mut R,
    ) -> Result<Self, ProtoError> {
        let pcreds = Pcreds::setup(&deployment_label(community))?;
        let first = Period::new(&pcreds, period, rng)?;
        let requirements_digest =
            vta_sdk::vetting::requirements::requirements_digest(&requirements)
                .map_err(|e| ProtoError::Serialization(e.to_string()))?;
        let requirements: VettingRequirements = serde_json::from_value(requirements)
            .map_err(|e| ProtoError::Serialization(e.to_string()))?;
        let mut tokens = TokenIssuer::new();
        let current_token_label = monthly_token_label(period);
        tokens.open_label(&current_token_label, rng);
        Ok(Self {
            community: community.to_string(),
            audience: community.to_string(),
            pcreds,
            periods: vec![first],
            grants: HashSet::new(),
            tokens,
            current_token_label,
            events: HashMap::new(),
            withdrawn: HashSet::new(),
            applications: HashMap::new(),
            challenges: HashSet::new(),
            requirements,
            requirements_digest,
        })
    }

    // --- public parameters, as the manifest's `vetting.anonymity` would carry them ----------

    pub fn pcreds(&self) -> &Pcreds {
        &self.pcreds
    }

    /// The helper key of a live period. In a deployment each party checks the published key
    /// once (`Protocol::helper_key`), and the prototype hands out the VTC's.
    pub fn hvk(&self, period: &str) -> Result<&HelperKey<Bk>, ProtoError> {
        Ok(self.period(period)?.helper.key())
    }

    fn period(&self, name: &str) -> Result<&Period, ProtoError> {
        self.periods
            .iter()
            .find(|p| p.name == name)
            .ok_or_else(|| ProtoError::PeriodNotLive(name.to_string()))
    }

    pub fn is_live(&self, period: &str) -> bool {
        self.periods.iter().any(|p| p.name == period)
    }

    pub fn live_periods(&self) -> Vec<&str> {
        self.periods.iter().map(|p| p.name.as_str()).collect()
    }

    pub fn current_period(&self) -> &str {
        &self.periods[0].name
    }

    pub fn current_token_label(&self) -> &str {
        &self.current_token_label
    }

    pub fn requirements_digest(&self) -> &str {
        &self.requirements_digest
    }

    pub fn audience(&self) -> &str {
        &self.audience
    }

    // --- vetters ----------------------------------------------------------------------------

    pub fn grant(&mut self, member: &str) {
        self.grants.insert(member.to_string());
    }

    /// Removal: the member gets no credential under any later period. Their credential under a
    /// live period still works until that period leaves the window, or until
    /// [`Self::drop_period`] (emergency).
    pub fn revoke(&mut self, member: &str) {
        self.grants.remove(member);
    }

    /// Root admission under the CURRENT period, behind the grant check (§3, §13 C3): one
    /// credential per member and period. `message` is the member's credential request with no
    /// attestations, under the session [`enrolment_ssid`] of `member`, which the VTC rebuilds
    /// rather than takes from the caller: a request replayed by another member fails `π_iss`.
    pub fn issue_vetter_root<R: RngCore + CryptoRng>(
        &mut self,
        member: &str,
        period: &str,
        message: &CredentialRequest<Bk>,
        rng: &mut R,
    ) -> Result<<Bk as Backend>::PreCredential, ProtoError> {
        if !self.grants.contains(member) {
            return Err(ProtoError::NotAVetter(member.to_string()));
        }
        if period != self.current_period() {
            return Err(ProtoError::NotCurrentPeriod(period.to_string()));
        }
        let already = || ProtoError::AlreadyIssued {
            member: member.to_string(),
            period: period.to_string(),
        };
        let ssid = enrolment_ssid(&self.community, member, period);
        let current = &mut self.periods[0];
        if current.enrolled.contains_key(member) {
            return Err(already());
        }
        let evaluated = self
            .pcreds
            .evaluate_request(&current.helper, message, &ssid)?;
        let id_text = point_text(evaluated.id())?;
        let reply = {
            let _guard = current.lock.lock().expect("helper signing lock");
            self.pcreds
                .respond(&mut current.helper, evaluated, PcsDecision::Root, rng)?
        };
        match reply {
            Reply::PreCredential(pre) => {
                current.enrolled.insert(member.to_string(), id_text);
                Ok(pre)
            }
            // `Issued`: the identifier holds a credential of this period already. `Fail` does
            // not occur for a root admission.
            Reply::Issued | Reply::Fail => Err(already()),
        }
    }

    /// Period rotation: a new helper key for the new period, which becomes current, the
    /// previous one stays live, anything older is dropped with its key. Same for the monthly
    /// token labels.
    pub fn rotate<R: RngCore + CryptoRng>(
        &mut self,
        new_period: &str,
        rng: &mut R,
    ) -> Result<(), ProtoError> {
        if self.is_live(new_period) {
            return Err(ProtoError::PeriodExists(new_period.to_string()));
        }
        let previous = self.current_period().to_string();
        let fresh = Period::new(&self.pcreds, new_period, rng)?;
        self.periods.truncate(1);
        self.periods.insert(0, fresh);
        let old_labels: Vec<String> = self
            .tokens
            .live_labels()
            .iter()
            .filter(|l| !l.starts_with("token/event/") && **l != monthly_token_label(&previous))
            .cloned()
            .collect();
        for l in old_labels {
            self.tokens.close_label(&l);
        }
        self.current_token_label = monthly_token_label(new_period);
        self.tokens.open_label(&self.current_token_label, rng);
        Ok(())
    }

    /// Emergency: a period that is not the current one is dropped now, with its helper key,
    /// e.g. to make a removal immediate. Every request under it fails from then on.
    pub fn drop_period(&mut self, period: &str) -> Result<(), ProtoError> {
        if period == self.current_period() {
            return Err(ProtoError::DropsCurrentPeriod(period.to_string()));
        }
        self.periods.retain(|p| p.name != period);
        Ok(())
    }

    // --- tokens -----------------------------------------------------------------------------

    /// One tick of the drip for `member` under `label` (monthly or event).
    pub fn drip<R: RngCore + CryptoRng>(
        &mut self,
        member: &str,
        tick: u32,
        label: &str,
        requests: &[TokenRequest],
        rng: &mut R,
    ) -> Result<Vec<<Bk as Backend>::PreCredential>, ProtoError> {
        if !self.grants.contains(member) {
            return Err(ProtoError::NotAVetter(member.to_string()));
        }
        if let Some(event) = label.strip_prefix("token/event/")
            && !self.events.get(event).is_some_and(|g| g.contains(member))
        {
            return Err(ProtoError::EventRefused(format!(
                "{member} is not in event {event}"
            )));
        }
        self.tokens.issue(member, tick, label, requests, rng)
    }

    /// Event mode (§5.1): approved by someone outside the group, for a group of at least
    /// `floor` vetters who all hold live grants.
    pub fn approve_event<R: RngCore + CryptoRng>(
        &mut self,
        event_id: &str,
        members: &[&str],
        approver: &str,
        floor: usize,
        rng: &mut R,
    ) -> Result<String, ProtoError> {
        if members.contains(&approver) {
            return Err(ProtoError::EventRefused(
                "a vetter cannot approve their own event mode".into(),
            ));
        }
        let group: HashSet<String> = members.iter().map(|m| (*m).to_string()).collect();
        if group.len() < floor {
            return Err(ProtoError::EventRefused(format!(
                "group of {} is below the floor of {floor}",
                group.len()
            )));
        }
        if let Some(m) = group.iter().find(|m| !self.grants.contains(*m)) {
            return Err(ProtoError::NotAVetter(m.clone()));
        }
        self.events.insert(event_id.to_string(), group);
        let label = event_token_label(event_id);
        self.tokens.open_label(&label, rng);
        Ok(label)
    }

    /// The event's grace period is over: its tokens die.
    pub fn close_event(&mut self, event_id: &str) {
        self.tokens.close_label(&event_token_label(event_id));
        self.events.remove(event_id);
    }

    // --- admission --------------------------------------------------------------------------

    pub fn challenge<R: RngCore + CryptoRng>(&mut self, rng: &mut R) -> String {
        let mut b = [0u8; 16];
        rng.fill_bytes(&mut b);
        let c: String = b.iter().map(|x| format!("{x:02x}")).collect();
        self.challenges.insert(c.clone());
        c
    }

    /// Evaluate a submission, spend its tokens, and count. Records are kept per applicant `id`,
    /// so a resubmission after `requestMore` adds to what was already counted.
    pub fn submit(&mut self, sub: &Submission, now: DateTime<Utc>) -> Result<Decision, ProtoError> {
        if !self.challenges.remove(&sub.challenge) {
            return Err(ProtoError::BadChallenge);
        }
        let attestations = &sub.request.attestations;
        if attestations.len() > MAX_ATTESTATIONS {
            return Err(ProtoError::TooManyAttestations {
                count: attestations.len(),
                max: MAX_ATTESTATIONS,
            });
        }
        if sub.statements.len() != attestations.len() {
            return Err(ProtoError::CountMismatch {
                statements: sub.statements.len(),
                attestations: attestations.len(),
            });
        }
        // One attestation per tag, so that the set `N''` of the tags of the valid attestations
        // says which attestation verified.
        let mut tags = Vec::with_capacity(attestations.len());
        for att in attestations {
            let tag = point_text(&att.tag)?;
            if tags.contains(&tag) {
                return Err(ProtoError::DuplicateTag);
            }
            tags.push(tag);
        }
        let id_text = point_text(&sub.request.id)?;
        let app0 = ProofContext {
            challenge: sub.challenge.clone(),
            audience: self.audience.clone(),
            join_did: sub.join_did.clone(),
            id_binding: id_binding(
                &id_text,
                &self.community,
                &self.requirements_digest,
                &sub.join_did,
            ),
        }
        .context_bytes()?;
        let apps: Vec<Vec<u8>> = sub
            .statements
            .iter()
            .map(|(m, _)| m.context_bytes())
            .collect::<Result<_, _>>()?;
        let app_refs: Vec<&[u8]> = apps.iter().map(Vec::as_slice).collect();
        let evaluated = self
            .pcreds
            .evaluate_request_in_context(
                &self.period(&sub.period)?.helper,
                &sub.request,
                sub.challenge.as_bytes(),
                &app_refs,
                &app0,
            )
            .map_err(ProtoError::ProofRejected)?;
        let valid: HashSet<String> = evaluated
            .tags()
            .iter()
            .map(point_text)
            .collect::<Result<_, _>>()?;

        // `π_iss` holds: the applicant owns `id`, and the request is bound to this challenge, to
        // the proof context and to the metadata of every statement, in order. A statement whose
        // tag is in `N''` is a valid attestation from a holder of a credential of the period,
        // bound to its metadata (including its token serial).
        for ((meta, spend), tag) in sub.statements.iter().zip(tags) {
            let verified = valid.contains(&tag);
            let mut failures = Vec::new();
            // The checks that need no token come first, so that a statement already ineligible
            // for them does not burn its token in the spent set.
            if meta.requirements_digest != self.requirements_digest {
                failures.push("requirements-digest-mismatch".to_string());
            }
            if now.date_naive() > meta.valid_until {
                failures.push("expired".to_string());
            }
            let mut eligible = verified && failures.is_empty();
            if !verified {
                failures.push("unverified".to_string());
            } else if !eligible {
                // Not spent: see above.
            } else if meta.token_label != spend.label
                || meta.token_serial != scalar_text(&spend.serial)?
            {
                failures.push("token-mismatch".to_string());
                eligible = false;
            } else if !self.tokens.signature_ok(spend) {
                failures.push("no-token".to_string());
                eligible = false;
            } else if self.tokens.record_spend(spend, &id_text, &tag)? == SpendOutcome::DoubleSpend
            {
                failures.push("token-double-spend".to_string());
                eligible = false;
            }
            let facts = StatementFacts {
                statement_id: meta.digest()?,
                vetter: tag.clone(),
                method: meta.method,
                claims_verified: meta.claims_verified.clone(),
                document_classes: Vec::new(),
                declared_relationship: meta.declared_relationship,
                identity_commitment: meta.identity_commitment.clone(),
                valid_from: DateTime::from_naive_utc_and_offset(
                    meta.valid_from.and_time(NaiveTime::MIN),
                    Utc,
                ),
                community_matches: meta.community == self.community,
                eligible,
                revoked: false,
            };
            self.applications
                .entry(id_text.clone())
                .or_default()
                .insert(
                    facts.statement_id.clone(),
                    Kept {
                        facts,
                        tag,
                        verified,
                        method: meta.method,
                        relationship: meta.declared_relationship,
                        failures,
                    },
                );
        }
        Ok(self.evaluate(&id_text, now))
    }

    /// Count an application as it stands now (withdrawals included).
    pub fn evaluate(&self, id_text: &str, now: DateTime<Utc>) -> Decision {
        let kept: Vec<Kept> = self
            .applications
            .get(id_text)
            .map(|m| m.values().cloned().collect())
            .unwrap_or_default();
        let facts: Vec<StatementFacts> = kept
            .iter()
            .map(|k| {
                let mut f = k.facts.clone();
                f.revoked = self
                    .withdrawn
                    .contains(&(id_text.to_string(), k.tag.clone()));
                f
            })
            .collect();
        let evaluation = evaluate(&self.requirements, &facts, now);
        let statements = kept
            .iter()
            .zip(&facts)
            .map(|(k, f)| {
                let mut failures = k.failures.clone();
                if let Some((_, reasons)) = evaluation
                    .not_counted
                    .iter()
                    .find(|(id, _)| *id == f.statement_id)
                {
                    failures.extend(reasons.iter().map(|r| r.code().to_string()));
                }
                failures.dedup();
                StatementRecord {
                    id: f.statement_id.clone(),
                    issuer: k.tag.clone(),
                    verified: k.verified,
                    eligible: f.eligible,
                    revoked: f.revoked,
                    method: k.method,
                    declared_relationship: k.relationship,
                    counted: evaluation.counted.contains(&f.statement_id),
                    failures,
                }
            })
            .collect();
        Decision {
            evaluation,
            statements,
        }
    }

    /// Withdrawal of one statement by its tag (§4.4), for the applicant `id` of `period`. The
    /// proof shows knowledge of the key behind the tag at the applicant's recipient point and
    /// nothing else, and the notice may come from a fresh sender (§13 C6).
    pub fn withdraw(
        &mut self,
        period: &str,
        id: &G1,
        tag: &G1,
        proof: &FSProof<Fr>,
    ) -> Result<bool, ProtoError> {
        let hvk = self.hvk(period)?;
        let params = self.pcreds.params();
        let xq = self.pcreds.recipient_point(hvk.vk(), id)?;
        let id_text = point_text(id)?;
        let ctx = withdraw_context(&self.community, period, &id_text);
        if <Bk as Backend>::check_tag(params, tag, &xq, "t").is_err()
            || <Bk as Backend>::check_tag_proof(params, tag, &xq, &ctx, proof).is_err()
        {
            return Ok(false);
        }
        self.withdrawn.insert((id_text, point_text(tag)?));
        Ok(true)
    }
}

pub fn withdraw_context(community: &str, period: &str, id_text: &str) -> Vec<u8> {
    let mut ctx = b"openvtc/hidden-vetting/withdraw/0.2\0".to_vec();
    for part in [community, period, id_text] {
        ctx.extend((part.len() as u64).to_le_bytes());
        ctx.extend(part.as_bytes());
    }
    ctx
}
