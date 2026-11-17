//! Attestation tokens (design §5.1, with §13 C3 and C5): Pointcheval–Sanders blind signatures
//! on secret serials, made with the credential base `Σ-PS` of `pcreds`. No RSA, no new
//! dependency.
//!
//! - One token key `(tvk, tsk)` per live label, never a helper key: a `Σ-PS` signature on `s`
//!   under a period's helper key would be a credential of that period on the "`usk`" `s`, which
//!   the vetter knows. `Σ-PS` signs one scalar, the serial, so the label (`token/<period>`,
//!   `token/event/<id>`) is in the key and not in the message, as with the per-month token keys
//!   of design §5.1 (§13 C1 had moved it into a second message, which this `Σ-PS` does not
//!   have). Closing a label deletes its key.
//! - Drip: the vetter commits to fresh serials `C_i = g_1^{ρ_i} Y^{s_i}` (the `PrepareIssue` of
//!   `Σ-PS`) with a proof of knowledge of each opening, and the VTC blind-signs them one at a
//!   time under the label's key (C3), at most once per member, label and tick.
//! - Spend: the serial is revealed with a RE-RANDOMISED signature `(σ_1^r, σ_2^r)`, and the VTC
//!   checks it under the key of a live label and records the serial in that label's spent set.
//!   For a uniform `r ≠ 0`, `σ_1^r` is uniform in `G_1 \ {1}` and fixes `σ_2^r`, so the spend is
//!   independent of the blind signing that made the token, whose `C` hid `s` perfectly.

use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    sync::Mutex,
};

use ark_ec::PrimeGroup;
use ark_ff::{UniformRand, Zero};
use predicate_credential_system::{
    Error as PcsError,
    pcreds::pairing::{Base, G1Request, PS, PSPair, PSSigningKey, PSVerificationKey},
    serialization::to_bytes,
    sigma::{FSProof, GroupRelation, LinearEquation, fiat_shamir},
};
use rand::{CryptoRng, RngCore};

use crate::{
    ProtoError,
    scheme::{E, Fr, G1, scalar_text},
};

/// One committed serial with its proof of opening.
#[derive(Debug, Clone)]
pub struct TokenRequest {
    pub commitment: G1,
    pub opening_proof: FSProof<Fr>,
}

/// A spent token as the applicant forwards it: the revealed serial and a re-randomised
/// signature.
#[derive(Debug, Clone)]
pub struct TokenSpend {
    pub label: String,
    pub serial: Fr,
    pub shown: PSPair<E>,
}

/// What the spent set said about a spend.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpendOutcome {
    /// First time this serial was seen.
    Fresh,
    /// Seen before with the same `(id, tag)`: a resubmission after `requestMore`.
    AlreadyCounted,
    /// Seen before with another `(id, tag)`. Recorded as an anomaly, and the VTC cannot name
    /// who.
    DoubleSpend,
}

/// The statement `C = g_1^ρ Y^s` over the variables `(s, ρ)`, in that order.
fn opening_relation(tvk: &PSVerificationKey<E>, c: &G1) -> Result<GroupRelation<G1>, ProtoError> {
    let mut rel = GroupRelation::new();
    let s = rel.alloc_scalar();
    let rho = rel.alloc_scalar();
    rel.add_equation(LinearEquation::new(
        vec![(rho, G1::generator()), (s, tvk.y1)],
        *c,
    ))?;
    Ok(rel)
}

/// The context of an opening proof: the key, the label, who asks, for which tick, which slot.
/// A proof made for one request cannot be replayed into another.
fn opening_context(
    tvk: &PSVerificationKey<E>,
    label: &str,
    member: &str,
    tick: u32,
    index: usize,
    c: &G1,
) -> Result<Vec<u8>, ProtoError> {
    let mut ctx = b"openvtc/hidden-vetting/token-open/0.1\0".to_vec();
    for part in [
        to_bytes(tvk)?,
        label.as_bytes().to_vec(),
        member.as_bytes().to_vec(),
        tick.to_le_bytes().to_vec(),
        (index as u64).to_le_bytes().to_vec(),
        to_bytes(c)?,
    ] {
        ctx.extend((part.len() as u64).to_le_bytes());
        ctx.extend(part);
    }
    Ok(ctx)
}

/// A uniform nonzero scalar.
fn nonzero_scalar<R: RngCore + CryptoRng>(rng: &mut R) -> Fr {
    loop {
        let r = Fr::rand(rng);
        if !r.is_zero() {
            return r;
        }
    }
}

/// `Verify(tvk, s, σ')`, under the key of the spend's label.
pub fn verify_spend(tvk: &PSVerificationKey<E>, spend: &TokenSpend) -> bool {
    <PS as Base<E>>::verify(&(), tvk, &spend.serial, &spend.shown)
}

// -------------------------------------------------------------------------------------------
// VTC side
// -------------------------------------------------------------------------------------------

/// The key of one live label, with one lock per signing key: blind signing is sequential
/// (§13 C3).
struct LabelKey {
    tvk: PSVerificationKey<E>,
    tsk: PSSigningKey<E>,
    sign_lock: Mutex<()>,
}

#[derive(Default)]
pub struct TokenIssuer {
    keys: BTreeMap<String, LabelKey>,
    live: BTreeSet<String>,
    served: HashSet<(String, String, u32)>,
    /// label → serial → (id, tag)
    spent: HashMap<String, HashMap<String, (String, String)>>,
    pub anomalies: Vec<String>,
}

impl TokenIssuer {
    pub fn new() -> Self {
        Self::default()
    }

    /// The key of a live label, as the manifest would publish it.
    pub fn tvk(&self, label: &str) -> Option<&PSVerificationKey<E>> {
        self.keys.get(label).map(|k| &k.tvk)
    }

    pub fn live_labels(&self) -> &BTreeSet<String> {
        &self.live
    }

    /// Open a label under a fresh key. A label that is live already keeps its key.
    pub fn open_label<R: RngCore + CryptoRng>(&mut self, label: &str, rng: &mut R) {
        if self.keys.contains_key(label) {
            return;
        }
        let (tvk, tsk) = <PS as Base<E>>::keygen(&(), rng);
        self.keys.insert(
            label.to_string(),
            LabelKey {
                tvk,
                tsk,
                sign_lock: Mutex::new(()),
            },
        );
        self.live.insert(label.to_string());
    }

    /// Closing a label deletes its key, so that its tokens expire, and drops its spent set:
    /// nothing under it can be spent any more, so nothing needs remembering.
    pub fn close_label(&mut self, label: &str) {
        self.keys.remove(label);
        self.live.remove(label);
        self.spent.remove(label);
    }

    /// Blind-sign one tick's drip for `member` under `label`. The caller has checked that
    /// `member` holds a live grant (and, for an event label, belongs to the event group).
    pub fn issue<R: RngCore + CryptoRng>(
        &mut self,
        member: &str,
        tick: u32,
        label: &str,
        requests: &[TokenRequest],
        rng: &mut R,
    ) -> Result<Vec<PSPair<E>>, ProtoError> {
        let key = self
            .keys
            .get(label)
            .ok_or_else(|| ProtoError::LabelNotLive(label.to_string()))?;
        let served = (member.to_string(), label.to_string(), tick);
        if self.served.contains(&served) {
            return Err(ProtoError::AlreadyServedThisTick {
                member: member.to_string(),
                tick,
            });
        }
        for (i, req) in requests.iter().enumerate() {
            let rel = opening_relation(&key.tvk, &req.commitment)?;
            let ctx = opening_context(&key.tvk, label, member, tick, i, &req.commitment)?;
            if !fiat_shamir::verify(&rel, &ctx, &req.opening_proof) {
                return Err(ProtoError::BadOpeningProof(i));
            }
        }
        let pres = {
            let _guard = key.sign_lock.lock().expect("token signing lock");
            requests
                .iter()
                .map(|req| {
                    <PS as Base<E>>::blind_issue(&(), &key.tsk, &G1Request(req.commitment), rng)
                        .ok_or(ProtoError::Pcs(PcsError::InvalidIssuanceEncoding))
                })
                .collect::<Result<Vec<_>, _>>()?
        };
        self.served.insert(served);
        Ok(pres)
    }

    /// The signature check alone: valid under the key of a live label. Also what the
    /// applicant's engine runs on receipt (§13 C5), with the published key.
    pub fn signature_ok(&self, spend: &TokenSpend) -> bool {
        self.tvk(&spend.label)
            .is_some_and(|tvk| verify_spend(tvk, spend))
    }

    /// Record a verified spend in its label's spent set.
    pub fn record_spend(
        &mut self,
        spend: &TokenSpend,
        id: &str,
        tag: &str,
    ) -> Result<SpendOutcome, ProtoError> {
        let serial = scalar_text(&spend.serial)?;
        let set = self.spent.entry(spend.label.clone()).or_default();
        match set.get(&serial) {
            None => {
                set.insert(serial, (id.to_string(), tag.to_string()));
                Ok(SpendOutcome::Fresh)
            }
            Some((i, t)) if i == id && t == tag => Ok(SpendOutcome::AlreadyCounted),
            Some(_) => {
                self.anomalies.push(format!(
                    "serial {serial} under {} presented twice",
                    spend.label
                ));
                Ok(SpendOutcome::DoubleSpend)
            }
        }
    }
}

// -------------------------------------------------------------------------------------------
// Vetter side (inside the vetter's VTA: the PCS engine)
// -------------------------------------------------------------------------------------------

struct Held {
    label: String,
    serial: Fr,
    minted_tick: u32,
    cred: PSPair<E>,
    reserved: bool,
}

struct Pending {
    label: String,
    tick: u32,
    serial: Fr,
    rho: Fr,
}

/// The vetter's bucket.
#[derive(Default)]
pub struct TokenWallet {
    held: Vec<Held>,
    pending: Vec<Pending>,
}

/// A token set aside when a request is accepted (§5.2), identified by its serial.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Reservation {
    pub label: String,
    pub serial: Fr,
}

impl TokenWallet {
    pub fn new() -> Self {
        Self::default()
    }

    /// Draw `r` serials for one tick and commit to them under the label's key `tvk`.
    pub fn prepare<R: RngCore + CryptoRng>(
        &mut self,
        tvk: &PSVerificationKey<E>,
        label: &str,
        member: &str,
        tick: u32,
        r: usize,
        rng: &mut R,
    ) -> Result<Vec<TokenRequest>, ProtoError> {
        self.pending.clear();
        let mut out = Vec::with_capacity(r);
        for i in 0..r {
            let (serial, rho) = (Fr::rand(rng), Fr::rand(rng));
            let c = <PS as Base<E>>::prepare_issue(&(), tvk, &serial, &rho)
                .ok_or(ProtoError::Pcs(PcsError::InvalidIssuanceEncoding))?
                .0;
            let rel = opening_relation(tvk, &c)?;
            let ctx = opening_context(tvk, label, member, tick, i, &c)?;
            let opening_proof = fiat_shamir::prove(&rel, &[serial, rho], &ctx, rng)?;
            out.push(TokenRequest {
                commitment: c,
                opening_proof,
            });
            self.pending.push(Pending {
                label: label.to_string(),
                tick,
                serial,
                rho,
            });
        }
        Ok(out)
    }

    /// Unblind the answers and keep them, failing closed on any that does not verify.
    pub fn receive(
        &mut self,
        tvk: &PSVerificationKey<E>,
        pres: &[PSPair<E>],
    ) -> Result<(), ProtoError> {
        let pending = std::mem::take(&mut self.pending);
        if pending.len() != pres.len() {
            return Err(ProtoError::CountMismatch {
                statements: pending.len(),
                attestations: pres.len(),
            });
        }
        for (p, pre) in pending.into_iter().zip(pres) {
            let cred = <PS as Base<E>>::unblind(&(), tvk, &p.serial, pre, &p.rho)
                .ok_or(ProtoError::Pcs(PcsError::InvalidPreCredential))?;
            if !<PS as Base<E>>::verify(&(), tvk, &p.serial, &cred) {
                return Err(ProtoError::Pcs(PcsError::InvalidPreCredential));
            }
            self.held.push(Held {
                label: p.label,
                serial: p.serial,
                minted_tick: p.tick,
                cred,
                reserved: false,
            });
        }
        Ok(())
    }

    /// Tokens whose label is no longer live are gone (the FIFO of §5.1).
    pub fn expire(&mut self, live: &BTreeSet<String>) {
        self.held.retain(|h| live.contains(&h.label));
    }

    pub fn free(&self) -> usize {
        self.held.iter().filter(|h| !h.reserved).count()
    }

    pub fn held(&self) -> usize {
        self.held.len()
    }

    /// Reserve the NEWEST free token (§5.1 step 3), preferring `prefer_label` when given (an
    /// event label during its event).
    pub fn reserve(&mut self, prefer_label: Option<&str>) -> Option<Reservation> {
        let pick = self
            .held
            .iter_mut()
            .filter(|h| !h.reserved)
            .max_by_key(|h| (prefer_label.is_some_and(|l| l == h.label), h.minted_tick))?;
        pick.reserved = true;
        Some(Reservation {
            label: pick.label.clone(),
            serial: pick.serial,
        })
    }

    pub fn release(&mut self, r: &Reservation) {
        if let Some(h) = self.held.iter_mut().find(|h| h.serial == r.serial) {
            h.reserved = false;
        }
    }

    /// Spend a reservation: the token leaves the wallet as a re-randomised signature.
    pub fn spend<R: RngCore + CryptoRng>(
        &mut self,
        r: &Reservation,
        rng: &mut R,
    ) -> Result<TokenSpend, ProtoError> {
        let pos = self
            .held
            .iter()
            .position(|h| h.serial == r.serial && h.reserved)
            .ok_or(ProtoError::AtCapacity { available_from: 0 })?;
        let h = self.held.remove(pos);
        let k = nonzero_scalar(rng);
        Ok(TokenSpend {
            label: h.label,
            serial: h.serial,
            shown: PSPair {
                s1: h.cred.s1 * k,
                s2: h.cred.s2 * k,
            },
        })
    }
}
