//! The instantiation and the labels.
//!
//! - ONE deployment label per community, with no period in it: `pp` is fixed for the life of
//!   the community.
//! - ONE helper key per vetter period, the "epoch rotation of `(hvk, hsk)`" of design §4.3.
//!   §13 C1 replaced it with class labels `vetter/<period>` under one long-lived key, but
//!   `pcreds` has no class labels, and every identifier and tag is a function of the helper key
//!   (`x_0 = H_id(⟨hvk⟩)`, `x_Q = H_req(⟨pp, hvk, id_Q, j_Q⟩)`). So a period is a key: a vetter
//!   holds one credential per period, an applicant registers under one period, and the VTC
//!   evaluates a request under that period's key alone. The current and the previous period are
//!   live.
//! - Tokens use one key per label, `token/<period>` or `token/event/<id>`, never a helper key
//!   (module `token`).

use ark_bls12_381::{Bls12_381, G1Projective};
use predicate_credential_system::{
    hash::bls12_381::G1Hasher,
    kiprf::DDH,
    pcreds::{
        Protocol,
        pairing::{PS, PairingBackend},
    },
    serialization::{to_bytes, to_multibase},
};

use crate::ProtoError;

pub type E = Bls12_381;
pub type G1 = G1Projective;
pub type Fr = ark_bls12_381::Fr;
/// `Tag_DDH` over `G_1`: identifiers and attestation tags.
pub type TagDdh = DDH<G1, G1Hasher>;
/// `Σ-PS` with `Tag_DDH` over BLS12-381: the paper's main pairing instantiation. The tokens
/// reuse its credential base `Σ-PS`.
pub type Bk = PairingBackend<E, PS, TagDdh>;
/// `Π_PCreds` for [`Bk`], under the community's deployment label.
pub type Pcreds = Protocol<Bk>;

pub fn deployment_label(community: &str) -> Vec<u8> {
    format!("{community}#vetting-pcs").into_bytes()
}

pub fn monthly_token_label(period: &str) -> String {
    format!("token/{period}")
}

pub fn event_token_label(event_id: &str) -> String {
    format!("token/event/{event_id}")
}

/// Multibase text of a group element (identifiers, tags).
pub fn point_text(p: &G1) -> Result<String, ProtoError> {
    Ok(to_multibase(&to_bytes(p)?))
}

/// Multibase text of a scalar (serials).
pub fn scalar_text(s: &Fr) -> Result<String, ProtoError> {
    Ok(to_multibase(&to_bytes(s)?))
}
