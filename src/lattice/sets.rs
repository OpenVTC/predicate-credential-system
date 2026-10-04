//! The parameter sets of Jali for the relations of the lattice instantiation, embedded in the
//! crate and pinned by their SHA-256 digests.
//!
//! | set | relation | id | estimated proof bytes | longest accepted proof |
//! |---|---|---|---|---|
//! | [`ATT_JSON`] | `R_att` (attestations) | [`ATT_ID`] | 85,608 | [`ATT_PROOF_MAX_BYTES`] = 171,216 |
//! | [`ISSUE_JSON`] | `R_issue` under `ctx_0` (`Prove`, `VerifyProof`) | [`ISSUE_ID`] | 42,912 | [`ISSUE_PROOF_MAX_BYTES`] = 85,824 |
//! | [`ISSUE_ROOT_JSON`] | `R_issue` under `ctx_root` (root requests) | [`ISSUE_ROOT_ID`] | 42,912 | [`ISSUE_PROOF_MAX_BYTES`] |
//!
//! Provenance: the 128-bit sets of tag set R at proof degree 128 (`(γ, p, q_t, m) = (15, 2^16,
//! 983,040, 168)`, `β_r = 1`), derived by Jali's parameter tool for exactly the statement layouts
//! of [`crate::pcs::lattice`] (block names and order, exact norms, `s` in the BDLOP part of the
//! commitment for `R_att`, `e` as subring blocks of the proof degree), gated at an estimator
//! target of 128 bits, with proof moduli proven prime in Sage, and copied byte for byte from the
//! tool's output. The choice of `s` in BDLOP is recorded only in the tool's derivation report
//! (`placement.chosen.bdlop = ["s"]`), not in the set: the statement builder hard-codes it. The
//! derivation reports are not part of this repository.
//!
//! `issue` and `issue-root` are twins that differ only in `id` and `estimator`. Both strings
//! enter Jali's transcript, so a root request and an issuance proof are separated by the
//! parameter set as well as by their contexts.
//!
//! Loading runs Jali's strict JSON decoding and its complete `check()` (feature `jali/serde`,
//! switched on by `lattice`), after comparing the embedded bytes with their pinned digests.

use jali::params::TboxParams;
use sha2::{Digest, Sha256};

use super::PROOF_DEGREE;
use crate::error::Error;

/// The `id` of the set for `R_att`.
pub const ATT_ID: &str = "pcs128-g15-k16-mdef-d128-att-beta439";
/// The `id` of the set for `R_issue` under `ctx_0`.
pub const ISSUE_ID: &str = "pcs128-g15-k16-mdef-d128-issue-beta439";
/// The `id` of the set for `R_issue` under `ctx_root`.
pub const ISSUE_ROOT_ID: &str = "pcs128-g15-k16-mdef-d128-issue-root-beta439";

/// The longest Jali proof for `R_att` (an attestation's $`\pi_j`$) that a decoder or a verifier
/// of this crate accepts: twice the estimated proof size of [`ATT_JSON`] (85,608 bytes). Honest
/// proofs have 0.95 to 1 times the estimate (measured over 60 proofs); the bound spares a
/// verifier from decoding and hashing megabytes of garbage before Jali refuses them (Jali's own
/// decoder reads up to 16 MiB). It changes no verdict on an honest proof.
pub const ATT_PROOF_MAX_BYTES: usize = 2 * 85_608;
/// The longest Jali proof for `R_issue` (the $`\pi_0`$ of an issuance proof or of a root
/// request) that a decoder or a verifier of this crate accepts: twice the estimated proof size
/// of [`ISSUE_JSON`] and [`ISSUE_ROOT_JSON`] (42,912 bytes); as [`ATT_PROOF_MAX_BYTES`].
pub const ISSUE_PROOF_MAX_BYTES: usize = 2 * 42_912;

/// `params-att-beta439.json`, byte for byte.
pub const ATT_JSON: &str = include_str!("sets/params-att-beta439.json");
/// `params-issue-beta439.json`, byte for byte.
pub const ISSUE_JSON: &str = include_str!("sets/params-issue-beta439.json");
/// `params-issue-root-beta439.json`, byte for byte.
pub const ISSUE_ROOT_JSON: &str = include_str!("sets/params-issue-root-beta439.json");

/// SHA-256 of [`ATT_JSON`]: `208ef25c…ad98`.
pub const ATT_SHA256: [u8; 32] = [
    0x20, 0x8e, 0xf2, 0x5c, 0x45, 0x97, 0x96, 0x1f, 0xb3, 0x73, 0x3e, 0xc9, 0x14, 0xa2, 0x25, 0xc5,
    0xbf, 0x7b, 0x19, 0x2a, 0x1b, 0xdc, 0x78, 0xd7, 0xc9, 0xcb, 0x0e, 0xea, 0x62, 0x03, 0xad, 0x98,
];
/// SHA-256 of [`ISSUE_JSON`]: `0322b83f…8c75`.
pub const ISSUE_SHA256: [u8; 32] = [
    0x03, 0x22, 0xb8, 0x3f, 0x28, 0xa3, 0xfe, 0xd4, 0x4a, 0xcb, 0xad, 0xf9, 0xab, 0xd0, 0xd9, 0xa1,
    0x77, 0x4a, 0x4a, 0x69, 0x66, 0xec, 0x6d, 0xbf, 0x94, 0x4a, 0x14, 0xcb, 0x99, 0xba, 0x8c, 0x75,
];
/// SHA-256 of [`ISSUE_ROOT_JSON`]: `20aafab6…2dea`.
pub const ISSUE_ROOT_SHA256: [u8; 32] = [
    0x20, 0xaa, 0xfa, 0xb6, 0x14, 0xf2, 0x19, 0x89, 0x1b, 0xd5, 0x6f, 0x9a, 0x70, 0x5d, 0x48, 0xf2,
    0x5a, 0xb0, 0x30, 0xf4, 0xa8, 0x29, 0x85, 0x7f, 0x21, 0x90, 0x42, 0x11, 0xe8, 0x05, 0x2d, 0xea,
];

/// The three checked parameter sets of the instantiation.
#[derive(Clone, Debug, PartialEq)]
pub struct ParameterSets {
    /// `R_att`.
    pub att: TboxParams,
    /// `R_issue` under `ctx_0`.
    pub issue: TboxParams,
    /// `R_issue` under `ctx_root`.
    pub issue_root: TboxParams,
}

impl ParameterSets {
    /// Loads and checks the embedded sets: digest pins, Jali's strict decoding and `check()`, the
    /// expected `id` and the proof degree. About a millisecond; run once per instance.
    ///
    /// # Errors
    /// [`Error::LatticeBackend`] if an embedded file does not match its pin or is refused by
    /// Jali (a build that altered the files; never for this crate as published).
    pub fn load() -> Result<Self, Error> {
        Ok(Self {
            att: load(ATT_JSON, &ATT_SHA256, ATT_ID)?,
            issue: load(ISSUE_JSON, &ISSUE_SHA256, ISSUE_ID)?,
            issue_root: load(ISSUE_ROOT_JSON, &ISSUE_ROOT_SHA256, ISSUE_ROOT_ID)?,
        })
    }
}

fn load(json: &str, sha256: &[u8; 32], id: &str) -> Result<TboxParams, Error> {
    if Sha256::digest(json.as_bytes()).as_slice() != sha256 {
        return Err(Error::LatticeBackend(format!(
            "parameter set {id}: the embedded file does not match its pinned SHA-256"
        )));
    }
    let params = TboxParams::from_json(json)
        .map_err(|e| Error::LatticeBackend(format!("parameter set {id}: {e}")))?;
    if params.id != id || params.degree != PROOF_DEGREE {
        return Err(Error::LatticeBackend(format!(
            "parameter set {id}: unexpected id or proof degree"
        )));
    }
    Ok(params)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_embedded_sets_load_and_check() {
        let sets = ParameterSets::load().unwrap();
        assert_eq!(sets.att.id, ATT_ID);
        assert_eq!(sets.issue.id, ISSUE_ID);
        assert_eq!(sets.issue_root.id, ISSUE_ROOT_ID);
        // the documented estimates, and the proof bounds at twice them
        assert_eq!(sets.att.check().unwrap().estimated_proof_bytes, 85_608);
        assert_eq!(sets.issue.check().unwrap().estimated_proof_bytes, 42_912);
        assert_eq!(
            sets.issue_root.check().unwrap().estimated_proof_bytes,
            42_912
        );
        assert_eq!(
            ATT_PROOF_MAX_BYTES,
            2 * sets.att.check().unwrap().estimated_proof_bytes
        );
        assert_eq!(
            ISSUE_PROOF_MAX_BYTES,
            2 * sets.issue.check().unwrap().estimated_proof_bytes
        );
        // R_att: one exact l2 block (s) of 16 proof-ring rows at ⌊β_s²⌋
        assert_eq!(sets.att.l2_bounds_squared, vec![super::super::S_BOUND]);
        assert_eq!(sets.att.l2_rows, vec![16]);
    }

    /// `issue` and `issue-root` differ in `id` and `estimator` only.
    #[test]
    fn issue_and_issue_root_are_twins() {
        let sets = ParameterSets::load().unwrap();
        let mut root = sets.issue_root.clone();
        assert_ne!(root, sets.issue);
        root.id = sets.issue.id.clone();
        root.estimator = sets.issue.estimator.clone();
        assert_eq!(root, sets.issue);
    }

    #[test]
    fn a_changed_file_is_refused() {
        let changed = ATT_JSON.replacen("\"m2\": 66", "\"m2\": 67", 1);
        assert_ne!(changed, ATT_JSON);
        assert!(matches!(
            load(&changed, &ATT_SHA256, ATT_ID),
            Err(Error::LatticeBackend(_))
        ));
        assert!(matches!(
            load(ATT_JSON, &ATT_SHA256, ISSUE_ID),
            Err(Error::LatticeBackend(_))
        ));
    }
}
