//! The parameter sets of Jali for the four relations of the lattice backend
//! ([`crate::pcreds::lattice`]) and their extraction sets, embedded in the crate and pinned by
//! their SHA-256 digests.
//!
//! | set | relation (proof) | id | proof bytes | longest accepted proof, plain build |
//! |---|---|---|---|---|
//! | [`TAG_JSON`] | `R_Tag` (`π_id`) | [`TAG_ID`] | 29,112 | 58,224 |
//! | [`ATT_JSON`] | `R_att` (`π_att`) | [`ATT_ID`] | 90,168 | 180,336 |
//! | [`ISS_JSON`] | `R_iss` (`π_iss`) | [`ISS_ID`] | 46,152 | 92,304 |
//! | [`POSSESS_JSON`] | `R_Possess` (`π_prove`) | [`POSSESS_ID`] | 84,856 | 169,712 |
//!
//! Since Jali 0.2.0 every field of a proof has a fixed width, so every proof of a set has the
//! set's `estimated_proof_bytes`, the column above, exactly. Jali 0.1 estimated these lengths
//! (29,168, 90,216, 46,208 and 84,904 bytes) and its variable-length codes stayed below them.
//!
//! # Extraction sets
//!
//! In the default build ([`STRAIGHT_LINE`]) the backend
//! proves in Jali's straight-line extractable mode, which takes an extraction set besides each
//! parameter set: the rank $`n'`$ and the modulus $`q'`$ of the LinHC commitment that commits to
//! the $`m'`$ polynomials of the final opening's witness. Both builds load and check them. Only
//! the extractable build proves with them, and only its `pp` covers their pins
//! ([`EXTRACTION_PINS`]).
//!
//! | extraction set | of | $`n'`$ | $`q'`$ | $`m'`$ | LinHC part | proof bytes | longest accepted proof, extractable build |
//! |---|---|---|---|---|---|---|---|
//! | [`TAG_EXTRACTION_JSON`] | [`TAG_JSON`] | 22 | ≈ 2^57.29 | 52 | [`TAG_LINHC_BYTES`] = 140,864 | 169,976 | 339,952 |
//! | [`ATT_EXTRACTION_JSON`] | [`ATT_JSON`] | 24 | ≈ 2^61.74 | 149 | [`ATT_LINHC_BYTES`] = 414,112 | 504,280 | 1,008,560 |
//! | [`ISS_EXTRACTION_JSON`] | [`ISS_JSON`] | 23 | ≈ 2^60.82 | 101 | [`ISS_LINHC_BYTES`] = 279,952 | 326,104 | 652,208 |
//! | [`POSSESS_EXTRACTION_JSON`] | [`POSSESS_JSON`] | 23 | ≈ 2^61.65 | 139 | [`POSSESS_LINHC_BYTES`] = 386,544 | 471,400 | 942,800 |
//!
//! The LinHC part of an extractable proof is $`t_1`$ and $`t_2`$, $`2m'd\lceil\log_2 q'\rceil`$
//! bits, and $`z'`$, $`(n' + 2m')d`$ coefficients of $`t'+4`$ bits each in Jali's fixed-width
//! code, so the whole proof has `ExtractionParams::proof_bytes` exactly
//! (`tools/lattice/sets/extraction_sizes.py` computes the same lengths). The bound of a proof is
//! twice the size of a proof of its build ([`TAG_PROOF_MAX_BYTES`] and the others).
//!
//! Provenance: Jali's parameter tool (`tools/params/lnp_params.py extraction` at Jali `976c9bd`,
//! the release 0.1.1) derived each extraction set from its parameter set, as the least rank whose
//! LinHC MLWE estimate meets the set's own policy (uSVP block size at least 439, 443 for `tag`)
//! at the modulus that rank gives. `att` asks for 444: at 439 its rank is 23, whose cheapest
//! attack in lattice-estimator's rough mode is the dual hybrid at 2^127.9. With it, the rough mode
//! reaches 128 bits on the commitment's hiding instance of every set (2^132.9, 2^135.5, 2^130.5
//! and 2^128.2), and the instance of keys with a trapdoor costs far more
//! (`tools/lattice/extraction_estimate.sage`, lattice-estimator at the commit the tool pins).
//! The crate derives the modulus again from the parameter set and the rank, and refuses a set
//! whose modulus differs.
//!
//! Every set is for tag set R at proof degree 128 (`(γ, p, q_t, m) = (15, 2^16, 983,040, 168)`),
//! the issuance randomness $`x_0`$ of $`\ell_r = 3`$ ternary elements, and exactly the statement
//! layout of its relation (block names and order, exact norms, the two-sided bound
//! $`1\le\|s\|^2\le\lfloor\beta_s^2\rfloor`$, the placement of `s`, `e` as subring blocks of
//! the proof degree): Jali's `compile` refuses any other.
//!
//! Provenance: every set was derived by Jali's parameter tool (`tools/params/lnp_params.py
//! derive` at Jali `5ee737b`, whose library code the pinned release 0.1.0 has) from the requests
//! under `tools/lattice/sets/`, which export each statement at its worst-case public data; the
//! reports are kept next to them, the commands are in its README. `tag` was first derived at Jali
//! `0cd24f38`, for the first port, and `5ee737b` derives it again byte for byte. Each set was
//! refused unless
//!   lattice-estimator's rough mode reached 128 bits on both its MLWE and its MSIS instance
//!   (`--estimator-target 128`, lattice-estimator at the commit the tool pins), and its proof
//!   modulus was proven prime in Sage (`Integer.is_prime(proof=True)`). The policy is block
//!   sizes of at least 439 (core-SVP 128 bits), except for `tag`, whose request asks for 443:
//!   at 439 its smallest MLWE rank misses the estimator gate (the dual-hybrid attack, 2^127.3).
//!
//! The `id` and `estimator` strings of a set, and every field of an extraction set, enter Jali's
//! transcript.
//!
//! Loading runs Jali's strict JSON decoding and its complete `check()` (feature `jali/serde`,
//! switched on by `lattice`), for an extraction set against its parameter set, after comparing
//! the embedded bytes with their pinned digests.

use jali::params::{ExtractionParams, OracleModel, TboxParams};
use sha2::{Digest, Sha256};

use super::{PROOF_DEGREE, STRAIGHT_LINE};
use crate::{error::Error, pcreds::ProofKind};

/// The `id` of the set for `R_Tag`.
pub const TAG_ID: &str = "pcreds128-g15-k16-mdef-d128-tag-beta443";
/// The `id` of the set for `R_att`.
pub const ATT_ID: &str = "pcreds128-g15-k16-mdef-d128-lr3-att-beta439";
/// The `id` of the set for `R_iss`.
pub const ISS_ID: &str = "pcreds128-g15-k16-mdef-d128-lr3-iss-beta439";
/// The `id` of the set for `R_Possess`.
pub const POSSESS_ID: &str = "pcreds128-g15-k16-mdef-d128-lr3-possess-beta439";

/// The bytes that the LinHC part adds to an extractable proof for `R_Tag`, exactly, as in the
/// module docs. Only the extractable build adds it ([`TAG_PROOF_MAX_BYTES`]).
pub const TAG_LINHC_BYTES: usize = 140_864;
/// The bytes that the LinHC part adds to an extractable proof for `R_att`, as
/// [`TAG_LINHC_BYTES`] for `R_Tag`.
pub const ATT_LINHC_BYTES: usize = 414_112;
/// The bytes that the LinHC part adds to an extractable proof for `R_iss`, as
/// [`TAG_LINHC_BYTES`] for `R_Tag`.
pub const ISS_LINHC_BYTES: usize = 279_952;
/// The bytes that the LinHC part adds to an extractable proof for `R_Possess`, as
/// [`TAG_LINHC_BYTES`] for `R_Tag`.
pub const POSSESS_LINHC_BYTES: usize = 386_544;

/// Twice the size of a proof of this build: of the plain proof, `plain`, and in the extractable
/// build ([`STRAIGHT_LINE`]) also of its LinHC part, `linhc`.
const fn bound(plain: usize, linhc: usize) -> usize {
    2 * (plain + if STRAIGHT_LINE { linhc } else { 0 })
}

/// The longest Jali proof for `R_Tag` (an identifier proof `π_id`) that a decoder or a verifier
/// of the lattice backend accepts: twice the proof size of [`TAG_JSON`] (58,224 bytes), in the
/// extractable build of the extractable proof with [`TAG_EXTRACTION_JSON`] (339,952 bytes).
/// Every honest proof has half the bound exactly. The bound spares a verifier from
/// decoding and hashing megabytes of garbage before Jali refuses them (Jali's own decoder reads
/// up to 16 MiB), and it changes no verdict on an honest proof.
pub const TAG_PROOF_MAX_BYTES: usize = bound(29_112, TAG_LINHC_BYTES);
/// The longest Jali proof for `R_att` (an attestation proof `π_att`): twice the proof size of
/// [`ATT_JSON`] (180,336 bytes), in the extractable build of the extractable proof (1,008,560
/// bytes), as [`TAG_PROOF_MAX_BYTES`] for `R_Tag`.
pub const ATT_PROOF_MAX_BYTES: usize = bound(90_168, ATT_LINHC_BYTES);
/// The longest Jali proof for `R_iss` (an issuance proof `π_iss`): twice the proof size of
/// [`ISS_JSON`] (92,304 bytes), in the extractable build of the extractable proof (652,208
/// bytes), as [`TAG_PROOF_MAX_BYTES`] for `R_Tag`.
pub const ISS_PROOF_MAX_BYTES: usize = bound(46_152, ISS_LINHC_BYTES);
/// The longest Jali proof for `R_Possess` (a membership proof `π_prove`): twice the proof size
/// of [`POSSESS_JSON`] (169,712 bytes), in the extractable build of the extractable proof
/// (942,800 bytes), as [`TAG_PROOF_MAX_BYTES`] for `R_Tag`.
pub const POSSESS_PROOF_MAX_BYTES: usize = bound(84_856, POSSESS_LINHC_BYTES);

/// `params-tag-beta443.json`, byte for byte.
pub const TAG_JSON: &str = include_str!("sets/params-tag-beta443.json");
/// `params-att-lr3-beta439.json`, byte for byte.
pub const ATT_JSON: &str = include_str!("sets/params-att-lr3-beta439.json");
/// `params-iss-lr3-beta439.json`, byte for byte.
pub const ISS_JSON: &str = include_str!("sets/params-iss-lr3-beta439.json");
/// `params-possess-lr3-beta439.json`, byte for byte.
pub const POSSESS_JSON: &str = include_str!("sets/params-possess-lr3-beta439.json");

/// SHA-256 of [`TAG_JSON`]: `aa598dab…b430`.
pub const TAG_SHA256: [u8; 32] = [
    0xaa, 0x59, 0x8d, 0xab, 0xcb, 0x2b, 0xba, 0xc3, 0xbb, 0x97, 0x6c, 0x05, 0x8a, 0x75, 0xe4, 0x8c,
    0x50, 0xc0, 0x91, 0x84, 0x67, 0xee, 0x93, 0x20, 0x70, 0xa8, 0xac, 0xc5, 0x2c, 0x45, 0xb4, 0x30,
];
/// SHA-256 of [`ATT_JSON`]: `b7f5fd92…c736`.
pub const ATT_SHA256: [u8; 32] = [
    0xb7, 0xf5, 0xfd, 0x92, 0x3c, 0xcb, 0x44, 0x62, 0x3a, 0xac, 0x5b, 0x95, 0x04, 0x1e, 0x4a, 0x02,
    0x44, 0x09, 0x79, 0xaa, 0xf5, 0x4c, 0x96, 0xe5, 0x0e, 0x08, 0x02, 0xca, 0x1a, 0xa1, 0xc7, 0x36,
];
/// SHA-256 of [`ISS_JSON`]: `99497d95…1db3`.
pub const ISS_SHA256: [u8; 32] = [
    0x99, 0x49, 0x7d, 0x95, 0x5a, 0xe1, 0xb9, 0x25, 0x2b, 0x3f, 0xeb, 0xe7, 0xe3, 0x31, 0xa8, 0xde,
    0xf5, 0x2e, 0x18, 0xf0, 0x61, 0xa4, 0xa1, 0x07, 0x45, 0xb7, 0xf6, 0xd4, 0xef, 0xa2, 0x1d, 0xb3,
];
/// SHA-256 of [`POSSESS_JSON`]: `18ad0181…df45`.
pub const POSSESS_SHA256: [u8; 32] = [
    0x18, 0xad, 0x01, 0x81, 0x34, 0x98, 0x86, 0x3c, 0xbf, 0x6c, 0x86, 0x72, 0xa4, 0xa1, 0xb7, 0x2f,
    0x36, 0x85, 0x17, 0xc2, 0xbf, 0x42, 0xbb, 0x57, 0xae, 0x8e, 0xae, 0x58, 0x90, 0xcc, 0xdf, 0x45,
];

/// The four pins in the order `tag`, `att`, `iss`, `possess`: what the digest of the lattice
/// `pp` covers of the sets.
pub const PINS: [[u8; 32]; 4] = [TAG_SHA256, ATT_SHA256, ISS_SHA256, POSSESS_SHA256];

/// `extraction-tag-beta443.json`, byte for byte: the extraction set of [`TAG_JSON`].
pub const TAG_EXTRACTION_JSON: &str = include_str!("sets/extraction-tag-beta443.json");
/// `extraction-att-lr3-beta439.json`, byte for byte: the extraction set of [`ATT_JSON`].
pub const ATT_EXTRACTION_JSON: &str = include_str!("sets/extraction-att-lr3-beta439.json");
/// `extraction-iss-lr3-beta439.json`, byte for byte: the extraction set of [`ISS_JSON`].
pub const ISS_EXTRACTION_JSON: &str = include_str!("sets/extraction-iss-lr3-beta439.json");
/// `extraction-possess-lr3-beta439.json`, byte for byte: the extraction set of
/// [`POSSESS_JSON`].
pub const POSSESS_EXTRACTION_JSON: &str = include_str!("sets/extraction-possess-lr3-beta439.json");

/// SHA-256 of [`TAG_EXTRACTION_JSON`]: `355b5f5a…187a`.
pub const TAG_EXTRACTION_SHA256: [u8; 32] = [
    0x35, 0x5b, 0x5f, 0x5a, 0x8c, 0x9e, 0x48, 0xee, 0xed, 0x19, 0xe3, 0xae, 0x8d, 0x30, 0x84, 0x16,
    0x1f, 0x51, 0x9f, 0x07, 0x08, 0xd5, 0xfa, 0x53, 0x3b, 0x97, 0x86, 0x25, 0xe7, 0x2d, 0x18, 0x7a,
];
/// SHA-256 of [`ATT_EXTRACTION_JSON`]: `796c2cd6…9e4b`.
pub const ATT_EXTRACTION_SHA256: [u8; 32] = [
    0x79, 0x6c, 0x2c, 0xd6, 0xc4, 0x79, 0x59, 0xc3, 0x3d, 0x71, 0xfa, 0x70, 0x56, 0x76, 0xf9, 0x9b,
    0xfe, 0x0d, 0x46, 0x69, 0x7c, 0x8f, 0x0e, 0x15, 0xbc, 0x4d, 0xab, 0xcb, 0xb3, 0x80, 0x9e, 0x4b,
];
/// SHA-256 of [`ISS_EXTRACTION_JSON`]: `d51e5f21…957b`.
pub const ISS_EXTRACTION_SHA256: [u8; 32] = [
    0xd5, 0x1e, 0x5f, 0x21, 0x73, 0xa1, 0x84, 0xa7, 0x7b, 0x9f, 0x9e, 0xbc, 0x74, 0x57, 0xfa, 0xfe,
    0xe6, 0xaf, 0xe6, 0x37, 0xff, 0xe3, 0x45, 0x24, 0x44, 0x92, 0x15, 0x00, 0xfb, 0xec, 0x95, 0x7b,
];
/// SHA-256 of [`POSSESS_EXTRACTION_JSON`]: `5c647553…8254`.
pub const POSSESS_EXTRACTION_SHA256: [u8; 32] = [
    0x5c, 0x64, 0x75, 0x53, 0xe8, 0xa7, 0x3c, 0x9c, 0x86, 0x96, 0x46, 0xcc, 0x3d, 0x6f, 0x59, 0xbc,
    0x35, 0xf6, 0xcd, 0x16, 0x8d, 0x4f, 0xc1, 0xde, 0x51, 0x8d, 0x8b, 0x99, 0x04, 0xff, 0x82, 0x54,
];

/// The four pins of the extraction sets in the order `tag`, `att`, `iss`, `possess`: what the
/// digest of the lattice `pp` covers of them in the extractable build ([`STRAIGHT_LINE`]).
pub const EXTRACTION_PINS: [[u8; 32]; 4] = [
    TAG_EXTRACTION_SHA256,
    ATT_EXTRACTION_SHA256,
    ISS_EXTRACTION_SHA256,
    POSSESS_EXTRACTION_SHA256,
];

/// The four checked parameter sets of the lattice backend, with their extraction sets.
#[derive(Clone, Debug, PartialEq)]
pub struct ParameterSets {
    /// `R_Tag`.
    pub tag: TboxParams,
    /// `R_att`.
    pub att: TboxParams,
    /// `R_iss`.
    pub iss: TboxParams,
    /// `R_Possess`.
    pub possess: TboxParams,
    /// The extraction sets of the four, which the extractable build proves with.
    pub extraction: ExtractionSets,
}

/// The four checked extraction sets, each checked against its parameter set by Jali.
#[derive(Clone, Debug, PartialEq)]
pub struct ExtractionSets {
    /// Of [`ParameterSets::tag`].
    pub tag: ExtractionParams,
    /// Of [`ParameterSets::att`].
    pub att: ExtractionParams,
    /// Of [`ParameterSets::iss`].
    pub iss: ExtractionParams,
    /// Of [`ParameterSets::possess`].
    pub possess: ExtractionParams,
}

/// What the argument system takes for the proofs of one relation: its parameter set, and the
/// extraction set that the extractable build ([`STRAIGHT_LINE`]) proves with besides it.
#[derive(Clone, Copy, Debug)]
pub struct ProofSet<'a> {
    /// The parameter set.
    pub params: &'a TboxParams,
    /// Its extraction set.
    pub extraction: &'a ExtractionParams,
}

impl ParameterSets {
    /// Loads and checks the embedded sets: digest pins, Jali's strict decoding and `check()`, the
    /// expected `id` and the proof degree, and for every extraction set its pin, Jali's strict
    /// decoding, its check against its parameter set (the moduli that its rank gives) and the
    /// classical random-oracle model. A few milliseconds. Run it once per deployment.
    ///
    /// # Errors
    /// [`Error::LatticeBackend`] if an embedded file does not match its pin or is refused by
    /// Jali (a build that altered the files, never this crate as written).
    pub fn load() -> Result<Self, Error> {
        let tag = load(TAG_JSON, &TAG_SHA256, TAG_ID)?;
        let att = load(ATT_JSON, &ATT_SHA256, ATT_ID)?;
        let iss = load(ISS_JSON, &ISS_SHA256, ISS_ID)?;
        let possess = load(POSSESS_JSON, &POSSESS_SHA256, POSSESS_ID)?;
        let extraction = ExtractionSets {
            tag: load_extraction(TAG_EXTRACTION_JSON, &TAG_EXTRACTION_SHA256, &tag)?,
            att: load_extraction(ATT_EXTRACTION_JSON, &ATT_EXTRACTION_SHA256, &att)?,
            iss: load_extraction(ISS_EXTRACTION_JSON, &ISS_EXTRACTION_SHA256, &iss)?,
            possess: load_extraction(
                POSSESS_EXTRACTION_JSON,
                &POSSESS_EXTRACTION_SHA256,
                &possess,
            )?,
        };
        Ok(Self {
            tag,
            att,
            iss,
            possess,
            extraction,
        })
    }

    /// The sets of the proofs of `kind`.
    #[must_use]
    pub fn of(&self, kind: ProofKind) -> ProofSet<'_> {
        let (params, extraction) = match kind {
            ProofKind::Identifier => (&self.tag, &self.extraction.tag),
            ProofKind::Attestation => (&self.att, &self.extraction.att),
            ProofKind::Issuance => (&self.iss, &self.extraction.iss),
            ProofKind::Possession => (&self.possess, &self.extraction.possess),
        };
        ProofSet { params, extraction }
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

fn load_extraction(
    json: &str,
    sha256: &[u8; 32],
    params: &TboxParams,
) -> Result<ExtractionParams, Error> {
    let id = &params.id;
    if Sha256::digest(json.as_bytes()).as_slice() != sha256 {
        return Err(Error::LatticeBackend(format!(
            "extraction set of {id}: the embedded file does not match its pinned SHA-256"
        )));
    }
    let extraction = ExtractionParams::from_json(json, params)
        .map_err(|e| Error::LatticeBackend(format!("extraction set of {id}: {e}")))?;
    if extraction.model != OracleModel::Rom {
        return Err(Error::LatticeBackend(format!(
            "extraction set of {id}: not the classical random-oracle model"
        )));
    }
    Ok(extraction)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_embedded_sets_load_and_check() {
        let sets = ParameterSets::load().unwrap();
        assert_eq!(sets.tag.id, TAG_ID);
        assert_eq!(sets.att.id, ATT_ID);
        assert_eq!(sets.iss.id, ISS_ID);
        assert_eq!(sets.possess.id, POSSESS_ID);
        // the documented proof sizes, exact since Jali 0.2.0, and the proof bounds at twice them:
        // of the plain proof, and in the extractable build of the plain proof with its LinHC part
        for (set, estimate, linhc, max) in [
            (&sets.tag, 29_112, TAG_LINHC_BYTES, TAG_PROOF_MAX_BYTES),
            (&sets.att, 90_168, ATT_LINHC_BYTES, ATT_PROOF_MAX_BYTES),
            (&sets.iss, 46_152, ISS_LINHC_BYTES, ISS_PROOF_MAX_BYTES),
            (
                &sets.possess,
                84_856,
                POSSESS_LINHC_BYTES,
                POSSESS_PROOF_MAX_BYTES,
            ),
        ] {
            assert_eq!(
                set.check().unwrap().estimated_proof_bytes,
                estimate,
                "{}",
                set.id
            );
            if STRAIGHT_LINE {
                assert_eq!(max, 2 * (estimate + linhc));
            } else {
                assert_eq!(max, 2 * estimate);
            }
        }
        // the documented extraction sets: rank, modulus and model, each checked against its set
        for (kind, rank, modulus) in [
            (ProofKind::Identifier, 22, 176_371_585_881_524_249u128),
            (ProofKind::Attestation, 24, 3_857_128_248_596_167_189),
            (ProofKind::Issuance, 23, 2_036_323_750_691_491_993),
            (ProofKind::Possession, 23, 3_606_003_552_620_118_107),
        ] {
            let ProofSet { params, extraction } = sets.of(kind);
            assert_eq!(
                (extraction.rank, extraction.modulus),
                (rank, modulus),
                "{kind:?}"
            );
            assert_eq!(extraction.model, OracleModel::Rom);
            assert_eq!(extraction.check(params), Ok(()));
            // the LinHC part: the extractable proof's exact size less the plain proof's
            let linhc = match kind {
                ProofKind::Identifier => TAG_LINHC_BYTES,
                ProofKind::Attestation => ATT_LINHC_BYTES,
                ProofKind::Issuance => ISS_LINHC_BYTES,
                ProofKind::Possession => POSSESS_LINHC_BYTES,
            };
            assert_eq!(
                extraction.proof_bytes(params),
                Ok(params.check().unwrap().estimated_proof_bytes + linhc),
                "{kind:?}"
            );
            assert_eq!(
                ExtractionParams::modulus_for(params, rank),
                Ok(modulus),
                "{kind:?}"
            );
        }
        // R_att and R_Possess: one exact l2 block (s) of 16 proof-ring rows at ⌊β_s²⌋
        for set in [&sets.att, &sets.possess] {
            assert_eq!(set.l2_bounds_squared, vec![super::super::S_BOUND]);
            assert_eq!(set.l2_rows, vec![16]);
        }
        assert!(sets.tag.l2_rows.is_empty() && sets.iss.l2_rows.is_empty());
    }

    #[test]
    fn a_changed_file_is_refused() {
        let changed = ATT_JSON.replacen("\"m2\": 65", "\"m2\": 66", 1);
        assert_ne!(changed, ATT_JSON);
        assert!(matches!(
            load(&changed, &ATT_SHA256, ATT_ID),
            Err(Error::LatticeBackend(_))
        ));
        assert!(matches!(
            load(ATT_JSON, &ATT_SHA256, ISS_ID),
            Err(Error::LatticeBackend(_))
        ));
        assert!(matches!(
            load(TAG_JSON, &ATT_SHA256, TAG_ID),
            Err(Error::LatticeBackend(_))
        ));
    }

    /// An extraction set is refused if its file differs from its pin, if it belongs to another
    /// parameter set (Jali derives another modulus), or if its rank changes (its pin then
    /// differs, and Jali would refuse its modulus as well).
    #[test]
    fn a_changed_extraction_file_is_refused() {
        let sets = ParameterSets::load().unwrap();
        let refused = |json: &str, pin: &[u8; 32], params: &TboxParams| {
            matches!(
                load_extraction(json, pin, params),
                Err(Error::LatticeBackend(_))
            )
        };
        assert!(load_extraction(ATT_EXTRACTION_JSON, &ATT_EXTRACTION_SHA256, &sets.att).is_ok());
        let changed = ATT_EXTRACTION_JSON.replacen("\"rank\": 24", "\"rank\": 23", 1);
        assert_ne!(changed, ATT_EXTRACTION_JSON);
        assert!(refused(&changed, &ATT_EXTRACTION_SHA256, &sets.att));
        let pin: [u8; 32] = Sha256::digest(changed.as_bytes()).into();
        assert!(refused(&changed, &pin, &sets.att));
        // the right file and pin against another parameter set
        assert!(refused(
            ATT_EXTRACTION_JSON,
            &ATT_EXTRACTION_SHA256,
            &sets.possess
        ));
        assert!(refused(
            ATT_EXTRACTION_JSON,
            &ISS_EXTRACTION_SHA256,
            &sets.att
        ));
    }

    #[test]
    fn the_pins_are_in_the_documented_order() {
        assert_eq!(PINS, [TAG_SHA256, ATT_SHA256, ISS_SHA256, POSSESS_SHA256]);
        assert_eq!(
            EXTRACTION_PINS,
            [
                TAG_EXTRACTION_SHA256,
                ATT_EXTRACTION_SHA256,
                ISS_EXTRACTION_SHA256,
                POSSESS_EXTRACTION_SHA256
            ]
        );
        let distinct: std::collections::BTreeSet<_> =
            PINS.iter().chain(EXTRACTION_PINS.iter()).collect();
        assert_eq!(distinct.len(), 8);
        for (json, pin) in [
            (TAG_EXTRACTION_JSON, TAG_EXTRACTION_SHA256),
            (ATT_EXTRACTION_JSON, ATT_EXTRACTION_SHA256),
            (ISS_EXTRACTION_JSON, ISS_EXTRACTION_SHA256),
            (POSSESS_EXTRACTION_JSON, POSSESS_EXTRACTION_SHA256),
        ] {
            assert_eq!(Sha256::digest(json.as_bytes()).as_slice(), pin);
        }
    }

    /// `of` pairs each kind of proof with its parameter set and that set's extraction set.
    #[test]
    fn the_sets_of_each_kind() {
        let sets = ParameterSets::load().unwrap();
        for (kind, params, extraction) in [
            (ProofKind::Identifier, &sets.tag, &sets.extraction.tag),
            (ProofKind::Attestation, &sets.att, &sets.extraction.att),
            (ProofKind::Issuance, &sets.iss, &sets.extraction.iss),
            (
                ProofKind::Possession,
                &sets.possess,
                &sets.extraction.possess,
            ),
        ] {
            let set = sets.of(kind);
            assert!(std::ptr::eq(set.params, params));
            assert!(std::ptr::eq(set.extraction, extraction));
        }
    }
}
