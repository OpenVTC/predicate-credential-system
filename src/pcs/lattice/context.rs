//! The digest of the lattice `pp` and the contexts $`ctx_j`$, $`ctx_0`$, $`ctx_{\mathsf{root}}`$, as
//! [`Transcript`] digests (SHA-256, injective framing), passed to Jali
//! as the application context of each proof:
//!
//! | digest | oracle suffix | items |
//! |---|---|---|
//! | `pp` | `/LATTICE-PP-DIGEST` | `label`, `format`, `pp-sigma`, `c0`, `jali-pp-seed`, `jali-sets`, `jali`, `placement` |
//! | $`ctx_j = (pp, hvk, id_i, \phi_j, id_{j \to i}, cred^*_j)`$ | `/LATTICE-CTX-ATT` | `pp`, `hvk`, `id`, `phi`, `T`, `cred*` (empty) |
//! | $`ctx_0 = (pp, hvk, f_k, id_i, C, id_{i \to i}, (att_j)_j)`$ | `/LATTICE-CTX-ISSUE` | `pp`, `hvk`, `f`, `id`, `C`, `T0`, one `att` per attestation |
//! | $`ctx_{\mathsf{root}} = (\texttt{"root"}, pp, hvk, f_{\mathsf{root}}, id, C, id_{i \to i})`$ | `/LATTICE-CTX-ROOT` | `pp`, `hvk`, `f`, `id`, `C`, `T0` |
//!
//! The component `"root"` of $`ctx_{\mathsf{root}}`$ is the oracle suffix: the three contexts are
//! transcripts of three different oracles, so a proof made for one role never verifies in
//! another. Values enter in their canonical encodings ([`super::types`]): `hvk` and `C` as
//! [`Rq`] (2560 bytes), tags as [`LWRTag`] (336), $`\phi`$ as [`BinaryPoly`] (128), `f` as
//! $`\langle f\rangle`$ ([`Predicate::canonical_bytes`]) and an attestation as
//! $`T \| \phi \| \mathrm{LE32}(|\pi_j|) \| \pi_j`$. The exact bytes are in `docs/encodings.md`.
//! A WIPED `hvk` or $`C`$ (no element of $`R_q`$) enters as an empty item, which no element
//! produces (the items are length-prefixed), so its digest is no context of a well-formed
//! statement; every verifier refuses a wiped key or $`C`$ before it computes a context.
//!
//! As in the pairing construction ([`crate::pcs::context`]):
//!
//! * **A verifier always REBUILDS its context** from the public statement and never takes one
//!   from the prover. The functions are public because they are functions of public data, and
//!   because a harness that plays a cheating prover needs the context an honest verifier will
//!   compute.
//! * **`pp` leads.** The digest of `pp` is computed once per [`LatticePCS`]. Beyond the label
//!   (which stands for `EncPred`, `H_0`, `H_1`), `pp_Σ` and $`c_0`$, it covers what Jali's
//!   verification depends on and the paper's `pp` does not name: Jali's `pp_seed`, the SHA-256
//!   of the three parameter sets, the Jali revision (Jali promises no stability of its proof
//!   encoding or transcripts) and the placement of `s` in the BDLOP part of `R_att` (recorded
//!   only in the derivation report of the set). One item fixes the constants of the
//!   instantiation (`format`).
//! * `f_k` itself enters $`ctx_0`$, not only $`\phi = \mathsf{EncPred}(f_k)`$: $`\phi`$ is a hash
//!   and does not tell the verifier the threshold.
//! * The attribute policy is not part of a context: it is the verifier's own input of
//!   `CheckAtts_P`.
//!
//! The harness the parameter sets were validated with framed its contexts differently
//! (`"pcs-128-final/ctx/v1"` with its own labels, and the stand-in key `h` of each attestation
//! in $`ctx_j`$; H/flow.rs:58-65, 166-169). With ONE helper key, $`h`$ is `hvk` and is in every
//! context already; the contexts here follow the paper's tuples (con:137, con:159, con:417).

use super::{
    LatticePCS,
    types::{Attestation, PublicParameters},
};
use crate::{
    cred::vsis::VSISVerificationKey,
    hash::Transcript,
    kiprf::lwr::LWRTag,
    lattice::{
        BETA_R, BETA_U, BETA_X, BinaryPoly, D, E_BOUND, E_DEG, ELL_R, GAMMA, JALI_REVISION, M, P,
        PROOF_DEGREE, Q, Q_T, Rq, S_BOUND,
        sets::{ATT_SHA256, ISSUE_ROOT_SHA256, ISSUE_SHA256},
    },
    pcs::Predicate,
};

/// Oracle suffix of the digest of `pp`.
const PP_SUFFIX: &[u8] = b"/LATTICE-PP-DIGEST";
/// Oracle suffix of $`ctx_j`$.
const ATTESTATION_SUFFIX: &[u8] = b"/LATTICE-CTX-ATT";
/// Oracle suffix of $`ctx_0`$.
const ISSUANCE_SUFFIX: &[u8] = b"/LATTICE-CTX-ISSUE";
/// Oracle suffix of $`ctx_{\mathsf{root}}`$.
const ROOT_SUFFIX: &[u8] = b"/LATTICE-CTX-ROOT";
/// The version of the format of the lattice objects and contexts, the first word of `format`.
pub(super) const FORMAT_VERSION: u64 = 1;
/// Where `R_att` holds `s`: the BDLOP part of Jali's commitment, the placement the `att` set was
/// derived for (`report-att-beta439.json`, `placement.chosen.bdlop = ["s"]`).
const PLACEMENT: &[u8] = b"R_att:s=bdlop";

impl PublicParameters {
    /// The digest of `pp` that leads every context (module docs): the items `label`, `format`
    /// (15 little-endian 64-bit words: the format version, then $`d, q, \gamma, p, q_t, m,
    /// \lfloor\gamma/2\rfloor, e_{\deg}, \beta_u, \beta_x, \beta_r, \ell_r, \lfloor\beta_s^2\rfloor`$
    /// and the proof degree), `pp-sigma` ($`v \| b_u \| b_\phi \| B_{r,0} \| B_{r,1}`$, 12,800
    /// bytes), `c0` (the 20-bit packing of $`c_0`$, 430,080 bytes), `jali-pp-seed`, `jali-sets`
    /// (the three SHA-256 pins), `jali` (the revision, ASCII) and `placement`. About 0.3 ms.
    #[must_use]
    pub fn digest(&self) -> [u8; 32] {
        let mut transcript = Transcript::new(PP_SUFFIX);
        transcript.append_bytes(b"label", &self.label);
        // `usize` is at most 64 bits wide on every supported target, so the casts are lossless.
        let format: [u64; 15] = [
            FORMAT_VERSION,
            D as u64,
            u64::from(Q),
            u64::from(GAMMA),
            u64::from(P),
            u64::from(Q_T),
            M as u64,
            E_BOUND,
            E_DEG as u64,
            BETA_U,
            BETA_X,
            BETA_R,
            ELL_R as u64,
            S_BOUND,
            PROOF_DEGREE as u64,
        ];
        transcript.append_bytes(b"format", &format.map(u64::to_le_bytes).concat());
        let sigma = &self.pp_sigma;
        let mut pp_sigma = Vec::with_capacity(5 * Rq::BYTES);
        for element in [sigma.v(), sigma.b_u(), sigma.b_phi()]
            .into_iter()
            .chain(sigma.b_r())
        {
            pp_sigma.extend_from_slice(&element.to_bytes());
        }
        transcript.append_bytes(b"pp-sigma", &pp_sigma);
        transcript.append_bytes(b"c0", &self.c0.to_bytes());
        transcript.append_bytes(b"jali-pp-seed", &self.jali_pp_seed);
        transcript.append_bytes(
            b"jali-sets",
            &[ATT_SHA256, ISSUE_SHA256, ISSUE_ROOT_SHA256].concat(),
        );
        transcript.append_bytes(b"jali", JALI_REVISION.as_bytes());
        transcript.append_bytes(b"placement", PLACEMENT);
        transcript.digest()
    }
}

/// The encoding of an attestation inside $`ctx_0`$: its canonical encoding
/// $`T \| \phi \| \mathrm{LE32}(|\pi_j|) \| \pi_j`$ ([`Attestation`]).
fn attestation_bytes(attestation: &Attestation) -> Vec<u8> {
    let proof = attestation.proof.as_bytes();
    let mut bytes = Vec::with_capacity(Attestation::FIXED_BYTES + proof.len());
    bytes.extend_from_slice(&attestation.tag.to_bytes());
    bytes.extend_from_slice(attestation.phi.as_bytes());
    // a `Proof` has at most `Proof::MAX_BYTES < 2^32` bytes: the cast is lossless
    bytes.extend_from_slice(&(proof.len() as u32).to_le_bytes());
    bytes.extend_from_slice(proof);
    bytes
}

/// A transcript of the oracle `suffix` that starts with `pp` (its digest) and `hvk`.
fn transcript(pp_digest: &[u8; 32], suffix: &[u8], hvk: &VSISVerificationKey) -> Transcript {
    let mut transcript = Transcript::new(suffix);
    transcript.append_bytes(b"pp", pp_digest);
    transcript.append_bytes(b"hvk", &hvk.h().to_bytes());
    transcript
}

/// [`LatticePCS::attestation_context`] under the `pp` of `pp_digest`: a function of the digest
/// alone, so that the attestation verifications of `CheckAtts_P` compute it without the policy
/// (on other threads with the feature `parallel`).
pub(super) fn attestation_context_of(
    pp_digest: &[u8; 32],
    hvk: &VSISVerificationKey,
    id: &LWRTag,
    phi: &BinaryPoly,
    tag: &LWRTag,
) -> [u8; 32] {
    let mut transcript = transcript(pp_digest, ATTESTATION_SUFFIX, hvk);
    transcript.append_bytes(b"id", &id.to_bytes());
    transcript.append_bytes(b"phi", phi.as_bytes());
    transcript.append_bytes(b"T", &tag.to_bytes());
    transcript.append_bytes(b"cred*", &[]);
    transcript.digest()
}

impl<P> LatticePCS<P> {
    /// A transcript of the oracle `suffix` that starts with `pp` and `hvk`.
    fn context(&self, suffix: &[u8], hvk: &VSISVerificationKey) -> Transcript {
        transcript(&self.pp_digest, suffix, hvk)
    }

    /// $`ctx_j := (pp, hvk, id_i, \phi_j, id_{j \to i}, cred^*_j)`$ (`Attest`, con:137;
    /// `VerifyProofAtt` step 2, con:152), with $`cred^*_j = \bot`$ as an empty item.
    #[must_use]
    pub fn attestation_context(
        &self,
        hvk: &VSISVerificationKey,
        id: &LWRTag,
        phi: &BinaryPoly,
        tag: &LWRTag,
    ) -> [u8; 32] {
        attestation_context_of(&self.pp_digest, hvk, id, phi, tag)
    }

    /// $`ctx_0 := (pp, hvk, f_k, id_i, C, id_{i \to i}, (att_j)_{j \in [k]})`$ (`Prove` step 3,
    /// con:159; `VerifyProof` step 3). `f_k` enters as $`\langle f_k\rangle`$; the attestations
    /// enter one by one, in order, as the last items, each completely.
    #[must_use]
    pub fn issuance_context(
        &self,
        hvk: &VSISVerificationKey,
        f: &Predicate,
        id: &LWRTag,
        c: &Rq,
        t0: &LWRTag,
        attestations: &[Attestation],
    ) -> [u8; 32] {
        let mut transcript = self.context(ISSUANCE_SUFFIX, hvk);
        transcript.append_bytes(b"f", &f.canonical_bytes());
        transcript.append_bytes(b"id", &id.to_bytes());
        transcript.append_bytes(b"C", &c.to_bytes());
        transcript.append_bytes(b"T0", &t0.to_bytes());
        for attestation in attestations {
            transcript.append_bytes(b"att", &attestation_bytes(attestation));
        }
        transcript.digest()
    }

    /// $`ctx_{\mathsf{root}} := (\texttt{"root"}, pp, hvk, f_{\mathsf{root}}, id, C, id_{i \to i})`$
    /// (rem:chain, con:417), the context of a root request; `"root"` is the oracle suffix.
    #[must_use]
    pub fn root_context(
        &self,
        hvk: &VSISVerificationKey,
        f_root: &Predicate,
        id: &LWRTag,
        c: &Rq,
        t0: &LWRTag,
    ) -> [u8; 32] {
        let mut transcript = self.context(ROOT_SUFFIX, hvk);
        transcript.append_bytes(b"f", &f_root.canonical_bytes());
        transcript.append_bytes(b"id", &id.to_bytes());
        transcript.append_bytes(b"C", &c.to_bytes());
        transcript.append_bytes(b"T0", &t0.to_bytes());
        transcript.digest()
    }
}

#[cfg(test)]
mod tests {
    use rand::{RngCore, SeedableRng, rngs::StdRng};
    use sha2::{Digest, Sha256};

    use super::*;
    use crate::{
        cred::{CredentialBase, VSIS},
        hash::DOMAIN_PREFIX,
        pcs::{PredicateCredentialSystem, SetupParams, lattice::types::Proof},
    };

    const KAT: &[u8] = b"PCS-LATTICE-KAT";

    /// The digest of `pp` is the documented transcript, recomputed here from the byte layout of
    /// the module docs with an independent SHA-256 framing, and it is pinned.
    #[test]
    fn the_digest_of_pp_is_the_documented_transcript() {
        let pp = PublicParameters::derive(KAT).unwrap();
        let mut hasher = Sha256::new();
        let mut item = |label: &[u8], data: &[u8]| {
            hasher.update((label.len() as u64).to_le_bytes());
            hasher.update(label);
            hasher.update((data.len() as u64).to_le_bytes());
            hasher.update(data);
        };
        item(b"dst", &[DOMAIN_PREFIX, b"/LATTICE-PP-DIGEST"].concat());
        item(b"label", KAT);
        let format: Vec<u8> = [
            1u64,
            1024,
            1_048_573,
            15,
            65_536,
            983_040,
            168,
            7,
            128,
            1,
            1,
            1,
            2,
            90_803_788_942,
            128,
        ]
        .iter()
        .flat_map(|w| w.to_le_bytes())
        .collect();
        item(b"format", &format);
        item(
            b"pp-sigma",
            &crate::serialization::to_bytes(&pp.pp_sigma).unwrap(),
        );
        item(b"c0", &pp.c0.to_bytes());
        item(b"jali-pp-seed", &pp.jali_pp_seed);
        let mut sets = Vec::new();
        for json in [
            crate::lattice::sets::ATT_JSON,
            crate::lattice::sets::ISSUE_JSON,
            crate::lattice::sets::ISSUE_ROOT_JSON,
        ] {
            sets.extend_from_slice(&Sha256::digest(json.as_bytes()));
        }
        item(b"jali-sets", &sets);
        item(b"jali", b"0cd24f38bd84e2e48d2dcb63f34d2d17cba2a90d");
        item(b"placement", b"R_att:s=bdlop");
        let expected: [u8; 32] = hasher.finalize().into();
        assert_eq!(pp.digest(), expected);
        // the pin, reproduced by an independent Python reference (hashlib;
        // tools/lattice/ref_contexts.py): a change of any item or of the format shows
        assert_eq!(
            hex(&pp.digest()),
            "72c1d94fc0f63645ba250d0ddf9577d656d6624e794e174af05dd4093e4b9515"
        );
        // another label, another digest
        assert_ne!(
            PublicParameters::derive(b"another").unwrap().digest(),
            pp.digest()
        );
    }

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    /// Known answers of the three contexts for fixed inputs under the deployment
    /// `PCS-LATTICE-KAT`, reproduced by the Python reference `ref_contexts.py`.
    #[test]
    fn known_answers_of_the_contexts() {
        let pcs = LatticePCS::setup(SetupParams::new(KAT.to_vec())).unwrap();
        let hvk = VSISVerificationKey::from_h(Rq::from_i64(&[5; D]).unwrap());
        let c = Rq::from_i64(&[7; D]).unwrap();
        let mut id = [0u8; LWRTag::BYTES];
        for (i, b) in id.iter_mut().take(256).enumerate() {
            *b = i as u8;
        }
        let id = LWRTag::from_bytes(&id).unwrap();
        let t = LWRTag::from_bytes(&[0x11; LWRTag::BYTES]).unwrap();
        let t0 = LWRTag::from_bytes(&[0x22; LWRTag::BYTES]).unwrap();
        let phi = BinaryPoly::from_bytes([0x5a; BinaryPoly::BYTES]);
        let attestation = Attestation {
            tag: t.clone(),
            phi,
            proof: Proof::from_bytes(vec![1, 2, 3]).unwrap(),
        };
        assert_eq!(
            hex(&pcs.attestation_context(&hvk, &id, &phi, &t)),
            "b91ef50e4f5141bf975a3b968a64d207fd0bb107879674423ba6512645865adc"
        );
        assert_eq!(
            hex(&pcs.issuance_context(
                &hvk,
                &Predicate::new(2, "members"),
                &id,
                &c,
                &t0,
                &[attestation]
            )),
            "77502dd288188c7026193e009c0d45827cf6063fccbb1d5d81bca41043b8610d"
        );
        assert_eq!(
            hex(&pcs.root_context(&hvk, &Predicate::root("founders"), &id, &c, &t0)),
            "93912252e35514603d2542daeb40afacb6e02581e8f1f7a7cb51bf37265dd1d7"
        );
    }

    /// Every item of a context enters it, and the three oracles are separated: the same items
    /// under `/LATTICE-CTX-ISSUE` (no attestations) and `/LATTICE-CTX-ROOT` give different
    /// contexts.
    #[test]
    fn every_item_enters_its_context() {
        let mut rng = StdRng::seed_from_u64(0x7c7_0001);
        let pcs = LatticePCS::setup(SetupParams::new(b"context-tests".to_vec())).unwrap();
        let (hvk, _) = VSIS::keygen(&pcs.pp.pp_sigma, &mut rng);
        let (hvk2, _) = VSIS::keygen(&pcs.pp.pp_sigma, &mut rng);
        let tag = |rng: &mut StdRng| {
            let mut b = [0u8; LWRTag::BYTES];
            rng.fill_bytes(&mut b);
            LWRTag::from_bytes(&b).unwrap()
        };
        let (id, t, t2) = (tag(&mut rng), tag(&mut rng), tag(&mut rng));
        let mut phi = [0u8; BinaryPoly::BYTES];
        rng.fill_bytes(&mut phi);
        let phi = BinaryPoly::from_bytes(phi);
        let mut phi2 = *phi.as_bytes();
        phi2[0] ^= 1;
        let phi2 = BinaryPoly::from_bytes(phi2);
        let att = pcs.attestation_context(&hvk, &id, &phi, &t);
        assert_eq!(att, pcs.attestation_context(&hvk, &id, &phi, &t));
        for other in [
            pcs.attestation_context(&hvk2, &id, &phi, &t),
            pcs.attestation_context(&hvk, &t2, &phi, &t),
            pcs.attestation_context(&hvk, &id, &phi2, &t),
            pcs.attestation_context(&hvk, &id, &phi, &t2),
        ] {
            assert_ne!(att, other);
        }
        let c = Rq::from_i64(&[5; D]).unwrap();
        let c2 = Rq::from_i64(&[6; D]).unwrap();
        let f = Predicate::new(1, "members");
        let attestation = Attestation {
            tag: t.clone(),
            phi,
            proof: Proof::from_bytes(vec![1, 2, 3]).unwrap(),
        };
        let mut other_proof = attestation.clone();
        other_proof.proof = Proof::from_bytes(vec![1, 2, 4]).unwrap();
        let one = [attestation.clone()];
        let issue = pcs.issuance_context(&hvk, &f, &id, &c, &t2, &one);
        for other in [
            pcs.issuance_context(&hvk2, &f, &id, &c, &t2, &one),
            pcs.issuance_context(&hvk, &Predicate::new(2, "members"), &id, &c, &t2, &one),
            pcs.issuance_context(&hvk, &f, &t, &c, &t2, &one),
            pcs.issuance_context(&hvk, &f, &id, &c2, &t2, &one),
            pcs.issuance_context(&hvk, &f, &id, &c, &t, &one),
            pcs.issuance_context(&hvk, &f, &id, &c, &t2, &[other_proof]),
            pcs.issuance_context(&hvk, &f, &id, &c, &t2, &[]),
            pcs.issuance_context(
                &hvk,
                &f,
                &id,
                &c,
                &t2,
                &[attestation.clone(), attestation.clone()],
            ),
        ] {
            assert_ne!(issue, other);
        }
        let f_root = Predicate::root("founders");
        let root = pcs.root_context(&hvk, &f_root, &id, &c, &t2);
        assert_ne!(root, pcs.issuance_context(&hvk, &f_root, &id, &c, &t2, &[]));
        assert_ne!(root, pcs.root_context(&hvk, &f_root, &id, &c2, &t2));
        assert_ne!(
            root,
            pcs.root_context(&hvk, &Predicate::root("others"), &id, &c, &t2)
        );
        // another deployment, other contexts
        let other = LatticePCS::setup(SetupParams::new(b"context-tests-2".to_vec())).unwrap();
        assert_ne!(att, other.attestation_context(&hvk, &id, &phi, &t));
        assert_ne!(root, other.root_context(&hvk, &f_root, &id, &c, &t2));
        // hvk enters as its 2560-byte encoding
        assert_eq!(hvk.h().to_bytes().len(), 2560);
    }
}
