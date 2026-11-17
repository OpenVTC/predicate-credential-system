//! The lattice (post-quantum) instantiation of `Π_PCreds` (§5.2.3 with §5.1.3): the credential
//! base `Σ-vSIS` ([`base`]) with the short-key `Tag_LWR` ([`crate::kiprf::lwr`]), and Jali
//! proofs for the four relations of the protocol (`relations`), as the [`Backend`]
//! [`LatticeBackend`]. [`LatticeProtocol`] is the protocol over it (Corollary
//! `cor:pcs-instantiations` (iii)). Feature `lattice`.
//!
//! | paper | here |
//! |---|---|
//! | `pp`: $`pp_\Sigma = (v, b_u, B_r)`$, the constants of `Tag_LWR`, $`H_{\mathsf{id}}`$, $`H_{\mathsf{req}}`$ | [`LatticeParams`] (with Jali's public seed and parameter sets) |
//! | $`\mathbf X_0 = H_{\mathsf{id}}(\langle\mathsf{hvk}\rangle)`$, $`x_Q = H_{\mathsf{req}}(\langle pp, \mathsf{hvk}, \mathsf{id}_Q, j_Q\rangle)`$ | [`LatticePoint`] |
//! | the box "`Σ-vSIS` credential base" | [`base::VSIS`] |
//! | `R_Tag`, `R_att`, `R_iss`, `R_Possess` (§4.2, "Relations") | Jali statements (`relations`), sets of [`crate::lattice::sets`] |
//! | "The argument system" (§5.2.3): an LNP22-type argument compiled into a NIZK | Jali, in Jali's straight-line extractable mode, or with Fiat–Shamir with the feature `lattice-plain` ([`LatticeProof`], [`STRAIGHT_LINE`]) |
//! | the issuance cap $`Q_{\max} = 2^{48}`$ | the counter of [`base::VSISSigningKey`] |
//!
//! # The objects
//!
//! | object | type | bytes |
//! |---|---|---|
//! | `usk` | [`Ternary`] | 256 |
//! | `id`, `t` | [`LWRTag`] | 336 |
//! | `hvk`, `sk` | [`base::VSISVerificationKey`], [`base::VSISSigningKey`] | 2560, 5897 |
//! | `Ĉ` | [`Rq`] | 2560 |
//! | `τ = x_0` | [`base::VSISTape`] | 768 |
//! | `σ̂ = (s, x_1)`, `σ = (s, x_1, x_0)` | [`base::VSISPreCredential`], [`base::VSISCredential`] | 5376, 6144 |
//! | `σ*` | `()`, the empty encoding | 0 |
//! | `π_id`, `π_att`, `π_iss`, `π_prove` | [`LatticeProof`] | 4 + `len(π)`; `len(π)` about 28.1, 87.4, 44.3 and 82.4 KB, in the extractable build ([`STRAIGHT_LINE`]) about 166.8, 495.9, 320.3 and 463.5 KB |
//!
//! # What the paper claims, and what this code can claim
//!
//! The paper instantiates its theorem with `Σ-vSIS` and the short-key `Tag_LWR` "for
//! parameters as in lem:base-vsis, lem:tag-lwr-short, under the one-more vSIS assumption and
//! LWR, with the argument system [of §6.2.3] and the rounding errors of the tag clauses
//! extracted exactly". This code implements the protocol box faithfully on that instantiation.
//! **No security theorem covers this code yet:**
//!
//! * **The NIZK.** The theorem assumes a straight-line weak simulation-extractable NIZK (Def.
//!   `def:nizk`). The plain build (feature `lattice-plain`) compiles LNP22-style proofs with
//!   Fiat–Shamir, whose extraction rewinds, and Jali's knowledge soundness under Fiat–Shamir is
//!   not written out. In the default build ([`STRAIGHT_LINE`]) the proofs are Jali's straight-line
//!   extractable proofs (Katsumata's transform). Jali's target for them has the form of
//!   `def:nizk` with the context in the statement: in the classical random-oracle model, an
//!   extractor that neither rewinds nor queries the oracle itself recovers, after simulated
//!   proofs of true or false statements, a witness for every accepted proof whose statement and
//!   context received no simulated proof. Jali gives that argument as an outline with the
//!   status of each step and claims nothing in the quantum random-oracle model, so `def:nizk`
//!   is targeted but not established for this instantiation either.
//! * **The parameters.** The request is pseudorandom under MLWE with $`\ell_r = 3`$ ternary
//!   components of $`x_0`$ (lem:base-vsis (b)), and the proofs extract $`s \neq 0`$ (a two-sided
//!   exact norm), with $`\mathcal V_{\mathsf{pp}} = R_q`$, the whole key space, as §5.2.3 states
//!   ([`base`], "What the paper asks of the parameters"). The one-more vSIS assumption is not
//!   estimated at $`k = 1 + \ell_r = 4`$.
//!
//! The paper's key rotation at the cap ("the helper must accept attestations under each of its
//! keys") is outside the single-key model of the protocol and not implemented: a helper at the
//! cap issues nothing more under its key ([`Error::IssuanceCapReached`]).
//!
//! # Implementation notes
//!
//! None of them changes what honest parties compute.
//!
//! * **`pp` covers Jali.** The digest of `pp` ([`crate::pcreds::PublicParameters::digest`])
//!   covers the encoding of [`LatticeParams`]: besides `pp_Σ` and the label (which stands for
//!   `H_mat`, `H_id` and `H_req`), the constants of the instantiation, Jali's public seed, the
//!   SHA-256 pins of the four parameter sets, the Jali version (Jali promises no stability of
//!   its proof encoding or transcripts) and the placement of `s`, and in the extractable build
//!   the argument system and the pins of the four extraction sets, so that the two builds never
//!   share a `pp`. Every proof context starts with that digest.
//! * **Points by their oracle input.** A point of $`\mathbb Z_{q_t}^{m \times n}`$ is
//!   172,032 entries; a [`LatticePoint`] is the input of $`H_{\mathsf{mat}}`$ that defines it, and
//!   the matrix is derived when a tag is evaluated or a statement built (about 0.6 ms). The rule
//!   `x_Q ≠ x_0` compares the matrices ([`Backend::same_point`]).
//! * **Bounded proofs.** A proof longer than twice the estimated size of its parameter set is
//!   refused before any work on it, by the compact decoders and by every verifier
//!   ([`crate::lattice::sets`]).
//! * **Honest provers check their witness first.** A credential that does not verify, or a tag
//!   that the key does not give at the point, is refused
//!   ([`Error::WitnessDoesNotSatisfyRelation`]) before Jali compiles anything; Jali's prover
//!   would refuse the witness as well.
//! * **Fresh coins everywhere.** Every Jali proof gets a fresh 32-byte seed from the caller's
//!   RNG, every `SampPre` call another one, every `TrapGen` another one; a `RestartLimit` of Jali
//!   is retried with a new seed.
//! * **Cost.** An attestation proof takes seconds (about 7 s to prove and 3.5 s to verify at one
//!   thread on an Apple M4) and up to about 0.7 GB of memory to prove or to verify. The
//!   extractable build's proofs are about 5.7 times as long, but a whole protocol run retired
//!   only 1.08 times the instructions of the plain build (seeds 1 to 3, one thread): its
//!   verifications stayed within 6 % of the plain ones, its proofs vary with their restarts,
//!   and its peak memory was about 0.73 GB (docs/testing-and-benchmarks.md). A helper
//!   verifies every attestation of a request, so it should limit their number
//!   ([`crate::pcreds::Policy::with_max_attestations`]); with the feature `parallel` the
//!   attestations of a request are verified in parallel, in batches no wider than the rayon pool
//!   ([`crate::pcreds::Protocol::evaluate_request`]).
//! * **Side channels.** Performance comes first. Jali, `SampPre`'s floating-point arithmetic and
//!   rejection loops, `TrapGen` and the rejection sampling of ternary polynomials run in variable
//!   time ([`crate::lattice`], "Side channels").
//!
//! # Example
//!
//! The flow of [`crate::pcreds`] at the lattice instantiation: two root users attest for a
//! newcomer under `Pol_2`. Each attestation is a Jali proof of about 87 KB (about 496 KB in the
//! extractable build) that takes seconds to prove and to verify. The example is compiled but not
//! run by the documentation tests (`tests/lattice_protocol.rs` runs the same flow in release).
//!
//! ```no_run
//! use predicate_credential_system::pcreds::{Decision, Policy, Reply, lattice::LatticeProtocol};
//! use rand::{SeedableRng, rngs::StdRng};
//!
//! // seeded so that the example is reproducible; a helper uses `rand::rngs::OsRng`, since its
//! // trapdoor is a function of the RNG's output
//! let mut rng = StdRng::seed_from_u64(1);
//! let pcreds = LatticeProtocol::setup(b"example deployment")?;
//! // every attestation costs the helper seconds: limit their number
//! let policy = Policy::threshold(2)?.with_max_attestations(8)?;
//! let mut helper = pcreds.helper_keygen(policy, &mut rng); // TrapGen
//! let hvk = pcreds.helper_key(helper.key().vk())?;
//!
//! let mut members = Vec::new();
//! for i in 0..2 {
//!     let user = pcreds.register(&hvk, &mut rng)?;
//!     let ssid = format!("root-{i}").into_bytes();
//!     let (message, state) = pcreds.request_credential(&hvk, &user, Vec::new(), &ssid, &mut rng)?;
//!     let evaluated = pcreds.evaluate_request(&helper, &message, &ssid)?;
//!     let Reply::PreCredential(pre) = pcreds.respond(&mut helper, evaluated, Decision::Root, &mut rng)? else {
//!         unreachable!("a root admission issues");
//!     };
//!     members.push((pcreds.unblind(&hvk, &user, &pre, state)?, user));
//! }
//!
//! let newcomer = pcreds.register(&hvk, &mut rng)?;
//! let mut attestations = Vec::new();
//! for (j, (cred, member)) in members.iter().enumerate() {
//!     let (ssid, contact) = (format!("att-{j}").into_bytes(), format!("member-{j}").into_bytes());
//!     let request = pcreds.request_attestation(&hvk, &newcomer, &ssid, &contact, &mut rng)?;
//!     let pending = pcreds.receive_attestation_request(&hvk, &request, &ssid, &contact)?;
//!     attestations.push(pcreds.attest(&hvk, member, cred, pending, &mut rng)?);
//! }
//! let (message, state) = pcreds.request_credential(&hvk, &newcomer, attestations, b"req", &mut rng)?;
//! let evaluated = pcreds.evaluate_request(&helper, &message, b"req")?;
//! let Reply::PreCredential(pre) = pcreds.respond(&mut helper, evaluated, Decision::Policy, &mut rng)? else {
//!     unreachable!("a valid request is issued");
//! };
//! let cred = pcreds.unblind(&hvk, &newcomer, &pre, state)?;
//! let proof = pcreds.prove(&hvk, &newcomer, &cred, b"hello", &mut rng)?;
//! assert!(pcreds.verify(&hvk, b"hello", &proof));
//! # Ok::<(), predicate_credential_system::Error>(())
//! ```

pub mod base;
pub(crate) mod relations;

use core::fmt;
use std::sync::Arc;

use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, Read, SerializationError, Valid, Validate,
    Write,
};
use ark_std::rand::{CryptoRng, RngCore};
use jali::statement::Statement;
use zeroize::Zeroizing;

use self::{
    base::{
        VSIS, VSISCredential, VSISParams, VSISPreCredential, VSISSigningKey, VSISTape,
        VSISVerificationKey,
    },
    relations::{Constants, TagRows, tag_values},
};
use super::{
    Protocol,
    backend::{AttestationStatement, Backend, IssuanceStatement, Leaf, ProofKind},
};
use crate::{
    error::Error,
    hash::Transcript,
    kiprf::{
        KIPRF,
        lwr::{LWR, LWRTag, TagMatrix},
    },
    lattice::{
        BETA_R, BETA_U, BETA_X, D, E_BOUND, E_DEG, ELL_R, GAMMA, JALI_VERSION, M, P, PROOF_DEGREE,
        Q, Q_MAX, Q_T, Rq, S_BOUND, STRAIGHT_LINE, Ternary, oracles,
        sets::{
            ATT_PROOF_MAX_BYTES, EXTRACTION_PINS, ISS_PROOF_MAX_BYTES, PINS,
            POSSESS_PROOF_MAX_BYTES, ParameterSets, TAG_PROOF_MAX_BYTES,
        },
        xof,
    },
};

/// The protocol over the lattice instantiation.
pub type LatticeProtocol = Protocol<LatticeBackend>;

/// The version of the format of the lattice parameters, the first word of their `format` item.
/// Version 1 was the earlier construction (tag `pcs-final`), version 2 the first port, with
/// $`\ell_r = 2`$.
pub const FORMAT_VERSION: u64 = 3;

/// The constants of the instantiation as they enter the encoding of [`LatticeParams`]: the
/// format version, then $`d, q, \gamma, p, q_t, m, \lfloor\gamma/2\rfloor, e_{\deg}, \beta_u,
/// \beta_x, \beta_r, \ell_r, \lfloor\beta_s^2\rfloor`$, the proof degree and $`Q_{\max}`$.
// `usize` is at most 64 bits wide on every supported target, so the casts are lossless.
const FORMAT: [u64; 16] = [
    FORMAT_VERSION,
    D as u64,
    Q as u64,
    GAMMA as u64,
    P as u64,
    Q_T as u64,
    M as u64,
    E_BOUND,
    E_DEG as u64,
    BETA_U,
    BETA_X,
    BETA_R,
    ELL_R as u64,
    S_BOUND,
    PROOF_DEGREE as u64,
    Q_MAX,
];

/// Where `R_att` and `R_Possess` hold `s`: the BDLOP part of Jali's commitment, the placement
/// their parameter sets were derived for (and which the statement builders hard-code).
const PLACEMENT: &[u8] = b"R_att:s=bdlop;R_Possess:s=bdlop";

/// The argument system of the extractable build ([`STRAIGHT_LINE`]) as it enters the encoding of
/// [`LatticeParams`], after the placement and before the pins of the extraction sets: Jali's
/// straight-line extractable mode in the classical random-oracle model. The plain build's
/// encoding has neither item.
const ARGUMENT: &[u8] = b"jali-extractable:rom";

/// The parameters of a deployment of the lattice instantiation: the deployment label, `pp_Σ`
/// of `Σ-vSIS` and Jali's public seed, all derived from the label (transparent `Setup`), and the
/// checked parameter sets of Jali and the statement constants, built once and shared by the
/// clones of a value.
///
/// Implementation note: Jali's public seed `pp_seed`, from which Jali expands the public
/// matrices of its commitments, is not part of the paper's `pp`; it must come from public
/// randomness all the same, never from the helper, so it is derived from the label like
/// everything else (`/LATTICE-JALI-SEED`, [`crate::lattice`]).
///
/// Encoding (strict, [`Self::BYTES`] bytes plus the label and the strings): `label` (LE64
/// length, bytes), `format` (16 LE64 words, module constants), `pp_Σ` ([`VSISParams`]),
/// `pp_seed` (32), the four SHA-256 pins of the parameter sets (128), the Jali version (LE64
/// length, ASCII) and the placement of `s` (LE64 length, ASCII), and in the extractable build
/// ([`STRAIGHT_LINE`]) then the argument system (LE64 length, ASCII `jali-extractable:rom`) and
/// the four SHA-256 pins of the extraction sets (128). A decoder refuses any value but the
/// constants of this build in every item but the label, `pp_Σ` and `pp_seed`, which
/// [`Protocol::from_public_parameters`] compares with what the label derives. Equality compares
/// the label, `pp_Σ` and `pp_seed`.
#[derive(Clone)]
pub struct LatticeParams {
    label: Vec<u8>,
    sigma: VSISParams,
    jali_pp_seed: [u8; 32],
    cache: Arc<Cache>,
}

/// What a deployment builds once: the parameter sets and the statement constants. The
/// identifier point is not among them: "each helper key determines its own identifier point".
struct Cache {
    sets: ParameterSets,
    constants: Constants,
}

impl LatticeParams {
    /// Bytes of the encoding besides the label and the strings, with the pins of the extraction
    /// sets in the extractable build ([`STRAIGHT_LINE`]).
    pub const BYTES: usize =
        16 * 8 + VSISParams::BYTES + 32 + 4 * 32 + if STRAIGHT_LINE { 4 * 32 } else { 0 };

    /// `Setup` for the deployment `label` (a few ms on an Apple M4 core: the expansion of `pp_Σ`,
    /// the loading of the parameter sets, the lifting of the constants).
    ///
    /// # Errors
    /// [`Error::LatticeBackend`] if the embedded parameter sets do not load.
    pub fn derive(label: &[u8]) -> Result<Self, Error> {
        Self::assemble(label.to_vec(), VSIS::setup(label), xof::jali_pp_seed(label))
    }

    fn assemble(label: Vec<u8>, sigma: VSISParams, jali_pp_seed: [u8; 32]) -> Result<Self, Error> {
        let sets = ParameterSets::load()?;
        let constants = Constants::new(&sigma)?;
        Ok(Self {
            label,
            sigma,
            jali_pp_seed,
            cache: Arc::new(Cache { sets, constants }),
        })
    }

    /// The deployment label.
    #[must_use]
    pub fn label(&self) -> &[u8] {
        &self.label
    }

    /// `pp_Σ = (v, b_u, B_r)`.
    #[must_use]
    pub fn sigma(&self) -> &VSISParams {
        &self.sigma
    }

    /// Jali's public seed `pp_seed`.
    #[must_use]
    pub fn jali_pp_seed(&self) -> &[u8; 32] {
        &self.jali_pp_seed
    }

    /// The checked parameter sets of Jali.
    #[must_use]
    pub fn parameter_sets(&self) -> &ParameterSets {
        &self.cache.sets
    }

    /// The matrix of `point` (about 0.6 ms): $`H_{\mathsf{mat}}`$ under the label of its oracle
    /// ([`oracles`]).
    #[must_use]
    pub fn matrix(&self, point: &LatticePoint) -> TagMatrix {
        match point {
            LatticePoint::Identifier(digest) => oracles::identifier_point(&self.label, digest),
            LatticePoint::Request(digest) => oracles::request_point(&self.label, digest),
        }
    }

    /// The tag of `usk` at `point`, with its rounding error. `None` for a wiped key.
    fn eval(
        &self,
        usk: &Ternary,
        point: &LatticePoint,
    ) -> Option<(LWRTag, crate::kiprf::lwr::RoundingError)> {
        LWR.eval_with_error(usk, &self.matrix(point))
    }

    /// The rows of the matrix of `point`, lifted for the tag clauses.
    fn rows(&self, point: &LatticePoint) -> Result<TagRows, Error> {
        TagRows::new(&self.cache.constants.rings, &self.matrix(point))
    }

    fn constants(&self) -> &Constants {
        &self.cache.constants
    }
}

impl PartialEq for LatticeParams {
    fn eq(&self, other: &Self) -> bool {
        self.label == other.label
            && self.sigma == other.sigma
            && self.jali_pp_seed == other.jali_pp_seed
    }
}

impl Eq for LatticeParams {}

impl fmt::Debug for LatticeParams {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("LatticeParams")
            .field("label", &String::from_utf8_lossy(&self.label))
            .finish_non_exhaustive()
    }
}

impl CanonicalSerialize for LatticeParams {
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        self.label.serialize_with_mode(&mut writer, compress)?;
        for word in FORMAT {
            writer.write_all(&word.to_le_bytes())?;
        }
        self.sigma.serialize_with_mode(&mut writer, compress)?;
        writer.write_all(&self.jali_pp_seed)?;
        for pin in PINS {
            writer.write_all(&pin)?;
        }
        JALI_VERSION
            .as_bytes()
            .to_vec()
            .serialize_with_mode(&mut writer, compress)?;
        PLACEMENT
            .to_vec()
            .serialize_with_mode(&mut writer, compress)?;
        if STRAIGHT_LINE {
            ARGUMENT
                .to_vec()
                .serialize_with_mode(&mut writer, compress)?;
            for pin in EXTRACTION_PINS {
                writer.write_all(&pin)?;
            }
        }
        Ok(())
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        self.label.serialized_size(compress)
            + Self::BYTES
            + JALI_VERSION.as_bytes().to_vec().serialized_size(compress)
            + PLACEMENT.to_vec().serialized_size(compress)
            + if STRAIGHT_LINE {
                ARGUMENT.to_vec().serialized_size(compress)
            } else {
                0
            }
    }
}

impl Valid for LatticeParams {
    fn check(&self) -> Result<(), SerializationError> {
        self.sigma.check()
    }
}

impl CanonicalDeserialize for LatticeParams {
    /// Strict: every constant item must be this build's, whatever `validate` says; rebuilds the
    /// caches (module docs).
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let label = Vec::<u8>::deserialize_with_mode(&mut reader, compress, validate)?;
        for word in FORMAT {
            let mut le = [0u8; 8];
            reader.read_exact(&mut le)?;
            if u64::from_le_bytes(le) != word {
                return Err(SerializationError::InvalidData);
            }
        }
        let sigma = VSISParams::deserialize_with_mode(&mut reader, compress, validate)?;
        let mut jali_pp_seed = [0u8; 32];
        reader.read_exact(&mut jali_pp_seed)?;
        for pin in PINS {
            let mut read = [0u8; 32];
            reader.read_exact(&mut read)?;
            if read != pin {
                return Err(SerializationError::InvalidData);
            }
        }
        let version = Vec::<u8>::deserialize_with_mode(&mut reader, compress, validate)?;
        let placement = Vec::<u8>::deserialize_with_mode(&mut reader, compress, validate)?;
        if version != JALI_VERSION.as_bytes() || placement != PLACEMENT {
            return Err(SerializationError::InvalidData);
        }
        if STRAIGHT_LINE {
            let argument = Vec::<u8>::deserialize_with_mode(&mut reader, compress, validate)?;
            if argument != ARGUMENT {
                return Err(SerializationError::InvalidData);
            }
            for pin in EXTRACTION_PINS {
                let mut read = [0u8; 32];
                reader.read_exact(&mut read)?;
                if read != pin {
                    return Err(SerializationError::InvalidData);
                }
            }
        }
        Self::assemble(label, sigma, jali_pp_seed).map_err(|_| SerializationError::InvalidData)
    }
}

/// A point of the tag domain $`\mathbb Z_{q_t}^{m \times n}`$, by the input of
/// $`H_{\mathsf{mat}}`$ that defines it ([`crate::lattice::oracles`]): the identifier point
/// $`x_0 = H_{\mathsf{id}}(\langle\mathsf{hvk}\rangle) = H_{\mathsf{mat}}(\texttt{"hid"} \|
/// d)`$ of a helper key, or a recipient point $`x_Q = H_{\mathsf{mat}}(\texttt{"req"} \| d)`$,
/// for the 32-byte digest $`d`$ of the protocol's transcript of that oracle.
/// [`LatticeParams::matrix`] derives the matrix. Public.
///
/// Encoding: one byte (`0` for an identifier point, `1` for a recipient point), then $`d`$.
/// Equality compares the inputs; the protocol's rule `x_Q ≠ x_0` compares the matrices
/// ([`Backend::same_point`]). Two distinct inputs give the same matrix only with probability
/// $`q_t^{-mn}`$ in the random-oracle model, and the inputs of the two oracles never coincide
/// (their labels differ and have one length).
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum LatticePoint {
    /// $`x_0 = H_{\mathsf{mat}}(\texttt{"hid"} \| d)`$.
    Identifier([u8; 32]),
    /// $`x_Q = H_{\mathsf{mat}}(\texttt{"req"} \| d)`$.
    Request([u8; 32]),
}

const POINT_IDENTIFIER: u8 = 0;
const POINT_REQUEST: u8 = 1;

impl fmt::Debug for LatticePoint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (oracle, d) = match self {
            Self::Identifier(d) => ("H_id", d),
            Self::Request(d) => ("H_req", d),
        };
        write!(f, "LatticePoint({oracle} ")?;
        for byte in &d[..8] {
            write!(f, "{byte:02x}")?;
        }
        f.write_str("..)")
    }
}

impl CanonicalSerialize for LatticePoint {
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        _compress: Compress,
    ) -> Result<(), SerializationError> {
        let (kind, d) = match self {
            Self::Identifier(d) => (POINT_IDENTIFIER, d),
            Self::Request(d) => (POINT_REQUEST, d),
        };
        writer.write_all(&[kind])?;
        writer.write_all(d)?;
        Ok(())
    }

    fn serialized_size(&self, _compress: Compress) -> usize {
        33
    }
}

impl Valid for LatticePoint {
    const TRIVIAL_CHECK: bool = true;

    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }
}

impl CanonicalDeserialize for LatticePoint {
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        _compress: Compress,
        _validate: Validate,
    ) -> Result<Self, SerializationError> {
        let mut kind = [0u8; 1];
        reader.read_exact(&mut kind)?;
        let make = match kind[0] {
            POINT_IDENTIFIER => Self::Identifier,
            POINT_REQUEST => Self::Request,
            _ => return Err(SerializationError::InvalidData),
        };
        let mut d = [0u8; 32];
        reader.read_exact(&mut d)?;
        Ok(make(d))
    }
}

/// Bytes of the length prefix of a Jali proof.
const LENGTH_BYTES: usize = 4;

/// A Jali proof: the bytes of `Compiled::prove_bytes_with_seed`, or in the extractable build
/// ([`STRAIGHT_LINE`]) of `Compiled::prove_extractable_bytes_with_seed`. Public.
///
/// Encoding: `LE32(len) ‖ bytes` ([`Self::encoded_size`] bytes): Jali proofs vary in length by
/// tens of bytes with the proof seed, and Jali's decoder neither reads nor tolerates a length
/// (it rejects truncation and trailing bytes), so a valid proof has exactly one encoding. The
/// decoder refuses a length above its bound before it reads the proof, and it allocates only as
/// the input arrives, so a forged length on a short input fails fast. The bound is Jali's own
/// decoding limit ([`Self::MAX_BYTES`]) for the canonical encoding, and the bound of the proof's
/// parameter set (twice its estimate, [`crate::lattice::sets`]) for the compact encoding of
/// [`crate::pcreds::codec`] and in every verifier.
#[derive(Clone, PartialEq, Eq)]
pub struct LatticeProof(Vec<u8>);

impl LatticeProof {
    /// The largest stand-alone proof, Jali's own decoding limit (16 MiB).
    pub const MAX_BYTES: usize = 1 << 24;

    /// The bound of a proof of the given kind: twice the estimated size of its parameter set.
    #[must_use]
    pub const fn max_bytes(kind: ProofKind) -> usize {
        match kind {
            ProofKind::Identifier => TAG_PROOF_MAX_BYTES,
            ProofKind::Attestation => ATT_PROOF_MAX_BYTES,
            ProofKind::Issuance => ISS_PROOF_MAX_BYTES,
            ProofKind::Possession => POSSESS_PROOF_MAX_BYTES,
        }
    }

    /// Wraps proof bytes.
    ///
    /// # Errors
    /// [`Error::Serialization`] above [`Self::MAX_BYTES`].
    pub fn from_bytes(bytes: Vec<u8>) -> Result<Self, Error> {
        if bytes.len() > Self::MAX_BYTES {
            return Err(Error::Serialization(format!(
                "Jali proof of {} bytes, more than {}",
                bytes.len(),
                Self::MAX_BYTES
            )));
        }
        Ok(Self(bytes))
    }

    /// The proof bytes, as Jali encodes them.
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    /// The length of the proof in bytes, $`|\pi|`$.
    #[must_use]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Whether the proof has no bytes (no proof of this crate is empty).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Bytes of the encoding: the 4-byte length and the proof.
    #[must_use]
    pub fn encoded_size(&self) -> usize {
        LENGTH_BYTES + self.0.len()
    }

    /// [`Error::InvalidProof`] above the bound of its kind, before any work on the proof.
    fn within(&self, kind: ProofKind) -> Result<(), Error> {
        if self.0.len() <= Self::max_bytes(kind) {
            Ok(())
        } else {
            Err(Error::InvalidProof)
        }
    }

    /// Writes `LE32(len) ‖ bytes`, refusing a proof longer than `max`.
    fn write_bounded<W: Write>(&self, mut writer: W, max: usize) -> Result<(), SerializationError> {
        if self.0.len() > max.min(Self::MAX_BYTES) {
            return Err(SerializationError::InvalidData);
        }
        // MAX_BYTES < 2^32: the cast is lossless
        writer.write_all(&(self.0.len() as u32).to_le_bytes())?;
        writer.write_all(&self.0)?;
        Ok(())
    }

    /// Reads `LE32(len) ‖ bytes`, refusing a length above `max` before it reads the proof.
    fn read_bounded<R: Read>(mut reader: R, max: usize) -> Result<Self, SerializationError> {
        let mut length = [0u8; LENGTH_BYTES];
        reader.read_exact(&mut length)?;
        let length = u32::from_le_bytes(length) as usize;
        if length > max.min(Self::MAX_BYTES) {
            return Err(SerializationError::InvalidData);
        }
        // `take` + `read_to_end` grows the buffer with the input, so a forged length does not
        // allocate the maximum up front
        let mut bytes = Vec::new();
        reader
            .by_ref()
            .take(length as u64)
            .read_to_end(&mut bytes)?;
        if bytes.len() != length {
            return Err(SerializationError::IoError(std::io::Error::from(
                std::io::ErrorKind::UnexpectedEof,
            )));
        }
        Ok(Self(bytes))
    }
}

impl fmt::Debug for LatticeProof {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "LatticeProof({} bytes)", self.0.len())
    }
}

impl CanonicalSerialize for LatticeProof {
    fn serialize_with_mode<W: Write>(
        &self,
        writer: W,
        _compress: Compress,
    ) -> Result<(), SerializationError> {
        self.write_bounded(writer, Self::MAX_BYTES)
    }

    fn serialized_size(&self, _compress: Compress) -> usize {
        self.encoded_size()
    }
}

impl Valid for LatticeProof {
    fn check(&self) -> Result<(), SerializationError> {
        if self.0.len() <= Self::MAX_BYTES {
            Ok(())
        } else {
            Err(SerializationError::InvalidData)
        }
    }
}

impl CanonicalDeserialize for LatticeProof {
    /// Refuses a length above [`LatticeProof::MAX_BYTES`], whatever `validate` says.
    fn deserialize_with_mode<R: Read>(
        reader: R,
        _compress: Compress,
        _validate: Validate,
    ) -> Result<Self, SerializationError> {
        Self::read_bounded(reader, Self::MAX_BYTES)
    }
}

/// The [`Backend`] of the lattice instantiation: `Σ-vSIS`, the short-key `Tag_LWR` and Jali
/// proofs (module docs). A marker type.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct LatticeBackend;

impl LatticeBackend {
    /// [`Error::InvalidKey`] for a key outside `V_pp` (a wiped key).
    fn admissible(vk: &VSISVerificationKey) -> Result<(), Error> {
        if VSIS::admissible_key(vk) {
            Ok(())
        } else {
            Err(Error::InvalidKey)
        }
    }

    /// Proves `statement` for `witness` under the sets of the proofs of `kind`, in this build's
    /// mode ([`STRAIGHT_LINE`]).
    fn prove_with<R: RngCore + CryptoRng + ?Sized>(
        params: &LatticeParams,
        statement: &Statement,
        kind: ProofKind,
        witness: &relations::Witness,
        ctx: &[u8],
        rng: &mut R,
    ) -> Result<LatticeProof, Error> {
        let set = params.cache.sets.of(kind);
        let bytes = relations::prove(statement, set, params.jali_pp_seed, witness, ctx, rng)?;
        LatticeProof::from_bytes(bytes)
    }

    /// Verifies `proof` for `statement` under the sets of the proofs of `kind`, in this build's
    /// mode (the caller checked its length bound first).
    fn verify_with(
        params: &LatticeParams,
        statement: &Statement,
        kind: ProofKind,
        ctx: &[u8],
        proof: &LatticeProof,
    ) -> Result<(), Error> {
        let set = params.cache.sets.of(kind);
        relations::verify(statement, set, params.jali_pp_seed, proof.as_bytes(), ctx)
    }

    /// The tag of `usk` at `point` and its rounding error, refused unless it is `tag`.
    fn tag_witness_of(
        params: &LatticeParams,
        usk: &Ternary,
        point: &LatticePoint,
        tag: &LWRTag,
    ) -> Result<crate::kiprf::lwr::RoundingError, Error> {
        match params.eval(usk, point) {
            Some((t, e)) if &t == tag => Ok(e),
            _ => Err(Error::WitnessDoesNotSatisfyRelation),
        }
    }
}

impl Backend for LatticeBackend {
    type Params = LatticeParams;
    type UserKey = Ternary;
    type Point = LatticePoint;
    type Tag = LWRTag;
    type VerificationKey = VSISVerificationKey;
    type SigningKey = VSISSigningKey;
    type Request = Rq;
    type IssuanceTape = VSISTape;
    type PreCredential = VSISPreCredential;
    type Credential = VSISCredential;
    type Show = ();
    type Proof = LatticeProof;

    fn name() -> String {
        "vSIS+LWR".to_string()
    }

    fn setup(label: &[u8]) -> Result<LatticeParams, Error> {
        LatticeParams::derive(label)
    }

    fn check_params(params: &LatticeParams) -> Result<(), Error> {
        params
            .sigma
            .check()
            .map_err(|_| Error::DegenerateInput("pp_Σ"))
    }

    /// `x_0 = H_mat("hid" ‖ d)` for the digest `d` of the `H_id` transcript.
    fn identifier_point(_params: &LatticeParams, transcript: &Transcript) -> LatticePoint {
        LatticePoint::Identifier(transcript.digest())
    }

    /// `x_Q = H_mat("req" ‖ d)` for the digest `d` of the `H_req` transcript.
    fn request_point(_params: &LatticeParams, transcript: &Transcript) -> LatticePoint {
        LatticePoint::Request(transcript.digest())
    }

    /// The matrices, not the oracle inputs: "`j_Q` is the least nonnegative counter for which
    /// `x_Q ≠ x_0`". Equal inputs give equal matrices; otherwise both are derived (about 1.2 ms).
    fn same_point(params: &LatticeParams, a: &LatticePoint, b: &LatticePoint) -> bool {
        a == b || params.matrix(a) == params.matrix(b)
    }

    fn tag_keygen<R: RngCore + CryptoRng + ?Sized>(
        _params: &LatticeParams,
        rng: &mut R,
    ) -> Ternary {
        LWR.keygen(rng)
    }

    fn tag(params: &LatticeParams, usk: &Ternary, point: &LatticePoint) -> Option<LWRTag> {
        params.eval(usk, point).map(|(tag, _error)| tag)
    }

    fn check_tag(
        _params: &LatticeParams,
        tag: &LWRTag,
        _point: &LatticePoint,
        _what: &'static str,
    ) -> Result<(), Error> {
        if LWR.valid_tag(tag) {
            Ok(())
        } else {
            Err(Error::InvalidTag)
        }
    }

    fn keygen<R: RngCore + CryptoRng + ?Sized>(
        _params: &LatticeParams,
        rng: &mut R,
    ) -> (VSISVerificationKey, VSISSigningKey) {
        VSIS::keygen(rng)
    }

    fn check_key(_params: &LatticeParams, vk: &VSISVerificationKey) -> Result<(), Error> {
        Self::admissible(vk)
    }

    fn key_pair_matches(
        _params: &LatticeParams,
        vk: &VSISVerificationKey,
        sk: &VSISSigningKey,
    ) -> bool {
        VSIS::key_pair_matches(vk, sk)
    }

    fn signing_key_bytes_reserving(
        sk: &VSISSigningKey,
        n: u64,
    ) -> Result<Zeroizing<Vec<u8>>, Error> {
        sk.to_bytes_reserving(n)
    }

    /// [`Error::IssuanceCapReached`] once the key has reserved $`Q_{\max}`$ `SampPre` calls.
    fn check_issuance_capacity(sk: &VSISSigningKey) -> Result<(), Error> {
        if sk.remaining() == 0 {
            Err(Error::IssuanceCapReached)
        } else {
            Ok(())
        }
    }

    fn prepare_issue<R: RngCore + CryptoRng + ?Sized>(
        params: &LatticeParams,
        _vk: &VSISVerificationKey,
        usk: &Ternary,
        rng: &mut R,
    ) -> Result<(Rq, VSISTape), Error> {
        let tape = VSISTape::sample(rng);
        let request =
            VSIS::prepare_issue(&params.sigma, usk, &tape).ok_or(Error::InvalidIssuanceEncoding)?;
        Ok((request, tape))
    }

    fn blind_issue<R: RngCore + CryptoRng + ?Sized>(
        params: &LatticeParams,
        sk: &VSISSigningKey,
        request: &Rq,
        rng: &mut R,
    ) -> Result<VSISPreCredential, Error> {
        VSIS::blind_issue(&params.sigma, sk, request, rng)
    }

    fn unblind(
        params: &LatticeParams,
        vk: &VSISVerificationKey,
        usk: &Ternary,
        pre: &VSISPreCredential,
        tau: &VSISTape,
    ) -> Result<VSISCredential, Error> {
        VSIS::unblind(&params.sigma, vk, usk, pre, tau)
    }

    fn verify(
        params: &LatticeParams,
        vk: &VSISVerificationKey,
        usk: &Ternary,
        cred: &VSISCredential,
    ) -> bool {
        VSIS::verify(&params.sigma, vk, usk, cred)
    }

    fn prove_tag<R: RngCore + CryptoRng + ?Sized>(
        params: &LatticeParams,
        tag: &LWRTag,
        point: &LatticePoint,
        usk: &Ternary,
        ctx: &[u8],
        rng: &mut R,
    ) -> Result<LatticeProof, Error> {
        if !LWR.valid_tag(tag) {
            return Err(Error::InvalidTag);
        }
        let e = Self::tag_witness_of(params, usk, point, tag)?;
        let k = params.constants();
        let statement = relations::r_tag(k, &params.rows(point)?, &tag_values(tag))?;
        let witness = relations::tag_witness(&k.rings, usk, &e)?;
        Self::prove_with(
            params,
            &statement,
            ProofKind::Identifier,
            &witness,
            ctx,
            rng,
        )
    }

    fn check_tag_proof(
        params: &LatticeParams,
        tag: &LWRTag,
        point: &LatticePoint,
        ctx: &[u8],
        proof: &LatticeProof,
    ) -> Result<(), Error> {
        proof.within(ProofKind::Identifier)?;
        let statement =
            relations::r_tag(params.constants(), &params.rows(point)?, &tag_values(tag))?;
        Self::verify_with(params, &statement, ProofKind::Identifier, ctx, proof)
    }

    fn prove_attestation<R: RngCore + CryptoRng + ?Sized>(
        params: &LatticeParams,
        statement: &AttestationStatement<'_, Self>,
        usk: &Ternary,
        cred: &VSISCredential,
        ctx: &[u8],
        rng: &mut R,
    ) -> Result<((), LatticeProof), Error> {
        Self::admissible(statement.vk)?;
        if !VSIS::verify(&params.sigma, statement.vk, usk, cred) {
            return Err(Error::WitnessDoesNotSatisfyRelation);
        }
        let e = Self::tag_witness_of(params, usk, statement.point, statement.tag)?;
        let k = params.constants();
        let relation = relations::r_att(
            k,
            statement.vk.h(),
            &params.rows(statement.point)?,
            &tag_values(statement.tag),
        )?;
        let witness = relations::att_witness(&k.rings, cred, usk, &e)?;
        let proof = Self::prove_with(
            params,
            &relation,
            ProofKind::Attestation,
            &witness,
            ctx,
            rng,
        )?;
        Ok(((), proof))
    }

    fn check_attestation_proof(
        params: &LatticeParams,
        statement: &AttestationStatement<'_, Self>,
        _show: &(),
        ctx: &[u8],
        proof: &LatticeProof,
    ) -> Result<(), Error> {
        // `σ*` is the empty encoding: no public check of `R_Possess` to run
        Self::admissible(statement.vk)?;
        proof.within(ProofKind::Attestation)?;
        let relation = relations::r_att(
            params.constants(),
            statement.vk.h(),
            &params.rows(statement.point)?,
            &tag_values(statement.tag),
        )?;
        Self::verify_with(params, &relation, ProofKind::Attestation, ctx, proof)
    }

    fn prove_issuance<R: RngCore + CryptoRng + ?Sized>(
        params: &LatticeParams,
        statement: &IssuanceStatement<'_, Self>,
        usk: &Ternary,
        tau: &VSISTape,
        ctx: &[u8],
        rng: &mut R,
    ) -> Result<LatticeProof, Error> {
        if VSIS::prepare_issue(&params.sigma, usk, tau).as_ref() != Some(statement.request) {
            return Err(Error::WitnessDoesNotSatisfyRelation);
        }
        let e = Self::tag_witness_of(params, usk, statement.x0, statement.id)?;
        let k = params.constants();
        let relation = relations::r_iss(
            k,
            statement.request,
            &params.rows(statement.x0)?,
            &tag_values(statement.id),
        )?;
        let witness = relations::iss_witness(&k.rings, usk, tau, &e)?;
        Self::prove_with(params, &relation, ProofKind::Issuance, &witness, ctx, rng)
    }

    fn check_issuance_proof(
        params: &LatticeParams,
        statement: &IssuanceStatement<'_, Self>,
        ctx: &[u8],
        proof: &LatticeProof,
    ) -> Result<(), Error> {
        // the public check of `Π_PrepareIssue`: `Ĉ ∈ R_q` (only a wiped value is not)
        if statement.request.coeffs().len() != D {
            return Err(Error::InvalidIssuanceEncoding);
        }
        Self::admissible(statement.vk)?;
        proof.within(ProofKind::Issuance)?;
        let relation = relations::r_iss(
            params.constants(),
            statement.request,
            &params.rows(statement.x0)?,
            &tag_values(statement.id),
        )?;
        Self::verify_with(params, &relation, ProofKind::Issuance, ctx, proof)
    }

    fn prove_possession<R: RngCore + CryptoRng + ?Sized>(
        params: &LatticeParams,
        vk: &VSISVerificationKey,
        usk: &Ternary,
        cred: &VSISCredential,
        ctx: &[u8],
        rng: &mut R,
    ) -> Result<((), LatticeProof), Error> {
        Self::admissible(vk)?;
        if !VSIS::verify(&params.sigma, vk, usk, cred) {
            return Err(Error::WitnessDoesNotSatisfyRelation);
        }
        let k = params.constants();
        let relation = relations::r_possess(k, vk.h())?;
        let witness = relations::possess_witness(&k.rings, cred, usk)?;
        let proof = Self::prove_with(params, &relation, ProofKind::Possession, &witness, ctx, rng)?;
        Ok(((), proof))
    }

    fn check_possession_proof(
        params: &LatticeParams,
        vk: &VSISVerificationKey,
        _show: &(),
        ctx: &[u8],
        proof: &LatticeProof,
    ) -> Result<(), Error> {
        Self::admissible(vk)?;
        proof.within(ProofKind::Possession)?;
        let relation = relations::r_possess(params.constants(), vk.h())?;
        Self::verify_with(params, &relation, ProofKind::Possession, ctx, proof)
    }

    fn proof_compact_size(proof: &LatticeProof) -> usize {
        proof.encoded_size()
    }

    /// The exact sizes of the fixed-size leaves (a tag 336 bytes, `σ*` empty, `Ĉ` 2560, `σ̂`
    /// 5376), and for a proof its 4-byte length and the bound of its kind
    /// ([`LatticeProof::max_bytes`]).
    fn max_leaf_bytes(leaf: Leaf) -> usize {
        match leaf {
            Leaf::Tag => LWRTag::BYTES,
            Leaf::Show => 0,
            Leaf::Request => Rq::BYTES,
            Leaf::PreCredential => VSISPreCredential::BYTES,
            Leaf::Proof(kind) => LENGTH_BYTES + LatticeProof::max_bytes(kind),
        }
    }

    fn serialize_proof_compact<W: Write>(
        kind: ProofKind,
        proof: &LatticeProof,
        writer: W,
    ) -> Result<(), Error> {
        let max = LatticeProof::max_bytes(kind);
        if proof.len() > max {
            return Err(Error::LengthMismatch {
                expected: max,
                actual: proof.len(),
            });
        }
        Ok(proof.write_bounded(writer, max)?)
    }

    fn deserialize_proof_compact<R: Read>(
        kind: ProofKind,
        reader: R,
    ) -> Result<LatticeProof, Error> {
        Ok(LatticeProof::read_bounded(
            reader,
            LatticeProof::max_bytes(kind),
        )?)
    }
}

#[cfg(test)]
mod tests {
    use sha2::{Digest, Sha256};

    use super::*;
    use crate::serialization::{from_bytes, to_bytes};

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    /// The encoding of the parameters, the digest of `pp`, an identifier point and a recipient
    /// point of this build, computed independently by `tools/lattice/ref_contexts.py` (Python
    /// hashlib over the documented framing, reading the embedded sets), with `--plain` for the
    /// plain build.
    #[test]
    fn known_answers_of_the_digest_and_the_points() {
        // (encoding bytes, its SHA-256, the pp digest, the identifier digest, the recipient digest)
        let (bytes, encoding, pp, identifier, recipient) = if STRAIGHT_LINE {
            (
                13_319,
                "dc88a6b25cc276ff679d826a34501fa1fcd86f3709e100f79a55b61e0969e901",
                "8da1f24b0fd228f2d91355d4000d8f80a7319a8bedf78d73606abcb8ba67a8c6",
                "1863d36961913c03444e2a54ba10090f1c33db0ba05d4eeba996a2b0a1727628",
                "605e2b468a168d41b20511d4831b49dd34134e891d396f8802b66f2a939c5761",
            )
        } else {
            (
                13_163,
                "da6a6903e9113c4e683154190cd73d0dec1e869d4a3ba4c8fd2db7e83fad4373",
                "41713d9df7435f52f92385e25eb0f07085b8e8d44301fde19395745c1ac7aaf3",
                "d8d8b3a1e46327596631a2afa95a7469f2bb5d4318fb2ec66fc08610736e3538",
                "adf57807ac7426481b307f96d020eadf00af83ee7e862aced4dea03f7bf97df2",
            )
        };
        let pcreds = LatticeProtocol::setup(b"PCS-LATTICE-KAT").unwrap();
        let params = to_bytes(pcreds.params()).unwrap();
        assert_eq!(params.len(), bytes);
        assert_eq!(pcreds.params().serialized_size(Compress::Yes), bytes);
        assert_eq!(hex(&Sha256::digest(&params)), encoding);
        assert_eq!(hex(&pcreds.public_parameters().digest().unwrap()), pp);
        assert_eq!(hex(pcreds.parameters_digest()), pp);
        let hvk = VSISVerificationKey::from_h(Rq::from_coeffs(&[5; D]).unwrap());
        let mut id = [0u8; LWRTag::BYTES];
        for (i, b) in id.iter_mut().take(256).enumerate() {
            *b = i as u8;
        }
        let id = LWRTag::from_bytes(&id).unwrap();
        let LatticePoint::Identifier(d) = pcreds.identifier_point(&hvk).unwrap() else {
            panic!("an identifier point")
        };
        assert_eq!(hex(&d), identifier);
        let LatticePoint::Request(d) = pcreds.recipient_point(&hvk, &id).unwrap() else {
            panic!("a recipient point")
        };
        assert_eq!(hex(&d), recipient);
    }

    /// The encoding of the parameters of one build is refused by the other: the plain decoder
    /// finds trailing bytes after the placement, and the extractable decoder misses the argument
    /// system and the pins of the extraction sets, or finds them changed.
    #[test]
    fn the_encoding_belongs_to_its_build() {
        let a = LatticeParams::derive(b"lattice/build").unwrap();
        let bytes = to_bytes(&a).unwrap();
        // the item that the extractable build appends: the argument system, then 4 pins
        let tail = {
            let mut t = Vec::new();
            ARGUMENT.to_vec().serialize_compressed(&mut t).unwrap();
            for pin in EXTRACTION_PINS {
                t.extend_from_slice(&pin);
            }
            t
        };
        if STRAIGHT_LINE {
            assert!(bytes.ends_with(&tail));
            let plain = &bytes[..bytes.len() - tail.len()];
            assert!(from_bytes::<LatticeParams>(plain).is_err());
            let mut other = bytes.clone();
            let last = other.len() - 1;
            other[last] ^= 1;
            assert!(from_bytes::<LatticeParams>(&other).is_err());
        } else {
            assert!(!bytes.ends_with(&tail));
            let mut extended = bytes.clone();
            extended.extend_from_slice(&tail);
            assert!(from_bytes::<LatticeParams>(&extended).is_err());
        }
        assert_eq!(from_bytes::<LatticeParams>(&bytes).unwrap(), a);
    }

    /// Clones share the caches; equality ignores them; the parameters of another label differ.
    #[test]
    fn parameters_compare_by_what_defines_them() {
        let a = LatticeParams::derive(b"lattice/params").unwrap();
        let b = a.clone();
        assert!(Arc::ptr_eq(&a.cache, &b.cache));
        let c = from_bytes::<LatticeParams>(&to_bytes(&a).unwrap()).unwrap();
        assert!(!Arc::ptr_eq(&a.cache, &c.cache));
        assert_eq!(a, c);
        assert_ne!(a, LatticeParams::derive(b"lattice/other").unwrap());
        assert_eq!(
            format!("{a:?}"),
            "LatticeParams { label: \"lattice/params\", .. }"
        );
        assert_eq!(
            a.matrix(&LatticePoint::Identifier([7; 32])),
            oracles::identifier_point(b"lattice/params", &[7; 32])
        );
        assert_eq!(
            a.matrix(&LatticePoint::Request([7; 32])),
            oracles::request_point(b"lattice/params", &[7; 32])
        );
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<LatticeParams>();
        assert_send_sync::<LatticeProtocol>();
    }
}
