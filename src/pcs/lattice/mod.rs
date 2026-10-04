//! The lattice (post-quantum) instantiation of the construction (construction.tex,
//! sec:pq-construction): `Σ-vSIS` ([`VSIS`]) with the short-key `Tag_LWR`
//! ([`LWR`]) and Jali proofs in place of the compiled sigma protocols, as
//! [`LatticePCS`], which implements [`PredicateCredentialSystem`]. Feature `lattice`.
//!
//! It realizes the same protocol box as [`PCS`](crate::pcs::PCS) (construction.tex,
//! "Modular threshold predicate credential construction", con:108-191) with the relations of
//! `relations`, the contexts of [`context`] and the fixed format of [`codec`]. The PRC of the
//! paper's appendix is out of scope: the trait has no `Req` and no session context `χ`, and the
//! main construction ignores `χ` (con:125-129).
//!
//! | paper (protocol box) | here |
//! |---|---|
//! | `Setup` (con:110-114), with $`c_0 = H_0(\texttt{"identity"})`$ (con:210) | [`PredicateCredentialSystem::setup`]; [`LatticePCS::from_public_parameters`] for a received `pp` |
//! | `HKeyGen`, `UKeyGen` (con:117-123) | [`PredicateCredentialSystem::helper_keygen`], [`PredicateCredentialSystem::user_keygen`] |
//! | `Attest`, `VerifyProofAtt` (con:131-153) | [`PredicateCredentialSystem::attest`], [`PredicateCredentialSystem::verify_attestation`] ([`LatticePCS::check_attestation`] names the reason) |
//! | `Prove`, `VerifyProof` with `CheckAtts_P` (con:155-173) | [`PredicateCredentialSystem::prove`], [`PredicateCredentialSystem::verify_proof`] ([`LatticePCS::check_proof`] names the reason) |
//! | `Issue`, `Unblind`, `VerifyCred` (con:175-189) | [`PredicateCredentialSystem::issue`], [`PredicateCredentialSystem::unblind`], [`PredicateCredentialSystem::verify_cred`] |
//! | `R_att`, `R_issue` (con:18-37) | the Jali statements of `relations` (an exact port of the validated harness) |
//! | $`ctx_j`$, $`ctx_0`$, $`ctx_{\mathsf{root}}`$ | [`LatticePCS::attestation_context`], [`LatticePCS::issuance_context`], [`LatticePCS::root_context`] |
//! | root credentials (rem:chain, con:417) | [`LatticePCS::root_request`], [`LatticePCS::verify_root_request`], [`LatticePCS::issue_root`] |
//! | the issuance cap $`Q_{\max} = 2^{48}`$ (con:220-221) | the counter of [`VSISSigningKey`](crate::cred::vsis::VSISSigningKey) ([`Error::IssuanceCapReached`]) |
//!
//! # In formulas
//!
//! With $`c_0 = H_0(\texttt{"identity"})`$ and $`s_i = H_0(\langle id_i\rangle)`$, both
//! $`m \times n`$ matrices of $`\mathbb Z_{q_t}`$ (con:210), a user's public values are
//! rounded-LWR tags of its ternary key: $`id_i = \lfloor c_0\, usk_i\rceil_p`$, an attester's tag
//! $`id_{j \to i} = \lfloor s_i\, usk_j\rceil_p`$ and the self-exclusion tag
//! $`id_{i \to i} = \lfloor s_i\, usk_i\rceil_p`$. An attestation proves, in `R_att`, possession of
//! a `Σ-vSIS` credential on $`(usk_j, \phi_j, x_{0,j})`$ under $`h = \mathsf{hvk}`$ together with
//! the tag clauses of $`id_{j \to i}`$ on the same $`usk_j`$:
//!
//! ```math
//! \bigl(s_0 + h s_1 - b_u\,usk_j - B_r x_{0,j} - b_\phi \phi_j\bigr)(v - x_1) = 1,\qquad
//! s_i\, usk_j + e = \gamma\, id_{j \to i} \bmod q_t,\qquad \|e\|_\infty \le \lfloor\gamma/2\rfloor,
//! ```
//!
//! with $`\|s\|^2 \le \lfloor\beta_s^2\rfloor`$ and $`\|x_1\|_\infty, \|usk_j\|_\infty, \|x_{0,j}\|_\infty \le 1`$,
//! every bound proven EXACTLY. An issuance proof proves, in `R_issue`, the opening
//! $`C = b_u\,usk + B_r x_0`$ and the tag clauses of $`id_i`$ at $`c_0`$ and of $`id_{i \to i}`$ at
//! $`s_i`$, all on one $`usk`$. `CheckAtts_P` accepts $`k`$ attestations iff each verifies, their
//! tags are pairwise distinct, $`id_{i \to i}`$ is not among them and $`P(\phi_1, \dots, \phi_k) = 1`$.
//!
//! # What the paper claims, and what this code can claim
//!
//! The paper states the theorems of sec:security for `Σ-vSIS` with `Tag_LWR` "through
//! thm:pq-security" (con:299), for an online-extractable argument system in the ROM, under the
//! assumptions recorded there (`IntGenISIS_f` in the falsifiable form of lem:base-vsis, under the
//! issuance cap; MSIS; a hiding issuance encoding; short-secret LWR; the tag rounding errors
//! extracted exactly). Two gaps separate this implementation from that statement: Jali compiles
//! LNP22-style proofs with Fiat-Shamir, whose extraction is by rewinding (not online), and
//! `thm:pq-security` is referenced but not stated in the paper. **No security theorem covers this
//! code yet.** It implements the box faithfully and makes no claim beyond it.
//!
//! # Implementation notes
//!
//! How the code realizes the box, and what it adds. None of it changes what honest parties
//! compute.
//!
//! * **One real helper key.** `HKeyGen` is `Σ-vSIS.KeyGen`: an NTRU trapdoor from
//!   `ntru-trapdoor` (`TrapGen`), and `Issue` / `issue_root` call `BlindIssue`, i.e. `SampPre`
//!   with fresh coins, on the issuance encoding $`C`$ carried by the verified proof. Every
//!   credential of a helper is a preimage under the same $`h`$, and each preimage is checked
//!   exactly ($`s_0 + h s_1 = t`$ in integer arithmetic, and its norm) before it leaves the key
//!   (bb:864; [`crate::cred::vsis`], "The implemented preimage sampler"). The trapdoor is a
//!   function of the RNG's output: the helper's RNG must be a CSPRNG seeded by the operating
//!   system (the examples below are seeded for reproducibility only).
//! * **The issuance cap** (con:220-221). The signing key counts its `SampPre` calls and refuses
//!   from $`Q_{\max} = 2^{48}`$ on ([`Error::IssuanceCapReached`]); the count is part of the
//!   encoding of `hsk` ([`HelperSecretKey::to_bytes_reserving`] stores it ahead of issuance). The
//!   count lives in one in-memory value: a deployment runs one live instance per stored `hsk`.
//!   Rotation is the helper's: a new `HKeyGen` and a new `hvk`. Accepting the credentials of
//!   earlier keys as attesters (con:221) needs a `VerifyProofAtt` that takes all of a helper's
//!   keys, which the trait's single `hvk` does not express; it is not implemented.
//! * **Bounded proofs.** A Jali proof inside an attestation, an issuance proof or a root request
//!   has at most twice the estimated size of its parameter set ([`ATT_PROOF_MAX_BYTES`],
//!   [`ISSUE_PROOF_MAX_BYTES`]); the decoders and the verifiers refuse a longer one before any
//!   work on it (honest proofs have 0.95 to 1 times the estimate).
//! * **$`\mathcal V_\mathsf{pp}`$** is every canonically encoded $`h`$ (con:194), which every
//!   [`VSISVerificationKey`] is; the key checks of the box therefore refuse only a wiped key.
//! * **Public checks before any proof** (performance first, then soundness). `VerifyProof` runs,
//!   in this order: $`f_k \in \mathcal F`$ (threshold at least 1), the number of attestations,
//!   $`\mathsf{hvk} \in \mathcal V_\mathsf{pp}`$, `ValidTag` on $`id_i`$ and $`id_{i \to i}`$
//!   (con:171), the canonicity of $`C`$, `ValidTag` on every $`id_{j \to i}`$ (con:152), the
//!   pairwise distinctness of the attester tags, the self-exclusion check and the policy `P`;
//!   THEN the Jali verification of $`\pi_0`$ (about 0.6 s) and of the $`k`$ attestation proofs
//!   (about 3 s and 0.5-0.6 GiB each), one after the other, or in parallel with the feature
//!   `parallel` (next item). The verdict is the box's `CheckAtts_P ∧ Verify_FS`; only the reason
//!   reported for a proof that fails several checks can differ from the box's order.
//!   $`\phi_j \in \mathcal M_\mathsf{pub}`$ (con:151, the check without which an attestation is
//!   forgeable with no credential, bb:892) and `ValidTag` (bb:232) are invariants of the types
//!   [`BinaryPoly`] and [`LWRTag`]: a non-binary $`\phi`$ and a non-canonical tag $`T + pz`$
//!   cannot be represented, decoded or passed in. `ValidTag` is evaluated all the same, on every
//!   tag; $`\phi_j \in \mathcal M_\mathsf{pub}`$ holds by type and leaves nothing to evaluate (the
//!   verifier computes the constant $`b_\phi\phi_j`$ of `R_att` from the bits itself).
//! * **Parallel verification of the attestations** (feature `parallel`). The $`k`$ attestation
//!   proofs of `CheckAtts_P` are independent. With `parallel`, `VerifyProof` (and so `Issue`)
//!   and `Prove` verify them on the rayon pool of the calling thread (the global pool, unless the
//!   call runs inside `ThreadPool::install`), in batches of $`n`$ for a pool of $`n`$ threads:
//!   each batch with rayon's short-circuiting `all`, and no batch after a failure. Without the
//!   feature they are verified one after the other, up to the first failure. Either way the result
//!   is `Ok` iff every attestation verifies, and [`Error::InvalidAttestation`] otherwise, whichever
//!   attestations fail: only the time changes (at $`k = 5`$ on ten cores of an Apple M4,
//!   `VerifyProof` takes about 4 s, 3.8-4.1 s over four runs, against 8.1-8.5 s with Jali's
//!   parallelism alone and 15.4 s at one thread). A verification that has started runs to its
//!   end even when another one fails, so a call whose first attestation fails can still verify
//!   up to $`\min(k, n)`$ of them, where the sequential loop verifies one. **Memory**: a call
//!   holds up to $`\min(k, n)`$ Jali verifications of about 0.5 GiB each at once, and
//!   concurrent calls add up; at $`k = 5`$ the benchmark process peaked at 0.6 GiB with one
//!   thread, 1.0-1.1 GiB with two, 1.5 GiB with three and 2.0-2.5 GiB with five or ten. Bound it
//!   with the pool: `RAYON_NUM_THREADS=n`, or
//!   `rayon::ThreadPoolBuilder::new().num_threads(n).build()` and
//!   `pool.install(|| pcs.issue(..))`; one thread verifies one at a time, as without the feature.
//!   A single parallel iterator over the $`k`$ attestations would not respect this bound: rayon
//!   lets a thread that waits inside one verification start another. Each verification is also
//!   parallel inside Jali (the feature enables Jali's `parallel`), on the same pool; rayon's work
//!   stealing schedules both levels, so threads that a batch leaves idle help inside its
//!   verifications. The policy `P` runs once, on the calling thread, before any proof, and need
//!   not be `Sync`: the threads share only `pp`, the parameter sets, the caches, `hvk`, $`id_i`$,
//!   the rows of $`s_i`$ and the attestations.
//! * **`UKeyGen`** samples $`usk`$ and returns $`(id, usk)`$; it does not evaluate
//!   $`id_{i \to i}`$ (con:123), whose only role in the box is the restart on an undefined tag:
//!   `Tag_LWR` is total on its key space.
//! * **`Prove` checks $`id = \mathsf{Tag}(usk, c_0)`$** ([`Error::IdentifierMismatch`]), the
//!   first condition of `R_PCS`, and builds `R_issue` and $`ctx_0`$ with the code the verifier
//!   uses. Its `CheckAtts_P` verifies every attestation in full before $`\pi_0`$ is proven.
//! * **`Unblind` verifies once.** The box of `Σ-vSIS` verifies inside its own `Unblind`
//!   (bb:846-849), so the construction's `Unblind` fails closed
//!   ([`Error::InvalidPreCredential`]) without a second `VerifyCred`.
//! * **A helper key belongs to ONE deployment** ([`HelperSecretKey`] records the digest of `pp`);
//!   `Issue` and `issue_root` refuse it under another one ([`Error::InvalidKey`]).
//! * **Fresh coins everywhere.** Every Jali proof gets a fresh 32-byte seed from the caller's RNG
//!   (`prove_bytes_with_seed`), every `SampPre` call another one (bb:864), every `TrapGen` another
//!   one; a `RestartLimit` of Jali is retried with a new seed.
//! * **Caches.** A [`LatticePCS`] keeps the checked parameter sets, the rings of the statements,
//!   the elements of `pp_Σ` as Jali polynomials and the rows of $`c_0`$; each call computes
//!   $`s_i = H_0(\langle id_i\rangle)`$ (about 0.6 ms) and its rows once and shares them between
//!   the $`k`$ attestations and $`\pi_0`$. Compiled statements cannot be cached: every proof has
//!   its own public constants, and Jali has no shape-level compilation.
//! * **Side channels.** Performance comes first. Jali, `SampPre`'s floating-point arithmetic and
//!   rejection loops, `TrapGen` and the rejection sampling of ternary polynomials run in variable
//!   time ([`crate::lattice`], "Side channels").
//!
//! # Example
//!
//! Two root members endorse a newcomer, as in [`crate::pcs::construction`], at the lattice
//! instantiation. Each attestation is a Jali proof of about 83 KB that takes seconds to prove
//! and to verify, and about 0.5 GiB of memory; the example is compiled but not run by the
//! documentation tests (`tests/lattice_pcs.rs` runs it in release).
//!
//! ```no_run
//! use predicate_credential_system::{
//!     LatticePCS,
//!     pcs::{Predicate, PredicateCredentialSystem, SetupParams},
//! };
//! use rand::{SeedableRng, rngs::StdRng};
//!
//! // seeded so that the example is reproducible; a helper uses `rand::rngs::OsRng`, since its
//! // trapdoor is a function of the RNG's output
//! let mut rng = StdRng::seed_from_u64(1);
//! let f_root = Predicate::root(b"founders".to_vec());
//! let f = Predicate::new(2, b"members".to_vec());
//! let setup = SetupParams::new(b"example deployment".to_vec());
//! let pcs = LatticePCS::setup(setup)?;
//! // a helper should restrict the attesters it counts
//! let pcs = LatticePCS::from_public_parameters(
//!     pcs.public_parameters().clone(),
//!     pcs.allow_list([&f_root, &f]),
//! )?;
//! let (hvk, hsk) = pcs.helper_keygen(&mut rng); // TrapGen
//!
//! // Root credentials: the helper admits two founders out of band. It never sees a user key.
//! let mut founders = Vec::new();
//! for _ in 0..2 {
//!     let (id_j, usk_j) = pcs.user_keygen(&mut rng)?;
//!     let (request, state) = pcs.root_request(&hvk, &f_root, &id_j, &usk_j, &mut rng)?;
//!     let pre = pcs.issue_root(&hvk, &hsk, &f_root, &id_j, &request, &mut rng)?;
//!     let cred_j = pcs.unblind(&hvk, &usk_j, &f_root, &pre, &state)?;
//!     founders.push((usk_j, cred_j));
//! }
//!
//! // A newcomer collects one attestation per founder for its identifier ...
//! let (id, usk) = pcs.user_keygen(&mut rng)?;
//! let mut attestations = Vec::new();
//! for (usk_j, cred_j) in &founders {
//!     let att = pcs.attest(&hvk, usk_j, &f_root, cred_j, &id, &mut rng)?;
//!     assert!(pcs.verify_attestation(&hvk, &id, &att));
//!     attestations.push(att);
//! }
//! // ... proves that it holds them, and the helper issues on the proof alone.
//! let (proof, state) = pcs.prove(&hvk, &f, &id, &usk, &attestations, &mut rng)?;
//! let pre = pcs.issue(&hvk, &hsk, &f, &id, &proof, &mut rng)?; // VerifyProof, then BlindIssue
//! let cred = pcs.unblind(&hvk, &usk, &f, &pre, &state)?;
//! assert!(pcs.verify_cred(&hvk, &usk, &f, &cred));
//! # Ok::<(), predicate_credential_system::Error>(())
//! ```

pub mod codec;
pub mod context;
pub(crate) mod relations;
pub mod types;

use core::fmt;
use std::collections::HashSet;

use ark_serialize::Valid;
use ark_std::rand::{CryptoRng, RngCore};
use jali::statement::Statement;

use self::relations::{Constants, TagRows, tag_values};
pub use self::types::{
    Attestation, Credential, IssuanceProof, IssuanceState, Proof, PublicParameters, RootRequest,
    UserSecretKey,
};
use super::{
    HelperSecretKey, PredicateCredentialSystem,
    predicate::{AcceptAll, AllowList, AttributePolicy, Predicate},
    types::SetupParams,
};
use crate::{
    cred::{
        CredentialBase, VSIS,
        vsis::{VSISHiddenMessage, VSISIssuanceState, VSISPreCredential, VSISVerificationKey},
    },
    error::Error,
    kiprf::{
        KIPRF,
        lwr::{LWR, LWRTag, TagMatrix},
    },
    lattice::{
        BinaryPoly, Rq, Ternary, oracles,
        sets::{ATT_PROOF_MAX_BYTES, ISSUE_PROOF_MAX_BYTES, ParameterSets},
    },
};

/// The lattice construction: a predicate credential system for the threshold predicates
/// [`Predicate`] with the public attribute policy `P` over the disclosed labels
/// $`\phi_j \in \{0,1\}^{1024}`$ ([`BinaryPoly`]). A value of this type is `pp` together with
/// the policy, the checked parameter sets of Jali and the caches of the module docs; it is
/// `Send + Sync` when `P` is (as [`AcceptAll`] and [`AllowList`] are), and its algorithms take
/// `&self`. The parallel attestation verification of the feature `parallel` does not need `P` to
/// be `Sync` (module docs).
pub struct LatticePCS<P = AcceptAll> {
    pp: PublicParameters,
    /// The digest of `pp` ([`context`]), computed once; it leads every context.
    pp_digest: [u8; 32],
    policy: P,
    sets: ParameterSets,
    /// The rings, `pp_Σ` lifted to Jali and the rows of `c_0` (`relations`).
    constants: Constants,
}

impl<P> fmt::Debug for LatticePCS<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("LatticePCS")
            .field("label", &String::from_utf8_lossy(&self.pp.label))
            .field("pp_digest", &self.pp_digest)
            .finish_non_exhaustive()
    }
}

/// What `Prove` steps 1-3 produce, shared with the root path: $`C`$, $`id_{i \to i}`$,
/// $`\pi_0`$ and $`st_{\mathsf{iss}}`$.
struct IssuanceParts {
    c: Rq,
    t0: LWRTag,
    proof: Proof,
    state: IssuanceState,
}

/// What `VerifyProofAtt` reads of a [`LatticePCS`]: everything but the policy, borrowed. Its parts
/// are `Sync`, so the attestation verifications of `CheckAtts_P` share one view across the threads
/// of the feature `parallel` without a `Sync` bound on `P` (a custom policy, e.g. a closure over
/// an `Rc`, need not be `Sync`).
#[derive(Clone, Copy)]
struct AttestationVerifier<'a> {
    pp: &'a PublicParameters,
    pp_digest: &'a [u8; 32],
    sets: &'a ParameterSets,
    constants: &'a Constants,
}

impl AttestationVerifier<'_> {
    /// `R_att` for $`(\mathsf{hvk}, \phi, id_{j \to i}, s_i)`$, with the constant
    /// $`b_\phi\phi`$ from the prepared $`b_\phi`$ of `pp_Σ`.
    fn statement(
        &self,
        hvk: &VSISVerificationKey,
        phi: &BinaryPoly,
        tag: &LWRTag,
        rows: &TagRows,
    ) -> Result<Statement, Error> {
        relations::r_att(
            self.constants,
            hvk.h(),
            &self.pp.pp_sigma.phi_term(phi),
            rows,
            &tag_values(tag),
        )
    }

    /// `VerifyProofAtt` step 2 for a checked `hvk` and `id`, and the rows of $`s_i = H_0(id)`$.
    fn check(
        &self,
        hvk: &VSISVerificationKey,
        id: &LWRTag,
        rows: &TagRows,
        att: &Attestation,
    ) -> Result<(), Error> {
        if !LWR.valid_tag(&att.tag) {
            return Err(Error::InvalidTag);
        }
        // no honest proof comes near the bound: refuse garbage before compiling R_att (0.3 s)
        if att.proof.len() > ATT_PROOF_MAX_BYTES {
            return Err(Error::InvalidProof);
        }
        let ctx = context::attestation_context_of(self.pp_digest, hvk, id, &att.phi, &att.tag);
        let statement = self.statement(hvk, &att.phi, &att.tag, rows)?;
        relations::verify(
            &statement,
            &self.sets.att,
            self.pp.jali_pp_seed,
            att.proof.as_bytes(),
            &ctx,
        )
    }

    /// Whether [`Self::check`] accepts every attestation, decided on the rayon pool of the calling
    /// thread in batches of the pool's width $`n`$: rayon's short-circuiting `all` within a batch,
    /// and no batch after a failing one. A batch holds at most $`n`$ verifications, so at most
    /// $`\min(k, n)`$ run at once; one parallel iterator over all $`k`$ would let a thread that
    /// waits inside one verification (Jali is parallel too) start another, beyond $`n`$.
    #[cfg(feature = "parallel")]
    fn check_all(
        &self,
        hvk: &VSISVerificationKey,
        id: &LWRTag,
        rows: &TagRows,
        attestations: &[Attestation],
    ) -> bool {
        use rayon::prelude::*;
        let width = rayon::current_num_threads().max(1);
        attestations.chunks(width).all(|batch| {
            batch
                .par_iter()
                .all(|att| self.check(hvk, id, rows, att).is_ok())
        })
    }
}

impl<P> LatticePCS<P> {
    /// The checks every constructor runs, then the digest and the caches.
    fn assemble(pp: PublicParameters, policy: P) -> Result<Self, Error> {
        let sets = ParameterSets::load()?;
        let pp_digest = pp.digest();
        let constants = Constants::new(&pp)?;
        Ok(Self {
            pp,
            pp_digest,
            policy,
            sets,
            constants,
        })
    }

    /// A received `pp`, accepted only if it is what `Setup` derives from its own label
    /// (transparent setup: nothing of `pp` is chosen by anyone), with the verifier's own policy.
    ///
    /// Implementation note: the elements of `pp_Σ` must come "from public randomness, so that
    /// nobody, the helper included, knows a short relation among them" (bb:795), and the matrices
    /// of Jali's commitments from a public seed; well-formed parameters are not good enough.
    ///
    /// # Errors
    /// [`Error::InvalidPublicParameters`] if a component of `pp` is not the one derived from the
    /// label; [`Error::LatticeBackend`] if the embedded parameter sets do not load.
    pub fn from_public_parameters(pp: PublicParameters, policy: P) -> Result<Self, Error> {
        let derived = PublicParameters::derive(&pp.label)?;
        if pp.pp_sigma != derived.pp_sigma {
            return Err(Error::InvalidPublicParameters(
                "pp_Σ is not expanded from the deployment label",
            ));
        }
        if pp.c0 != derived.c0 {
            return Err(Error::InvalidPublicParameters(
                "c_0 is not H_0(\"identity\") of the deployment label",
            ));
        }
        if pp.jali_pp_seed != derived.jali_pp_seed {
            return Err(Error::InvalidPublicParameters(
                "Jali's pp_seed is not expanded from the deployment label",
            ));
        }
        // `pp_tag` is the unit struct of the constants: nothing to compare
        Self::assemble(derived, policy)
    }

    /// `pp`.
    #[must_use]
    pub fn public_parameters(&self) -> &PublicParameters {
        &self.pp
    }

    /// The deployment label.
    #[must_use]
    pub fn label(&self) -> &[u8] {
        &self.pp.label
    }

    /// The digest of `pp` that leads every context ([`PublicParameters::digest`]).
    #[must_use]
    pub fn parameters_digest(&self) -> &[u8; 32] {
        &self.pp_digest
    }

    /// The attribute policy `P`.
    #[must_use]
    pub fn policy(&self) -> &P {
        &self.policy
    }

    /// The checked parameter sets of Jali.
    #[must_use]
    pub fn parameter_sets(&self) -> &ParameterSets {
        &self.sets
    }

    /// $`\phi = \mathsf{EncPred}(f)`$ in this deployment (con:65; [`oracles::pred_enc`]).
    #[must_use]
    pub fn enc_pred(&self, f: &Predicate) -> BinaryPoly {
        oracles::pred_enc(&self.pp.label, f)
    }

    /// The policy that admits attesters whose credentials were issued under one of
    /// `predicates` in this deployment: the allow list over their `EncPred(f)`. Hand it to
    /// [`Self::from_public_parameters`] (or to `Setup`) to obtain the verifier that enforces it
    /// (`docs/operating-a-helper.md`: do not run a helper with `P ≡ 1`).
    #[must_use]
    pub fn allow_list<'a>(
        &self,
        predicates: impl IntoIterator<Item = &'a Predicate>,
    ) -> AllowList<BinaryPoly> {
        AllowList::new(predicates.into_iter().map(|f| self.enc_pred(f)))
    }

    /// $`id = \mathsf{Tag}(usk, c_0)`$ (`UKeyGen`, con:122).
    ///
    /// # Errors
    /// [`Error::UndefinedTag`] for a wiped key (the only key outside the key space).
    pub fn identity(&self, usk: &UserSecretKey) -> Result<LWRTag, Error> {
        LWR.eval(&usk.0, &self.pp.c0).ok_or(Error::UndefinedTag)
    }

    /// $`s = H_0(\langle id\rangle)`$, the point at which the tags of the attesters of `id`, and
    /// the self-exclusion tag of `id`, are evaluated (con:134, con:157; about 0.6 ms).
    #[must_use]
    pub fn tag_point(&self, id: &LWRTag) -> TagMatrix {
        oracles::tag_point(&self.pp.label, id)
    }

    /// $`\mathsf{hvk} \in \mathcal V_\mathsf{pp}`$ (con:149, con:169, con:182, con:188): every
    /// canonical $`h`$ (con:194), i.e. every key that was not wiped.
    fn check_key(&self, hvk: &VSISVerificationKey) -> Result<(), Error> {
        if VSIS::is_well_formed_key(&self.pp.pp_sigma, hvk) {
            Ok(())
        } else {
            Err(Error::InvalidKey)
        }
    }

    /// The rows of a tag matrix as Jali polynomials (`relations`).
    fn rows(&self, a: &TagMatrix) -> Result<TagRows, Error> {
        TagRows::new(&self.constants.rings, a)
    }

    /// The parts of `self` that `VerifyProofAtt` reads, without the policy.
    fn attestation_verifier(&self) -> AttestationVerifier<'_> {
        AttestationVerifier {
            pp: &self.pp,
            pp_digest: &self.pp_digest,
            sets: &self.sets,
            constants: &self.constants,
        }
    }

    /// `R_att` for $`(\mathsf{hvk}, \phi, id_{j \to i}, s_i)`$ (`AttestationVerifier::statement`),
    /// the statement that `Attest` proves and `VerifyProofAtt` verifies.
    fn attestation_statement(
        &self,
        hvk: &VSISVerificationKey,
        phi: &BinaryPoly,
        tag: &LWRTag,
        rows: &TagRows,
    ) -> Result<Statement, Error> {
        self.attestation_verifier().statement(hvk, phi, tag, rows)
    }

    /// `R_issue` for $`(C, (c_0, id), (s_i, id_{i \to i}))`$, the same for `Prove`, `VerifyProof`
    /// and the root path.
    fn issuance_statement(
        &self,
        c: &Rq,
        id: &LWRTag,
        t0: &LWRTag,
        rows: &TagRows,
    ) -> Result<Statement, Error> {
        relations::r_issue(
            &self.constants,
            c,
            [
                (&self.constants.c0, &tag_values(id)),
                (rows, &tag_values(t0)),
            ],
        )
    }
}

impl<P: AttributePolicy<BinaryPoly>> LatticePCS<P> {
    /// `VerifyProofAtt(hvk, id, att_j)` (con:149-153) with the reason for a rejection: `Ok(())`
    /// iff [`PredicateCredentialSystem::verify_attestation`] returns `true`. A function of public
    /// data; never panics.
    ///
    /// # Errors
    /// [`Error::InvalidKey`] for a wiped `hvk`; [`Error::InvalidTag`] if
    /// `ValidTag(id, c_0) = 0` or `ValidTag(T_j, s) = 0` (never, for values of [`LWRTag`]);
    /// [`Error::InvalidProof`] if $`\pi_j`$ is longer than [`ATT_PROOF_MAX_BYTES`] or does not
    /// verify under the rebuilt $`ctx_j`$.
    pub fn check_attestation(
        &self,
        hvk: &VSISVerificationKey,
        id: &LWRTag,
        att: &Attestation,
    ) -> Result<(), Error> {
        // 1. Reject malformed input: hvk ∉ V_pp (and ValidTag of the identifier, implementation
        //    note), φ_j ∉ M_pub (a type invariant of BinaryPoly).
        self.check_key(hvk)?;
        if !LWR.valid_tag(id) {
            return Err(Error::InvalidTag);
        }
        // 2. s_i = H_0(id), ctx_j as in Attest, ValidTag(T_j, s_i) ∧ Verify_FS(ctx_j, π_j)
        let rows = self.rows(&self.tag_point(id))?;
        self.check_attestation_at(hvk, id, &rows, att)
    }

    /// `VerifyProofAtt` step 2 for a checked `hvk` and `id`, and the rows of $`s_i = H_0(id)`$
    /// (`AttestationVerifier::check`).
    fn check_attestation_at(
        &self,
        hvk: &VSISVerificationKey,
        id: &LWRTag,
        rows: &TagRows,
        att: &Attestation,
    ) -> Result<(), Error> {
        self.attestation_verifier().check(hvk, id, rows, att)
    }

    /// The public part of `CheckAtts_P` (con:94-106): `ValidTag` of every attester tag (and the
    /// length bound of every attestation proof, which `VerifyProofAtt` would refuse anyway),
    /// their pairwise distinctness, the self-exclusion of $`id_{i \to i}`$ and the policy, all
    /// cheap.
    fn check_atts_public(&self, t0: &LWRTag, attestations: &[Attestation]) -> Result<(), Error> {
        if attestations
            .iter()
            .any(|att| !LWR.valid_tag(&att.tag) || att.proof.len() > ATT_PROOF_MAX_BYTES)
        {
            return Err(Error::InvalidAttestation);
        }
        // |{id_{j→i}}| ≠ k: equal tags are equal encodings (an LWRTag IS its encoding)
        let mut tags = HashSet::with_capacity(attestations.len());
        if !attestations.iter().all(|att| tags.insert(&att.tag)) {
            return Err(Error::DuplicateAttester);
        }
        // id_{i→i} ∈ {id_{j→i}}
        if tags.contains(t0) {
            return Err(Error::SelfAttestation);
        }
        // P((φ_j)_j)
        let phis: Vec<BinaryPoly> = attestations.iter().map(|att| att.phi).collect();
        if self.policy.accepts(&phis) {
            Ok(())
        } else {
            Err(Error::PolicyRejected)
        }
    }

    /// The expensive part of `CheckAtts_P`: `VerifyProofAtt` of every attestation at the shared
    /// rows of $`s_i`$, [`Error::InvalidAttestation`] if one fails. Without the feature `parallel`
    /// one after the other, up to the first failure; with it in parallel, in batches of the
    /// pool's width (`AttestationVerifier::check_all`; module docs, "Parallel verification of the
    /// attestations"), with the same result for every input, since `VerifyProofAtt` never panics
    /// (were it to panic on some input, the two could differ only between that panic and
    /// [`Error::InvalidAttestation`], never in accepting). Each Jali verification of `R_att` holds
    /// about 0.5-0.6 GiB.
    fn check_attestation_proofs(
        &self,
        hvk: &VSISVerificationKey,
        id: &LWRTag,
        rows: &TagRows,
        attestations: &[Attestation],
    ) -> Result<(), Error> {
        #[cfg(not(feature = "parallel"))]
        for att in attestations {
            if self.check_attestation_at(hvk, id, rows, att).is_err() {
                return Err(Error::InvalidAttestation);
            }
        }
        #[cfg(feature = "parallel")]
        if !self
            .attestation_verifier()
            .check_all(hvk, id, rows, attestations)
        {
            return Err(Error::InvalidAttestation);
        }
        Ok(())
    }

    /// `VerifyProof(hvk, f_k, id, π)` (con:168-173) with the reason for a rejection: `Ok(())` iff
    /// [`PredicateCredentialSystem::verify_proof`] returns `true`. A function of public data;
    /// never panics. The public checks run before any Jali verification, and $`\pi_0`$ is
    /// verified before the $`k`$ attestation proofs (module docs, "Public checks before any
    /// proof"), which the feature `parallel` verifies in parallel (module docs, "Parallel
    /// verification of the attestations"); the verdict is the box's.
    ///
    /// # Errors
    /// [`Error::ZeroThreshold`] for a root predicate ($`f_k \notin \mathcal F`$);
    /// [`Error::WrongAttestationCount`] unless `π` carries exactly `f.threshold` attestations;
    /// [`Error::InvalidKey`] for a wiped `hvk`; [`Error::InvalidTag`] if `ValidTag(id, c_0) = 0`
    /// or `ValidTag(id_{i→i}, s_i) = 0`; [`Error::InvalidIssuanceEncoding`] for a wiped $`C`$;
    /// from `CheckAtts_P` [`Error::InvalidAttestation`], [`Error::DuplicateAttester`],
    /// [`Error::SelfAttestation`], [`Error::PolicyRejected`]; [`Error::InvalidProof`] if
    /// $`\pi_0`$ is longer than [`ISSUE_PROOF_MAX_BYTES`] or does not verify under the rebuilt
    /// $`ctx_0`$.
    pub fn check_proof(
        &self,
        hvk: &VSISVerificationKey,
        f: &Predicate,
        id: &LWRTag,
        proof: &IssuanceProof,
    ) -> Result<(), Error> {
        // 1. Reject malformed input: f_k ∉ F, hvk ∉ V_pp, a count other than k.
        if f.is_root() {
            return Err(Error::ZeroThreshold);
        }
        let actual = proof.attestations.len();
        if u32::try_from(actual).ok() != Some(f.threshold) {
            return Err(Error::WrongAttestationCount {
                expected: usize::try_from(f.threshold).unwrap_or(usize::MAX),
                actual,
            });
        }
        self.check_key(hvk)?;
        // 2. s_i = H_0(id), ValidTag(id, c_0) and ValidTag(id_{i→i}, s_i); C is canonical.
        if !LWR.valid_tag(id) || !LWR.valid_tag(&proof.t0) {
            return Err(Error::InvalidTag);
        }
        if proof.c.check().is_err() {
            return Err(Error::InvalidIssuanceEncoding);
        }
        // 3. CheckAtts_P, its public part first ...
        self.check_atts_public(&proof.t0, &proof.attestations)?;
        if proof.proof.len() > ISSUE_PROOF_MAX_BYTES {
            return Err(Error::InvalidProof);
        }
        let rows = self.rows(&self.tag_point(id))?;
        // ... then Verify_FS(ctx_0, π_0) under the REBUILT ctx_0 (the cheaper proof first) ...
        let ctx = self.issuance_context(hvk, f, id, &proof.c, &proof.t0, &proof.attestations);
        let statement = self.issuance_statement(&proof.c, id, &proof.t0, &rows)?;
        relations::verify(
            &statement,
            &self.sets.issue,
            self.pp.jali_pp_seed,
            proof.proof.as_bytes(),
            &ctx,
        )?;
        // ... and the k attestation proofs.
        self.check_attestation_proofs(hvk, id, &rows, &proof.attestations)
    }

    /// `Prove` steps 1-3 (con:155-163), shared with the root path. For `Some(attestations)`
    /// this is `Prove` proper: `CheckAtts_P`, the context $`ctx_0`$ and the set `issue`. For
    /// `None` it is the root request: no attestations, the context $`ctx_{\mathsf{root}}`$ and the
    /// set `issue-root`.
    fn prove_issuance<R: RngCore + CryptoRng + ?Sized>(
        &self,
        hvk: &VSISVerificationKey,
        f: &Predicate,
        id: &LWRTag,
        usk: &UserSecretKey,
        attestations: Option<&[Attestation]>,
        rng: &mut R,
    ) -> Result<IssuanceParts, Error> {
        self.check_key(hvk)?;
        // The first condition of R_PCS: (id, usk) ∈ supp(UKeyGen(pp)), i.e. id = Tag(usk, c_0);
        // the rounding error is the witness of the identifier's tag clauses.
        let (identity, e0) = LWR
            .eval_with_error(&usk.0, &self.pp.c0)
            .ok_or(Error::IdentifierMismatch)?;
        if identity != *id {
            return Err(Error::IdentifierMismatch);
        }
        // 1. φ := EncPred(f_k), s_i := H_0(id), id_{i→i} ← Tag(usk, s_i), CheckAtts_P = 1
        let phi = self.enc_pred(f);
        let s = self.tag_point(id);
        let (t0, e1) = LWR.eval_with_error(&usk.0, &s).ok_or(Error::UndefinedTag)?;
        let rows = self.rows(&s)?;
        if let Some(attestations) = attestations {
            self.check_atts_public(&t0, attestations)?;
            self.check_attestation_proofs(hvk, id, &rows, attestations)?;
        }
        // 2. (m_aux, ρ) = (x_0, x_0), x_0 uniform on {−1, 0, 1}^{ℓ_r d}; C ← Com(m_hid, φ; x_0)
        let x0 = [Ternary::sample(rng), Ternary::sample(rng)];
        let c = self.pp.pp_sigma.commitment(&usk.0, &x0)?;
        // 3. ctx_0 (or ctx_root), π_0 for R_issue, with the statement the verifier rebuilds
        let statement = self.issuance_statement(&c, id, &t0, &rows)?;
        let (ctx, params) = match attestations {
            Some(attestations) => (
                self.issuance_context(hvk, f, id, &c, &t0, attestations),
                &self.sets.issue,
            ),
            None => (
                self.root_context(hvk, f, id, &c, &t0),
                &self.sets.issue_root,
            ),
        };
        let witness = relations::issue_witness_of(&self.constants.rings, &usk.0, &x0, &e0, &e1)?;
        let proof = relations::prove(
            &statement,
            params,
            self.pp.jali_pp_seed,
            &witness,
            &ctx,
            rng,
        )?;
        Ok(IssuanceParts {
            c,
            t0,
            proof: Proof::from_bytes(proof)?,
            // st_iss = (m_hid, φ, ρ) = ((usk, x_0), φ, x_0), x_0 stored once
            state: IssuanceState {
                usk: usk.0.clone(),
                x0,
                phi,
            },
        })
    }

    /// USER: the root request $`(C, id_{i \to i}, \pi_0)`$ of rem:chain (con:417), computed "as in
    /// `Prove`, with the empty list of attestations and with $`ctx_0`$ replaced by
    /// $`ctx_{\mathsf{root}}`$", proven with the parameter set `issue-root`; and the issuance
    /// state for [`PredicateCredentialSystem::unblind`].
    ///
    /// `Prove`'s `CheckAtts_P` on the empty list is the policy's verdict $`P(())`$ alone
    /// (con:104), and it is not evaluated here: the allow lists and `AcceptAll` accept the empty
    /// list, and the issuer of a root request runs no policy (the admission is its out-of-band
    /// check). Only a custom policy that rejects the empty list would have stopped the request.
    ///
    /// # Errors
    /// [`Error::NotARootPredicate`] unless `f_root.threshold = 0`;
    /// [`Error::IdentifierMismatch`] if $`id \ne \mathsf{Tag}(usk, c_0)`$; [`Error::InvalidKey`]
    /// for a wiped `hvk`; [`Error::LatticeBackend`] if Jali fails.
    pub fn root_request<R: RngCore + CryptoRng + ?Sized>(
        &self,
        hvk: &VSISVerificationKey,
        f_root: &Predicate,
        id: &LWRTag,
        usk: &UserSecretKey,
        rng: &mut R,
    ) -> Result<(RootRequest, IssuanceState), Error> {
        if !f_root.is_root() {
            return Err(Error::NotARootPredicate);
        }
        let parts = self.prove_issuance(hvk, f_root, id, usk, None, rng)?;
        Ok((
            RootRequest {
                c: parts.c,
                t0: parts.t0,
                proof: parts.proof,
            },
            parts.state,
        ))
    }

    /// Verification of a root request with the reason for a rejection (rem:chain: "verifies
    /// $`\pi_0`$ under $`ctx_{\mathsf{root}}`$, including the public checks of `R_issue`, in
    /// particular `ValidTag(id, c_0) = 1` and `ValidTag(id_{i→i}, H_0(id)) = 1`"). It says that
    /// $`C`$, $`id`$ and $`id_{i \to i}`$ are under one key which the requester knows; it does NOT
    /// say that the requester should be admitted.
    ///
    /// # Errors
    /// [`Error::NotARootPredicate`], [`Error::InvalidKey`], [`Error::InvalidTag`],
    /// [`Error::InvalidIssuanceEncoding`] (a wiped $`C`$), [`Error::InvalidProof`] (also for a
    /// proof longer than [`ISSUE_PROOF_MAX_BYTES`]).
    pub fn check_root_request(
        &self,
        hvk: &VSISVerificationKey,
        f_root: &Predicate,
        id: &LWRTag,
        request: &RootRequest,
    ) -> Result<(), Error> {
        if !f_root.is_root() {
            return Err(Error::NotARootPredicate);
        }
        self.check_key(hvk)?;
        if !LWR.valid_tag(id) || !LWR.valid_tag(&request.t0) {
            return Err(Error::InvalidTag);
        }
        if request.c.check().is_err() {
            return Err(Error::InvalidIssuanceEncoding);
        }
        if request.proof.len() > ISSUE_PROOF_MAX_BYTES {
            return Err(Error::InvalidProof);
        }
        let rows = self.rows(&self.tag_point(id))?;
        let statement = self.issuance_statement(&request.c, id, &request.t0, &rows)?;
        let ctx = self.root_context(hvk, f_root, id, &request.c, &request.t0);
        relations::verify(
            &statement,
            &self.sets.issue_root,
            self.pp.jali_pp_seed,
            request.proof.as_bytes(),
            &ctx,
        )
    }

    /// Whether `request` is a valid root request for `(hvk, f_root, id)`. Never panics.
    #[must_use]
    pub fn verify_root_request(
        &self,
        hvk: &VSISVerificationKey,
        f_root: &Predicate,
        id: &LWRTag,
        request: &RootRequest,
    ) -> bool {
        self.check_root_request(hvk, f_root, id, request).is_ok()
    }

    /// HELPER, after its out-of-band admission check: `BlindIssue(sk, C, EncPred(f_root))` for
    /// a verified root request (rem:chain). One `SampPre` call under the issuance cap. Choose
    /// `f_root` yourself: "$`f_{\mathsf{root}}`$ is fixed by the issuer, never named by the
    /// requester".
    ///
    /// # Errors
    /// [`Error::InvalidKey`] if `hsk` does not hold `hvk` or belongs to another deployment;
    /// [`Error::NotARootPredicate`]; [`Error::InvalidProof`] if the request does not verify;
    /// [`Error::IssuanceCapReached`] at the cap; the other errors of `BlindIssue`.
    pub fn issue_root<R: RngCore + CryptoRng + ?Sized>(
        &self,
        hvk: &VSISVerificationKey,
        hsk: &HelperSecretKey<VSIS>,
        f_root: &Predicate,
        id: &LWRTag,
        request: &RootRequest,
        rng: &mut R,
    ) -> Result<VSISPreCredential, Error> {
        if hsk.hvk != *hvk || hsk.pp_digest != self.pp_digest {
            return Err(Error::InvalidKey);
        }
        if !f_root.is_root() {
            return Err(Error::NotARootPredicate);
        }
        if !self.verify_root_request(hvk, f_root, id, request) {
            return Err(Error::InvalidProof);
        }
        VSIS::blind_issue(
            &self.pp.pp_sigma,
            &hsk.sk,
            &request.c,
            &self.enc_pred(f_root),
            rng,
        )
    }
}

impl<P: AttributePolicy<BinaryPoly>> PredicateCredentialSystem for LatticePCS<P> {
    type SetupParams = SetupParams<P>;
    type Predicate = Predicate;
    /// `hvk = h`.
    type HelperVerificationKey = VSISVerificationKey;
    /// `hsk = (sk, hvk)` and the digest of `pp`.
    type HelperSecretKey = HelperSecretKey<VSIS>;
    /// $`id = \mathsf{Tag}(usk, c_0) \in \mathbb Z_p^m`$.
    type Identity = LWRTag;
    type UserSecretKey = UserSecretKey;
    /// $`cred = ((s, x_1), x_0)`$.
    type Credential = Credential;
    /// $`att_j = (id_{j \to i}, \phi_j, \pi_j)`$.
    type Attestation = Attestation;
    /// $`w = (att_j)_{j \in [k]}`$.
    type Witness = [Attestation];
    /// $`\pi = ((att_j)_j, C, id_{i \to i}, \pi_0)`$.
    type IssuanceProof = IssuanceProof;
    /// $`st_{\mathsf{iss}} = ((usk, x_0), \phi, x_0)`$.
    type IssuanceState = IssuanceState;
    /// $`\widehat{cred} = (s, x_1)`$.
    type PreCredential = VSISPreCredential;

    /// `Setup(1^λ) → pp` (con:110-114). Transparent: every parameter is derived from the
    /// deployment label `params.label` ([`PublicParameters`]); the embedded Jali parameter sets
    /// are loaded and checked. About 4 ms.
    ///
    /// # Errors
    /// [`Error::LatticeBackend`] if the embedded parameter sets do not load (never for this
    /// crate as published).
    fn setup(params: Self::SetupParams) -> Result<Self, Error> {
        let pp = PublicParameters::derive(&params.label)?;
        Self::assemble(pp, params.policy)
    }

    /// `HKeyGen(pp) → (hvk, hsk)` (con:117): `Σ-vSIS.KeyGen`, an NTRU trapdoor (`TrapGen`, about
    /// 6 ms). `hsk` also records the digest of THIS `pp` and holds the issuance counter.
    ///
    /// # Panics
    /// As [`CredentialBase::keygen`] for `Σ-vSIS`: only if `TrapGen` fails for 4 fresh seeds in a
    /// row, which does not happen in practice.
    fn helper_keygen<R: RngCore + CryptoRng + ?Sized>(
        &self,
        rng: &mut R,
    ) -> (Self::HelperVerificationKey, Self::HelperSecretKey) {
        let (vk, sk) = VSIS::keygen(&self.pp.pp_sigma, rng);
        let hsk = HelperSecretKey::new(sk, vk.clone(), self.pp_digest);
        (vk, hsk)
    }

    /// `UKeyGen(pp) → (id, usk)` (con:122-123): $`usk \gets \mathsf{TagKeyGen}`$, uniform on
    /// $`\{-1, 0, 1\}^n`$, and $`id = \mathsf{Tag}(usk, c_0)`$. `Tag_LWR` is total on its key
    /// space, so there is no restart (module docs).
    ///
    /// # Errors
    /// None occur; the signature is the trait's.
    fn user_keygen<R: RngCore + CryptoRng + ?Sized>(
        &self,
        rng: &mut R,
    ) -> Result<(Self::Identity, Self::UserSecretKey), Error> {
        let usk = UserSecretKey(LWR.keygen(rng));
        let id = self.identity(&usk)?;
        Ok((id, usk))
    }

    /// `Attest(hvk, usk_j, f_j, cred_j, id) → att_j / ⊥` (con:131-140): the tag
    /// $`id_{j \to i} = \mathsf{Tag}(usk_j, H_0(id))`$ and a Jali proof for `R_att` under
    /// $`ctx_j`$ (about 6 s and 0.5 GiB at one thread).
    ///
    /// As in the box, `Attest` does not verify its own output. On a credential that does not
    /// belong to `(usk_j, f_j)` the honest prover's witness check refuses
    /// ([`Error::WitnessDoesNotSatisfyRelation`]) before any proving work.
    ///
    /// # Errors
    /// [`Error::InvalidTag`] if `ValidTag(id, c_0) = 0` (never for an [`LWRTag`]);
    /// [`Error::UndefinedTag`] for a wiped key; [`Error::InvalidMessage`] or
    /// [`Error::InvalidCredential`] for wiped parts of the credential;
    /// [`Error::WitnessDoesNotSatisfyRelation`] if `cred_j` is not a credential of
    /// `(usk_j, f_j)` under `hvk`; [`Error::LatticeBackend`] if Jali fails.
    fn attest<R: RngCore + CryptoRng + ?Sized>(
        &self,
        hvk: &Self::HelperVerificationKey,
        usk: &Self::UserSecretKey,
        f: &Self::Predicate,
        cred: &Self::Credential,
        id: &Self::Identity,
        rng: &mut R,
    ) -> Result<Self::Attestation, Error> {
        // 1. cred_j = (cred_Σ, x_0), φ_j := EncPred(f_j), s_i := H_0(id),
        //    id_{j→i} ← Tag(usk_j, s_i) (with its rounding error, the witness of the tag clauses)
        if !LWR.valid_tag(id) {
            return Err(Error::InvalidTag);
        }
        let phi = self.enc_pred(f);
        let s = self.tag_point(id);
        let (tag, e) = LWR.eval_with_error(&usk.0, &s).ok_or(Error::UndefinedTag)?;
        // 2. m_hid := (usk_j, x_0); (cred* = ⊥, ω = cred_Σ) ← ReRand(hvk, Enc(m_hid, φ_j), cred_Σ)
        let m_hid = VSISHiddenMessage::new(usk.0.clone(), cred.x0.clone());
        let m = VSIS::encode_message(&self.pp.pp_sigma, &m_hid, &phi)?;
        let ((), omega) = VSIS::rerand(&self.pp.pp_sigma, hvk, &m, &cred.cred, rng)?;
        // 3. ctx_j := (pp, hvk, id, φ_j, id_{j→i}, cred*), π_j for R_att
        let ctx = self.attestation_context(hvk, id, &phi, &tag);
        let rows = self.rows(&s)?;
        let statement = self.attestation_statement(hvk, &phi, &tag, &rows)?;
        let ring = &self.constants.rings.c;
        let witness = relations::att_witness(
            [
                relations::int_poly(ring, omega.s0().iter().map(|&x| i128::from(x)))?,
                relations::int_poly(ring, omega.s1().iter().map(|&x| i128::from(x)))?,
            ],
            relations::ternary_poly(ring, omega.x1())?,
            relations::ternary_poly(ring, m.usk())?,
            [
                relations::ternary_poly(ring, &m.x0()[0])?,
                relations::ternary_poly(ring, &m.x0()[1])?,
            ],
            relations::e_subring(ring, e.entries())?,
        );
        let proof = relations::prove(
            &statement,
            &self.sets.att,
            self.pp.jali_pp_seed,
            &witness,
            &ctx,
            rng,
        )?;
        Ok(Attestation {
            tag,
            phi,
            proof: Proof::from_bytes(proof)?,
        })
    }

    /// `VerifyProofAtt(hvk, id, att_j) → {0, 1}` (con:149-153); [`LatticePCS::check_attestation`]
    /// is the same algorithm with the reason for a rejection. About 3 s and 0.5 GiB at one thread.
    fn verify_attestation(
        &self,
        hvk: &Self::HelperVerificationKey,
        id: &Self::Identity,
        att: &Self::Attestation,
    ) -> bool {
        self.check_attestation(hvk, id, att).is_ok()
    }

    /// `Prove(hvk, f_k, id, usk, w) → (π, st_iss) / ⊥` (con:155-165). `CheckAtts_P` verifies the
    /// $`k`$ attestations in full (about 3 s each) before $`\pi_0`$ is proven (about 2.8 s;
    /// 17.5 s in all at $`k = 5`$ at one thread, about 5.8 s with `parallel` on ten cores, the
    /// attestations verified in parallel: module docs).
    ///
    /// # Errors
    /// [`Error::ZeroThreshold`] for a root predicate; [`Error::WrongAttestationCount`] unless
    /// `w` has exactly `f.threshold` attestations; [`Error::InvalidKey`] for a wiped `hvk`;
    /// [`Error::IdentifierMismatch`] if $`id \ne \mathsf{Tag}(usk, c_0)`$; where `CheckAtts_P`
    /// returns 0: [`Error::InvalidAttestation`], [`Error::DuplicateAttester`],
    /// [`Error::SelfAttestation`] or [`Error::PolicyRejected`]; [`Error::LatticeBackend`] if
    /// Jali fails.
    fn prove<R: RngCore + CryptoRng + ?Sized>(
        &self,
        hvk: &Self::HelperVerificationKey,
        f: &Self::Predicate,
        id: &Self::Identity,
        usk: &Self::UserSecretKey,
        w: &Self::Witness,
        rng: &mut R,
    ) -> Result<(Self::IssuanceProof, Self::IssuanceState), Error> {
        if f.is_root() {
            return Err(Error::ZeroThreshold);
        }
        if u32::try_from(w.len()).ok() != Some(f.threshold) {
            return Err(Error::WrongAttestationCount {
                expected: usize::try_from(f.threshold).unwrap_or(usize::MAX),
                actual: w.len(),
            });
        }
        let parts = self.prove_issuance(hvk, f, id, usk, Some(w), rng)?;
        // 4. π := ((att_j)_j, C, id_{i→i}, π_0), st_iss = ((usk, x_0), φ, x_0)
        let proof = IssuanceProof {
            attestations: w.to_vec(),
            c: parts.c,
            t0: parts.t0,
            proof: parts.proof,
        };
        Ok((proof, parts.state))
    }

    /// `Issue(hvk, hsk, f_k, id, π) → ĉred / ⊥` (con:175-179). Proof-gated: `⊥` whenever
    /// `VerifyProof(hvk, f_k, id, π) = 0`; then `BlindIssue(sk, C, EncPred(f_k))` on the $`C`$ of
    /// the verified `π`, one `SampPre` call under the issuance cap. `f_k` is the HELPER's input.
    ///
    /// # Errors
    /// [`Error::InvalidKey`] if `hvk` is not the key inside `hsk`, or if `hsk` belongs to another
    /// deployment; [`Error::ZeroThreshold`] for a root predicate; [`Error::InvalidProof`] if
    /// `VerifyProof` rejects, whatever the reason ([`LatticePCS::check_proof`] names it);
    /// [`Error::IssuanceCapReached`] at the cap; the other errors of `BlindIssue`.
    fn issue<R: RngCore + CryptoRng + ?Sized>(
        &self,
        hvk: &Self::HelperVerificationKey,
        hsk: &Self::HelperSecretKey,
        f: &Self::Predicate,
        id: &Self::Identity,
        proof: &Self::IssuanceProof,
        rng: &mut R,
    ) -> Result<Self::PreCredential, Error> {
        // 1. Parse hsk as (sk, hvk) (implementation note: the two copies of hvk agree, and hsk was
        //    generated under THIS pp). Check VerifyProof(hvk, f_k, id, π) = 1.
        if hsk.hvk != *hvk || hsk.pp_digest != self.pp_digest {
            return Err(Error::InvalidKey);
        }
        if f.is_root() {
            return Err(Error::ZeroThreshold);
        }
        if !self.verify_proof(hvk, f, id, proof) {
            return Err(Error::InvalidProof);
        }
        // 2. ĉred ← BlindIssue(sk, C, EncPred(f_k))
        VSIS::blind_issue(&self.pp.pp_sigma, &hsk.sk, &proof.c, &self.enc_pred(f), rng)
    }

    /// `Unblind(hvk, usk, f_k, ĉred, st_iss) → cred / ⊥` (con:181-185): the state must belong to
    /// `(usk, f_k)`; `Σ-vSIS.Unblind` returns $`\widehat{cred}`$ only if `Verify` accepts it
    /// (bb:846-849), so this fails closed with ONE verification (module docs).
    ///
    /// # Errors
    /// [`Error::InvalidKey`] for a wiped `hvk`; [`Error::IssuanceStateMismatch`] if `st_iss`
    /// does not belong to `(usk, f_k)`; [`Error::InvalidPreCredential`] if `ĉred` does not
    /// verify; [`Error::InvalidMessage`] for a wiped state.
    fn unblind(
        &self,
        hvk: &Self::HelperVerificationKey,
        usk: &Self::UserSecretKey,
        f: &Self::Predicate,
        pre: &Self::PreCredential,
        state: &Self::IssuanceState,
    ) -> Result<Self::Credential, Error> {
        // 1. hvk ∈ V_pp; the first component of m_hid is usk and φ = EncPred(f_k)
        self.check_key(hvk)?;
        let phi = self.enc_pred(f);
        if !(state.usk.ct_eq(&usk.0) && state.phi == phi) {
            return Err(Error::IssuanceStateMismatch);
        }
        // 2. cred_Σ ← Σ.Unblind(hvk, Enc(m_hid, φ), ĉred, x_0); cred = (cred_Σ, x_0)
        let m_hid = VSISHiddenMessage::new(state.usk.clone(), state.x0.clone());
        let m = VSIS::encode_message(&self.pp.pp_sigma, &m_hid, &state.phi)?;
        let r = VSISIssuanceState::new(state.x0.clone());
        let cred = VSIS::unblind(&self.pp.pp_sigma, hvk, &m, pre, &r)?;
        Ok(Credential {
            cred,
            x0: state.x0.clone(),
        })
    }

    /// `VerifyCred(hvk, usk, f, cred) → {0, 1}` (con:187-189): `Σ-vSIS.Verify` on
    /// $`(usk, \mathsf{EncPred}(f), x_0)`$, about 0.14 ms. Never panics.
    fn verify_cred(
        &self,
        hvk: &Self::HelperVerificationKey,
        usk: &Self::UserSecretKey,
        f: &Self::Predicate,
        cred: &Self::Credential,
    ) -> bool {
        if self.check_key(hvk).is_err() {
            return false;
        }
        let phi = self.enc_pred(f);
        let m_hid = VSISHiddenMessage::new(usk.0.clone(), cred.x0.clone());
        let Ok(m) = VSIS::encode_message(&self.pp.pp_sigma, &m_hid, &phi) else {
            return false;
        };
        VSIS::verify(&self.pp.pp_sigma, hvk, &m, &cred.cred)
    }

    /// `VerifyProof(hvk, f_k, id, π) → {0, 1}` (con:168-173); [`LatticePCS::check_proof`] is the
    /// same algorithm with the reason for a rejection. At one thread about 0.6 s for $`\pi_0`$ and
    /// 3 s per attestation (15.4 s at $`k = 5`$); with `parallel`, the attestations verified in
    /// parallel, about 4 s at $`k = 5`$ on ten cores and up to $`\min(k, n)`$ verifications of
    /// about 0.5 GiB at once on a pool of $`n`$ threads (module docs).
    fn verify_proof(
        &self,
        hvk: &Self::HelperVerificationKey,
        f: &Self::Predicate,
        id: &Self::Identity,
        proof: &Self::IssuanceProof,
    ) -> bool {
        self.check_proof(hvk, f, id, proof).is_ok()
    }
}

#[cfg(test)]
mod tests {
    use rand::{SeedableRng, rngs::StdRng};

    use super::*;
    use crate::serialization::WireFormat;

    const LABEL: &[u8] = b"PCS-LATTICE-CONSTRUCTION-UNIT-TESTS";

    fn pcs() -> LatticePCS {
        LatticePCS::setup(SetupParams::new(LABEL.to_vec())).unwrap()
    }

    #[test]
    fn setup_is_transparent_and_received_parameters_are_checked() {
        let pcs = pcs();
        let pp = pcs.public_parameters().clone();
        assert_eq!(pcs.label(), LABEL);
        assert_eq!(pp, PublicParameters::derive(LABEL).unwrap());
        assert_eq!(pcs.parameters_digest(), &pp.digest());
        let again = LatticePCS::from_public_parameters(pp.clone(), AcceptAll).unwrap();
        assert_eq!(again.parameters_digest(), pcs.parameters_digest());
        // a pp whose parts do not come from its label is refused
        let other = PublicParameters::derive(b"another label").unwrap();
        let mut forged = pp.clone();
        forged.pp_sigma = other.pp_sigma.clone();
        assert!(matches!(
            LatticePCS::from_public_parameters(forged, AcceptAll),
            Err(Error::InvalidPublicParameters(_))
        ));
        let mut forged = pp.clone();
        forged.c0 = other.c0.clone();
        assert!(matches!(
            LatticePCS::from_public_parameters(forged, AcceptAll),
            Err(Error::InvalidPublicParameters(_))
        ));
        let mut forged = pp.clone();
        forged.jali_pp_seed[0] ^= 1;
        assert!(matches!(
            LatticePCS::from_public_parameters(forged, AcceptAll),
            Err(Error::InvalidPublicParameters(_))
        ));
        // a relabelled pp is the pp of the new label (all of it is derived)
        let mut relabelled = pp;
        relabelled.label = b"another label".to_vec();
        assert!(matches!(
            LatticePCS::from_public_parameters(relabelled, AcceptAll),
            Err(Error::InvalidPublicParameters(_))
        ));
        assert!(format!("{pcs:?}").starts_with("LatticePCS"));
    }

    /// `UKeyGen`, the identifier and the attester point; `EncPred` and the allow list.
    #[test]
    fn keys_identifiers_and_predicates() {
        let pcs = pcs();
        let mut rng = StdRng::seed_from_u64(0x7a77_0001);
        let (id, usk) = pcs.user_keygen(&mut rng).unwrap();
        assert_eq!(pcs.identity(&usk).unwrap(), id);
        assert_eq!(
            id,
            LWR.eval(usk.expose_ternary(), &pcs.public_parameters().c0)
                .unwrap()
        );
        assert_eq!(pcs.tag_point(&id), oracles::tag_point(LABEL, &id));
        let (id2, _) = pcs.user_keygen(&mut rng).unwrap();
        assert_ne!(id, id2);
        let mut wiped = UserSecretKey::from_ternary(usk.expose_ternary().clone());
        zeroize::Zeroize::zeroize(&mut wiped);
        assert_eq!(pcs.identity(&wiped), Err(Error::UndefinedTag));
        // EncPred and the allow list
        let f = Predicate::new(2, "members");
        let f_root = Predicate::root("founders");
        assert_eq!(pcs.enc_pred(&f), oracles::pred_enc(LABEL, &f));
        let list = pcs.allow_list([&f, &f_root]);
        assert!(list.accepts(&[pcs.enc_pred(&f), pcs.enc_pred(&f_root)]));
        assert!(!list.accepts(&[pcs.enc_pred(&Predicate::new(2, "others"))]));
        // the identifier round-trips through the wire format
        assert_eq!(LWRTag::from_bytes(&id.to_bytes()).unwrap(), id);
        assert_eq!(
            <LWRTag as WireFormat>::from_bytes(&WireFormat::to_bytes(&id).unwrap()).unwrap(),
            id
        );
    }
}
