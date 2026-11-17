//! Sigma protocols: generalized Schnorr proofs with witness-preserving AND composition and
//! their Fiat-Shamir transform (paper §2.3, "Sigma protocols and Schnorr proofs"), following the
//! IETF CFRG drafts `draft-irtf-cfrg-sigma-protocols-04` and `draft-irtf-cfrg-fiat-shamir-04`.
//!
//! * [`relation`]: statements. A statement is a conjunction of linear equations over
//!   prime-order groups sharing one scalar field, built with [`GroupRelation`] (one group, the
//!   draft's `LinearRelation`) or [`PairingRelation`] (`G_1`, `G_2` and lazily evaluated `G_T`
//!   equations, the draft's `LinearRelation` over `G_1` when it has no `G_2` and `G_T` equation
//!   and this crate's extension otherwise). Both implement [`LinearRelation`], the only
//!   interface the protocol layers use.
//! * [`protocol`]: the interactive three-move protocol, its special-HVZK simulator and its
//!   special-soundness extractor (Defs. "Sigma protocol", "Schnorr sigma protocol").
//! * [`fiat_shamir`]: the non-interactive `zkPoK_ctx{…}` of §5.1: the compact NARG strings
//!   `(c, z)` of the Sigma draft, with the context `ctx` in the tag.
//! * [`codec`] and [`ciphersuite`]: the byte encodings and the ciphersuite identifiers.
//!
//! # In formulas
//!
//! A statement is a system of linear equations with bases $`B_{ij}`$, public coefficients
//! $`b_{ij}`$ and $`a_{ik}`$, image elements $`A_{ik}`$ and the witness $`(x_v)_v`$. A
//! coordinate $`x_v`$ that occurs in several equations is ONE variable:
//!
//! ```math
//! R = \Bigl\{\, \bigl(\text{instance},\ (x_v)_v\bigr) \;:\; \sum_k a_{ik} A_{ik} = \sum_j b_{ij}\, x_{v_{ij}}\, B_{ij} \ \text{ for all } i \,\Bigr\}
//! ```
//!
//! The three moves, with one mask $`r_v`$ and one response $`z_v`$ per variable and $`Y_i`$ the
//! value of the left-hand side of equation $`i`$:
//!
//! ```math
//! A_i = \sum_j b_{ij}\, r_{v_{ij}}\, B_{ij}, \qquad c \leftarrow \mathbb{Z}_p, \qquad z_v = r_v + c\, x_v, \qquad \text{accept iff } \sum_j b_{ij}\, z_{v_{ij}}\, B_{ij} = A_i + c\, Y_i \ \text{ for all } i
//! ```
//!
//! # Witness-preserving AND composition
//!
//! A witness coordinate is a [`ScalarVar`]. Every equation that mentions the same variable
//! shares its mask and its response. This is precisely the composition rule the paper states
//! for generalized Schnorr protocols ("the prover uses the same mask `r` and hence the same
//! response `z = r + cx` in each such equation"), and it makes the extractor return a *single*
//! value for a shared coordinate such as `usk`.
//!
//! # Example
//!
//! ```
//! use ark_bls12_381::{Fr, G1Projective as G1};
//! use ark_ec::PrimeGroup;
//! use predicate_credential_system::sigma::{fiat_shamir, GroupRelation, LinearEquation};
//! use rand::{rngs::StdRng, SeedableRng};
//!
//! let mut rng = StdRng::seed_from_u64(7);
//! let (g, h) = (G1::generator(), G1::generator() * Fr::from(5u64));
//! let usk = Fr::from(1234u64);
//!
//! // Two equations sharing ONE witness coordinate:  T1 = usk·g  and  T2 = usk·h.
//! let mut rel = GroupRelation::<G1>::new();
//! let x = rel.alloc_scalar();
//! rel.add_equation(LinearEquation::dlog(x, g, g * usk))?;
//! rel.add_equation(LinearEquation::dlog(x, h, h * usk))?;
//!
//! let proof = fiat_shamir::prove(&rel, &[usk], b"context", &mut rng)?;
//! assert!(fiat_shamir::verify(&rel, b"context", &proof));
//! assert!(!fiat_shamir::verify(&rel, b"another context", &proof));
//! // the NARG string of the draft's compact flavor: c ‖ z_1, two 32-byte big-endian scalars
//! assert_eq!(proof.to_narg().len(), 64);
//! # Ok::<(), predicate_credential_system::Error>(())
//! ```

pub mod ciphersuite;
pub mod codec;
pub mod fiat_shamir;
pub mod protocol;
pub mod relation;

pub use fiat_shamir::FSProof;
pub use protocol::{ProverState, Witness, commit, extract, respond, simulate, verify};
pub use relation::{
    GroupRelation, GtEquation, GtImageTerm, GtTerm, IndexedEquation, IndexedGtEquation,
    LinearEquation, LinearRelation, PairingImage, PairingProduct, PairingRelation, ScalarVar,
    pairing_product,
};
