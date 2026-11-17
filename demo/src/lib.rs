//! Throwaway prototype of hidden-vetter admission for OpenVTC, built on the Predicate
//! Credential System's protocol `pcreds` (the paper's `Π_PCreds`) with its application
//! contexts. Design: `design-docs/vetting-hidden-vetters-pcs.md`, with the corrections of its
//! §13 applied where `pcreds` allows them (README, "Changes for `pcreds`").
//!
//! What it shows end to end, in memory, with no transport:
//!
//! - The VTC (the PCS *helper*) issues vetter credentials as root admissions behind the grant
//!   check, under one helper key per period (`vetter` periods are keys, module `scheme`), and
//!   keeps the current and the previous period live.
//! - Tokens on a constant drip are `Σ-PS` blind signatures on secret serials, under one key per
//!   label, never a helper key, spent once per label (§5.1).
//! - The applicant collects attestations through `pcreds`'s attestation requests, each bound to
//!   its statement metadata, and sends the VTC a credential request bound to all of them and to
//!   the proof context. The VTC evaluates it (`N''`, the distinct tags of the valid
//!   attestations) and turns it into VTI's own `StatementFacts`, counted by VTI's own
//!   `vta_sdk::vetting::requirements::evaluate`, unchanged. It never answers it with a
//!   credential.
//! - Withdrawal by tag, from a sender that need not be named (§4.4).
//!
//! The engines stand in for the VTA (`vetter`, `applicant`: the PCS engine of §13 C7) and the
//! VTC (`vtc`). Nothing here is production code.

pub mod applicant;
pub mod error;
pub mod meta;
pub mod scheme;
pub mod token;
pub mod vetter;
pub mod vtc;

pub use error::ProtoError;
