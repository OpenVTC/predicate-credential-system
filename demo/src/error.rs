//! Errors of the prototype. Library errors keep their reason.

use predicate_credential_system::Error as PcsError;

#[derive(Debug, thiserror::Error, PartialEq, Eq)]
pub enum ProtoError {
    #[error("pcs: {0}")]
    Pcs(#[from] PcsError),
    #[error("member {0} holds no live vetter grant")]
    NotAVetter(String),
    #[error("token label {0} is not live")]
    LabelNotLive(String),
    #[error("vetter period {0} is not live")]
    PeriodNotLive(String),
    #[error("vetter period {0} is not the current one")]
    NotCurrentPeriod(String),
    #[error("vetter period {0} is already live")]
    PeriodExists(String),
    #[error("the request carries {count} attestations, more than the limit of {max}")]
    TooManyAttestations { count: usize, max: usize },
    #[error("vetter period {0} is the current one: rotate before dropping it")]
    DropsCurrentPeriod(String),
    #[error("member {member} already holds a credential under period {period}")]
    AlreadyIssued { member: String, period: String },
    #[error("no credential under vetter period {0}")]
    NoCredentialForPeriod(String),
    #[error("no statement was made in that session")]
    NoSuchStatement,
    #[error("member {member} was already served tokens for tick {tick}")]
    AlreadyServedThisTick { member: String, tick: u32 },
    #[error("token opening proof {0} does not verify")]
    BadOpeningProof(usize),
    #[error("vetter is at capacity, next free token from tick {available_from}")]
    AtCapacity { available_from: u32 },
    #[error("challenge unknown or already used")]
    BadChallenge,
    #[error("statement count {statements} differs from the request's {attestations}")]
    CountMismatch {
        statements: usize,
        attestations: usize,
    },
    #[error("the request carries two attestations with one tag")]
    DuplicateTag,
    #[error("the request does not verify: {0}")]
    ProofRejected(PcsError),
    #[error("received attestation does not verify: {0}")]
    AttestationRejected(String),
    #[error("event mode refused: {0}")]
    EventRefused(String),
    #[error("serialization: {0}")]
    Serialization(String),
}
