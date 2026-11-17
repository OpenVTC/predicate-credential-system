//! Soundness and zero-knowledge harness of the protocol `Π_PCreds`
//! (`predicate_credential_system::pcreds`), for every pairing-based base/tag pair.
//!
//! The harness drives the interactive sigma protocol of `predicate_credential_system::sigma`
//! (`commit`, `respond`, `verify`, `simulate`, `extract`) on EXACTLY the relations of the four
//! proofs, `PairingBackend::{identifier_relation, attestation_relation, issuance_relation,
//! possession_relation}`, at the statements a verifier rebuilds from public data (`x_0`,
//! `x_Q = recipient_point(hvk, id_Q)`, the received tag, show and request), and under the contexts
//! the protocol computes (`identifier_context`, `attestation_context`, `issuance_context`,
//! `prove_context`). In the extraction tests, the first of the two transcripts is a proof that
//! the protocol's own verifier accepted inside a protocol message.
//!
//! # What is tested: plain Fiat–Shamir, extraction by rewinding
//!
//! The theorem "Security of `Π_PCreds`" (pcreds-protocol.tex, lines 458–478 with Remark
//! "Corrupted helper") assumes in hypothesis (iv) that `π_id`, `π_att`, `π_iss` and `π_prove`
//! are proofs of ONE online simulation-extractable NIZK (Def. "Online simulation-extractable
//! NIZK", prelims.tex line 146), in the weak sense when the helper is corrupted. The pairing
//! instantiation compiles generalized Schnorr protocols with PLAIN Fiat–Shamir, and "Fiat–Shamir
//! with its rewinding extractor does not give" that definition (prelims.tex, "Instantiating the
//! definition", line 181). This file tests what plain Fiat–Shamir and the sigma protocols under
//! it do provide; it does NOT establish hypothesis (iv):
//!
//! * **Knowledge extraction is by rewinding, not online.** `fork` runs a prover twice on one
//!   random tape; the runs differ only in the answer of `H_1` at the prover's one query
//!   `(ctx, statement, A)`, the fork of the forking lemma. Run 1 is the Fiat–Shamir proof, run 2
//!   answers a reprogrammed challenge, and special soundness turns the two transcripts into a
//!   witness. There is no straight-line extractor here (neither Fischlin's transform nor the
//!   algebraic-group-model extractor of the paper's second route), nothing measures the
//!   extraction error `ε_ext`, and an adversary that sees simulated proofs is not modelled.
//! * **Zero knowledge is checked as special HVZK.** For a challenge fixed first, the simulator's
//!   transcript verifies and has the shape of an honest one. The NIZK simulator of the
//!   programmable random-oracle model also sets `H_1(ctx, statement, A) := c`; a hash function
//!   cannot be programmed, so simulated transcripts are REJECTED as proofs, which the tests
//!   assert. That the distributions agree (perfectly, for Schnorr protocols: Def. "Schnorr
//!   protocols", prelims.tex line 116) is the paper's argument, not a measurement.
//! * **Statements and contexts.** The challenge hashes `ctx`, every base and target of the
//!   statement, and `A` (strong Fiat–Shamir, "Fiat–Shamir", prelims.tex line 129), and the
//!   verifier rebuilds every statement and context itself ("Contexts", prelims.tex line 178).
//!   Tested by mounting the weak Fiat–Shamir attack, by moving valid proofs to other statements,
//!   and by proofs made under contexts the verifier does not compute.
//! * **Computational assumptions are out of reach**: DDH and `q`-DDHI for the tags (weak
//!   pseudorandomness), one-more issuance, the zero-knowledge game. Where a test documents a
//!   structural fact (attack A7), it states exactly what it computes and cites the distributional
//!   argument that covers every other test.
//!
//! # Map from the tests to the paper
//!
//! Generic tests run for `Σ-PS` and `Σ-BBS` with `Tag_DDH` and `Tag_DY` (`every_pair!`); the
//! others are specific to one base.
//!
//! | test | property | paper |
//! |---|---|---|
//! | `extractor_on_identifier_proof`, `extractor_on_attestation`, `extractor_on_issuance`, `extractor_on_membership_proof` | special soundness on `R_Tag`, `R_att`, `R_iss`, `R_Possess` from a forked Fiat–Shamir run; the extracted vector is the prover's witness; ONE `usk`, the user's (`User::expose_key`), satisfies every clause, and the tag clause and one clause of the base are on that variable; equal challenges, two independent runs and a rejected transcript extract nothing | Def. "Sigma protocol", "AND composition with a shared witness" (prelims.tex 86–115); "Relations" (pcreds-protocol.tex 255–265); Theorem, hyp. (iv) |
//! | the same, for `R_att` and `R_Possess` | the extracted witness yields a credential that verifies on the extracted `usk` and show randomness that reproduces the show (for `Σ-BBS`, the source's own credential); the user built from the extracted key has the source's identifier and the source's credential verifies for it | Lemma `lem:base-ps`, proof friendliness, "Possession" (base-instantiations.tex 113, 146); Lemma `lem:base-bbs` (v), case (a) (275–289); "Simulation overview": "the identifier `Tag(K, x_0)` determines which ideal user to register or reuse" (pcreds-protocol.tex 479–483) |
//! | `extractor_on_issuance` | the extracted `(usk, τ)` is the requester's (`IssuanceState::expose_tape`), opens `Ĉ`, and completes the helper's actual reply into a credential on the extracted `usk` | Def. "Credential base", Correctness "for every choice of the issuance randomness" (building-blocks.tex 81); Theorem, hyp. (iv): "extracted issuance messages lie in the admissible domain of `Verify`" |
//! | `bbs_extraction_covers_a_prover_that_knows_the_issuing_key` | a holder of `x` shows a credential it never received (`r_1 = 0`, `e = −x`); the verifier accepts, and extraction falls in case (b) and still yields a credential | Lemma `lem:base-bbs` (v), case (b) (base-instantiations.tex 290) and the third possession clause (234); Remark "Helper-key convention" (pcreds-protocol.tex 130) |
//! | `shared_witness` | a tag (identifier) of another key than the credential (request) has no witness and the provers refuse; with the key NOT shared, the same clauses let one credential vouch for any key's tag | "Relations" (sharing `usk` across clauses); "AND composition with a shared witness" |
//! | `simulator` | special HVZK on the four relations, a false statement included; simulated transcripts are no Fiat–Shamir proofs | Def. "Sigma protocol" (HVZK); Def. "Schnorr protocols"; Def. `def:nizk`, zero knowledge |
//! | `weak_fiat_shamir_on_attestation`, `weak_fiat_shamir_on_issuance` | the weak Fiat–Shamir attack (a tag or an identifier solved for after the challenge) is mounted: it breaks a transform that does not hash the statement, and fails against the crate's | "Fiat–Shamir": `c = H_1(x, a)` hashes the statement |
//! | `contexts_are_rebuilt_by_the_verifier` | a proof under any context the verifier does not compute itself is rejected | "Contexts": a proof under one context is a proof of another statement |
//! | `binding_of_statements` | a valid proof does not verify for another tag, recipient point, show, request `Ĉ`, identifier, attestation list, message, session or helper key; for `Σ-BBS`, whose clauses do not mention `hvk`, the binding to `hvk` is the context's (and, for shows, the public pairing check's) | protocol box (pcreds-protocol.tex 346–443): statements `(hvk, σ*, t, x_Q)`, `(hvk, Ĉ, id_Q)`, `(hvk, σ*)` and contexts `(ssid, P̃)`, `(ssid, att⃗)`, `m` |
//! | `ps_possession_proof_is_malleable_under_the_issuing_key`, `bbs_possession_proof_is_malleable_under_the_issuing_key` | a holder of the issuing key turns an accepting proof into another one of the same statement and context: `Σ-PS` `π_prove` (not `π_att`, `π_iss`: the tag clause pins `usk`); `Σ-BBS` `π_prove` and `π_att`, through the third clause | Remark "Malleability under the issuing key" (base-instantiations.tex 163); Remark "Corrupted helper" (pcreds-protocol.tex 475); `def:nizk`, the weak variant |
//! | `recipient_scoped_linkability` | a source's tag is fixed for one recipient and differs across recipients and sources; shows share no group element | `F_PCreds`, "Attestation tags" (pcreds-protocol.tex 32–33); "Identifiers and attestation tags" (247) |
//! | `proof_gated_issuance` | every single-field change of a credential request is refused before anything is issued; under a requester's fresh `π_iss`, a changed attestation does not count | protocol box, `CredentialRequest`, the helper's steps (i) and (ii) |
//! | `a7_bbs_records_do_not_single_out_the_source`, `a7_bbs_every_issued_credential_explains_every_show`, `a7_ps_records_do_not_single_out_the_source` | attack A7: the helper's tests with its issuance records give the same answer for every candidate source of a show (attestation or membership proof); every issued credential explains every `Σ-BBS` show; shows with fixed randomizers, which the verifier also accepts, are identified for their source only | `F_PCreds`, "Attestation tags": "the helper sees which attestations share a source but not who the sources are"; `lem:base-bbs` Fact 2 (base-instantiations.tex 259) and (iii); `lem:base-ps`, show simulatability (136); review note R3 (232) |
//!
//! # Ported from the harness of the earlier construction (`tests/pcs_soundness.rs`)
//!
//! * `extractor_on_att_*` → `extractor_on_attestation`; `bbs_extractor_rebuilds_the_signature_*`
//!   → `Algebra::check_extracted`, now for both bases; `extractor_on_issue_*` →
//!   `extractor_on_issuance`; `shared_witness_*` → `shared_witness`, extended to `R_iss` and to
//!   the unshared relation; `simulator_*` → `simulator`, extended to `π_id` and `π_prove`;
//!   `structural_anonymity_*` → `recipient_scoped_linkability`;
//!   `bbs_helper_cannot_deanonymize_at_pcs_level` → the `a7_*` tests, extended to the recorded
//!   `A` and `C` and to `Σ-PS`; `proof_gated_exhaustive_*` → `proof_gated_issuance`.
//! * Dropped: every `Σ-EQ` instance (the base is not in the paper); the self-exclusion tag `T_0`
//!   and its clauses (the helper keeps the set `I` of issued identifiers instead); the predicate
//!   label `φ` and its mutations (a credential certifies `usk` alone); the separate root request
//!   (a root user is admitted with `d = root` on an ordinary request, so its `π_iss` is the one of
//!   `extractor_on_issuance`).

mod common;

use ark_bls12_381::Fr;
use ark_ec::PrimeGroup;
use ark_ff::{Field, One, UniformRand, Zero};
use ark_serialize::CanonicalSerialize;
use common::{BBS, BaseTest, Bk, DDH, DY, Deployment, E, G1, G2, Member, PS};
use predicate_credential_system::{
    Error,
    hash::duplex_sponge::{DuplexSponge, derive_session_id, squeeze_scalar},
    kiprf::{KIPRF, ProtocolTag},
    pcreds::{
        Attestation, AttestationRequest, AttestationStatement, Backend, Credential,
        CredentialRequest, Decision, Helper, HelperKey, IssuanceRecord, IssuanceStatement,
        MembershipProof, Policy, ProofKind, Protocol, Reply, User,
        pairing::{
            BBSCredential, BBSParams, BBSShow, BBSVerificationKey, Base, G1Request, PSPair,
            PSVerificationKey, PairingParams, pairing_product_is_identity,
        },
    },
    sigma::{
        FSProof, IndexedEquation, IndexedGtEquation, LinearRelation, PairingImage, PairingRelation,
        Witness, commit, extract, fiat_shamir, respond, simulate, verify,
    },
};
use rand::{SeedableRng, rngs::StdRng};

// Masks that derive the auxiliary randomness of a test from its seed (`seed ^ MASK`), so that
// every run is reproducible from the one seed recorded at the call site.
const REPROGRAMMED_ORACLE: u64 = 0xF1F1_0001;
const INDEPENDENT_TAPE: u64 = 0xF1F1_0002;
const CHEATING_TAPE: u64 = 0xF1F1_0003;
const ADVERSARY: u64 = 0xF1F1_0004;
const SIMULATOR: u64 = 0xF1F1_0005;
const CONTEXTS: u64 = 0xF1F1_0006;

/// `x ← Z_p^*`.
fn nonzero(rng: &mut StdRng) -> Fr {
    loop {
        let x = Fr::rand(rng);
        if !x.is_zero() {
            return x;
        }
    }
}

// ---------------------------------------------------------------------------------------------
// What the harness knows about the bases and the tags
// ---------------------------------------------------------------------------------------------

/// The facts about a base that the generic tests need beyond `BaseTest`.
trait Algebra: BaseTest {
    /// Whether the clauses of `Π_PrepareIssue` and `Π_Possess` mention `vk`. `Σ-PS`: yes (`Y` in
    /// `C = g_1^ρ Y^usk`, `X̃` and `Ỹ` in the possession clause); `Σ-BBS`: no
    /// (`C h_0^{-1} = h_u^usk h_r^ρ` and the three possession clauses are over `h_0, h_u, h_r` and
    /// the show), so its relations are the same statement under every key.
    const CLAUSES_MENTION_VK: bool;
    /// Whether the public check of `Π_Possess` mentions `vk`. `Σ-BBS`: `e(Ā, X̃) = e(B̄, g̃)`;
    /// `Σ-PS`: no (`σ'_1 ≠ 1`).
    const SHOW_CHECK_MENTIONS_VK: bool;

    /// The extraction step of the base's lemma, "proof friendliness": from an extracted witness of
    /// `R_Possess` (in the variable order of the relation) build a credential and show randomness,
    /// and assert that the credential verifies on the extracted `usk` and that `ReRand` with that
    /// randomness reproduces `show`. `holder` is the credential the show was made from.
    fn check_extracted(
        pp: &Self::Params,
        vk: &Self::VerificationKey,
        show: &Self::Show,
        extracted: &[Fr],
        holder: &Self::Credential,
    );
}

impl Algebra for PS {
    const CLAUSES_MENTION_VK: bool = true;
    const SHOW_CHECK_MENTIONS_VK: bool = false;

    /// Lemma `lem:base-ps`, "Possession", special soundness: `cred = (σ'_1, σ'_2 σ'_1^{-t})` and
    /// `ω = (1, t)`. The credential is the holder's re-randomized one, `(σ_1^r, σ_2^r)`, not the
    /// holder's itself.
    fn check_extracted(
        (): &(),
        vk: &PSVerificationKey<E>,
        show: &PSPair<E>,
        extracted: &[Fr],
        _holder: &PSPair<E>,
    ) {
        let &[usk, t] = extracted else {
            panic!("the witness of R_Possess of Σ-PS is (usk, t)");
        };
        let cred = PSPair {
            s1: show.s1,
            s2: show.s2 - show.s1 * t,
        };
        assert!(
            <PS as Base<E>>::verify(&(), vk, &usk, &cred),
            "the extracted credential verifies on the extracted usk"
        );
        assert_eq!(
            ps_rerand(&cred, Fr::one(), t),
            *show,
            "ReRand(cred; (1, t))"
        );
    }
}

impl Algebra for BBS {
    const CLAUSES_MENTION_VK: bool = false;
    const SHOW_CHECK_MENTIONS_VK: bool = true;

    /// Lemma `lem:base-bbs` (v), case (a) (`r_1 ≠ 0`, as for every honest show):
    /// `A = Ā^{r_3/r_1}`, `cred = (A, e, ρ)`, `ω = (r_1, 1/r_3)`. The credential is the holder's
    /// own.
    fn check_extracted(
        pp: &BBSParams<E>,
        vk: &BBSVerificationKey<E>,
        show: &BBSShow<E>,
        extracted: &[Fr],
        holder: &BBSCredential<E>,
    ) {
        let &[usk, rho, r1, e, r3, _, _] = extracted else {
            panic!("the witness of R_Possess of Σ-BBS is (usk, ρ, r_1, e, r_3, u, v)");
        };
        let a = show.a_bar * (r3 * r1.inverse().expect("case (a): r_1 ≠ 0"));
        let cred = BBSCredential { a, e, rho };
        assert!(
            <BBS as Base<E>>::verify(pp, vk, &usk, &cred),
            "the extracted credential verifies on the extracted usk"
        );
        assert_eq!(cred, *holder, "case (a) recovers the holder's credential");
        let r2 = r3.inverse().expect("r_3 = 1/r_2 ≠ 0");
        assert_eq!(
            bbs_rerand(pp, &usk, &cred, r1, r2),
            *show,
            "ReRand(cred; ω)"
        );
    }
}

/// `Σ-PS` `ReRand(vk, usk, (σ_1, σ_2); (r, t)) = (σ_1^r, (σ_2 σ_1^t)^r)` with explicit randomness
/// (base-instantiations.tex, box `Σ-PS`).
fn ps_rerand(cred: &PSPair<E>, r: Fr, t: Fr) -> PSPair<E> {
    PSPair {
        s1: cred.s1 * r,
        s2: (cred.s2 + cred.s1 * t) * r,
    }
}

/// `Σ-BBS` `ReRand(vk, usk, (A, e, ρ); (r_1, r_2))` with explicit randomness (box `Σ-BBS`):
/// `D = B(usk, ρ)^{r_2}`, `Ā = A^{r_1 r_2}`, `B̄ = D^{r_1} Ā^{-e}`.
fn bbs_rerand(pp: &BBSParams<E>, usk: &Fr, cred: &BBSCredential<E>, r1: Fr, r2: Fr) -> BBSShow<E> {
    let d = pp.b(usk, &cred.rho) * r2;
    let a_bar = cred.a * (r1 * r2);
    BBSShow {
        a_bar,
        b_bar: d * r1 - a_bar * cred.e,
        d,
    }
}

/// The witness `(usk, ρ, r_1, e, r_3 = 1/r_2, u = 1/r_1, v = e/r_1)` of `R_Possess` of `Σ-BBS`
/// for the show `bbs_rerand(.., r_1, r_2)`.
fn bbs_show_witness(usk: Fr, cred: &BBSCredential<E>, r1: Fr, r2: Fr) -> Vec<Fr> {
    let u = r1.inverse().expect("r_1 ≠ 0");
    vec![
        usk,
        cred.rho,
        r1,
        cred.e,
        r2.inverse().expect("r_2 ≠ 0"),
        u,
        cred.e * u,
    ]
}

/// The witness of `R_att` and `R_Possess` for a show made by `Base::rerand`: `usk`, then the
/// variables of the base's possession clauses.
fn possession_witness<B: Base<E>>(
    usk: Fr,
    cred: &B::Credential,
    omega: &B::ShowWitness,
) -> Vec<Fr> {
    let mut witness = Witness::with_capacity(1 + B::POSSESSION_VARIABLES);
    witness.push(usk);
    B::possession_witness(cred, omega, &mut witness);
    witness.to_vec()
}

/// The cheating prover of the weak Fiat–Shamir attack needs to solve the tag clause for its tag.
trait Forge: ProtocolTag<G1> + 'static {
    /// The tag `t` for which the tag clause at the point `x` recomputes to `commitment` under the
    /// challenge `c` and the response `z` of `usk`.
    fn solve(&self, point: &Fr, commitment: &G1, challenge: &Fr, response: &Fr) -> G1;
}

impl Forge for DDH {
    /// Clause `t = htag(x)^usk`: `z·htag(x) − c·t = A`, so `t = (z·htag(x) − A)/c`.
    fn solve(&self, point: &Fr, commitment: &G1, challenge: &Fr, response: &Fr) -> G1 {
        (self.htag(point) * response - *commitment) * challenge.inverse().expect("c ≠ 0")
    }
}

impl Forge for DY {
    /// Clause `t^usk = g_1 t^{-x}`: `z·t − c·(g_1 − x·t) = A`, so `t = (A + c·g_1)/(z + c·x)`.
    fn solve(&self, point: &Fr, commitment: &G1, challenge: &Fr, response: &Fr) -> G1 {
        let scale = (*response + *challenge * point)
            .inverse()
            .expect("z + c·x ≠ 0");
        (*commitment + *self.generator() * challenge) * scale
    }
}

// ---------------------------------------------------------------------------------------------
// The forked Fiat–Shamir prover and the extractor
// ---------------------------------------------------------------------------------------------

/// Two runs of the Fiat–Shamir prover on ONE random tape, rewound to its random-oracle query, and
/// one run on another tape.
///
/// Run 1 is answered by `H_1` itself: `proof` is the Fiat–Shamir proof (`fiat_shamir::prove` on
/// that tape outputs exactly it). Run 2 reuses the tape, hence the commitment, and gets a
/// reprogrammed challenge. The independent run has its own commitment; it is the failure boundary
/// of special soundness.
struct Fork {
    commitment: PairingImage<E>,
    proof: FSProof<Fr>,
    reprogrammed: (Fr, Vec<Fr>),
    independent: (PairingImage<E>, Fr, Vec<Fr>),
}

/// Runs the prover of `relation` on `witness` under `ctx` as described at `Fork`; the tapes and
/// the reprogrammed oracle are derived from `seed`.
fn fork(relation: &PairingRelation<E>, witness: &[Fr], ctx: &[u8], seed: u64) -> Fork {
    let tape = || StdRng::seed_from_u64(seed);
    // run 1: the oracle H_1 answers the query (ctx, statement, A)
    let (commitment, state) = commit(relation, &mut tape()).expect("commit");
    let challenge = fiat_shamir::challenge(relation, ctx, &commitment).expect("H_1");
    let responses = respond(state, witness, &challenge).expect("respond");
    let proof = FSProof {
        challenge,
        responses,
    };
    assert_eq!(
        fiat_shamir::prove(relation, witness, ctx, &mut tape()).ok(),
        Some(proof.clone()),
        "run 1 is the Fiat–Shamir prover on this tape"
    );
    assert!(fiat_shamir::verify(relation, ctx, &proof));
    // run 2: rewound to the query, which a reprogrammed oracle answers differently
    let (again, state) = commit(relation, &mut tape()).expect("commit");
    assert_eq!(again, commitment, "one tape, one commitment");
    let mut oracle = StdRng::seed_from_u64(seed ^ REPROGRAMMED_ORACLE);
    let second = loop {
        let c = Fr::rand(&mut oracle);
        if c != challenge {
            break c;
        }
    };
    let second_responses = respond(state, witness, &second).expect("respond");
    // a run on another tape
    let (other, state) = commit(
        relation,
        &mut StdRng::seed_from_u64(seed ^ INDEPENDENT_TAPE),
    )
    .expect("commit");
    let third = Fr::rand(&mut oracle);
    let third_responses = respond(state, witness, &third).expect("respond");
    Fork {
        commitment,
        proof,
        reprogrammed: (second, second_responses),
        independent: (other, third, third_responses),
    }
}

impl Fork {
    /// The special-soundness extractor on the two transcripts of the rewound prover, after
    /// checking its failure boundary: equal challenges, the transcripts of two independent runs
    /// (no common commitment) and a rejected transcript extract nothing.
    fn extract(&self, relation: &PairingRelation<E>) -> Vec<Fr> {
        let a = &self.commitment;
        let (c1, z1) = (&self.proof.challenge, self.proof.responses.as_slice());
        let (c2, z2) = (&self.reprogrammed.0, self.reprogrammed.1.as_slice());
        let (a3, c3, z3) = (
            &self.independent.0,
            &self.independent.1,
            self.independent.2.as_slice(),
        );
        // the first transcript is the one a verifier reconstructs from the compact proof
        assert_eq!(relation.recompute_commitment(c1, z1).ok().as_ref(), Some(a));
        assert!(verify(relation, a, c1, z1));
        assert!(verify(relation, a, c2, z2));
        assert!(verify(relation, a3, c3, z3));
        assert_eq!(
            extract(relation, a, (c1, z1), (c1, z1)),
            None,
            "equal challenges"
        );
        assert_eq!(
            extract(relation, a, (c1, z1), (c3, z3)),
            None,
            "transcripts of two runs"
        );
        assert_eq!(extract(relation, a3, (c1, z1), (c3, z3)), None);
        let mut tampered = z2.to_vec();
        tampered[0] += Fr::one();
        assert_eq!(
            extract(relation, a, (c1, z1), (c2, &tampered)),
            None,
            "a rejected transcript"
        );
        extract(relation, a, (c1, z1), (c2, z2)).expect("special soundness")
    }
}

/// Whether a `G_1` equation is on the variable 0, `usk`.
fn on_usk<F>(equation: &IndexedEquation<F>) -> bool {
    equation.terms.iter().any(|(var, _, _)| var.index() == 0)
}

/// How a composed relation uses the variable 0, `usk`: whether the tag clause (the last `G_1`
/// equation, which every relation builder adds last) is on it, and how many clauses of the base
/// are. The relations of the protocol give `(true, 1)`: `Σ-PS`, the `G_T` clause of possession or
/// the request clause; `Σ-BBS`, `h_0 = D^{r_3} h_u^{-usk} h_r^{-ρ}` or the request clause.
fn usk_sharing(relation: &PairingRelation<E>) -> (bool, usize) {
    let (tag_clause, base) = relation.g1_equations().split_last().expect("a tag clause");
    let gt_on_usk = |equation: &IndexedGtEquation<Fr>| {
        equation.terms.iter().any(|(var, _, _, _)| var.index() == 0)
    };
    let base_on_usk = base.iter().filter(|equation| on_usk(equation)).count()
        + relation
            .gt_equations()
            .iter()
            .filter(|equation| gt_on_usk(equation))
            .count();
    (on_usk(tag_clause), base_on_usk)
}

// ---------------------------------------------------------------------------------------------
// Statements as a verifier rebuilds them
// ---------------------------------------------------------------------------------------------

/// A statement `(hvk, σ*, t, x_Q)` of `R_att` as the recipient and the helper rebuild it, with
/// the source's witness. The show is a fresh `ReRand` of the source's credential, made here so
/// that its randomness is known.
struct AttestationParts<B: Base<E>> {
    x_q: Fr,
    tag: G1,
    show: B::Show,
    relation: PairingRelation<E>,
    witness: Vec<Fr>,
}

/// The parts of an attestation from `source` for the identifier `recipient`.
fn attestation_parts<B: Algebra, T: Forge>(
    pcreds: &Protocol<Bk<B, T>>,
    hvk: &HelperKey<Bk<B, T>>,
    source: &Member<B, T>,
    recipient: &G1,
    rng: &mut StdRng,
) -> AttestationParts<B> {
    let (params, vk) = (pcreds.params(), hvk.vk());
    let usk = *source.user.expose_key();
    let x_q = pcreds.recipient_point(vk, recipient).expect("H_req");
    let tag = params.tag.eval(&usk, &x_q).expect("Tag(usk_P, x_Q) ≠ ⊥");
    let (show, omega) = B::rerand(&params.base, vk, &usk, source.cred.as_inner(), rng);
    let relation = Bk::<B, T>::attestation_relation(params, vk, &show, &tag, &x_q).expect("R_att");
    let witness = possession_witness::<B>(usk, source.cred.as_inner(), &omega);
    AttestationParts {
        x_q,
        tag,
        show,
        relation,
        witness,
    }
}

/// A statement `(hvk, σ*)` of `R_Possess` with the holder's witness, for a fresh show.
fn membership_parts<B: Algebra, T: Forge>(
    pcreds: &Protocol<Bk<B, T>>,
    hvk: &HelperKey<Bk<B, T>>,
    holder: &Member<B, T>,
    rng: &mut StdRng,
) -> (B::Show, PairingRelation<E>, Vec<Fr>) {
    let (params, vk) = (pcreds.params(), hvk.vk());
    let usk = *holder.user.expose_key();
    let (show, omega) = B::rerand(&params.base, vk, &usk, holder.cred.as_inner(), rng);
    let relation = Bk::<B, T>::possession_relation(params, vk, &show).expect("R_Possess");
    let witness = possession_witness::<B>(usk, holder.cred.as_inner(), &omega);
    (show, relation, witness)
}

/// An attestation that carries `show` with a Fiat–Shamir proof on `witness`, for the identifier
/// `recipient`, checked by the protocol's verifier.
fn accepted_attestation<B: Algebra, T: Forge>(
    pcreds: &Protocol<Bk<B, T>>,
    hvk: &HelperKey<Bk<B, T>>,
    usk: &Fr,
    show: &B::Show,
    witness: &[Fr],
    recipient: &G1,
    rng: &mut StdRng,
) {
    let (params, vk) = (pcreds.params(), hvk.vk());
    let x_q = pcreds.recipient_point(vk, recipient).expect("H_req");
    let tag = params.tag.eval(usk, &x_q).expect("Tag(usk, x_Q) ≠ ⊥");
    let relation = Bk::<B, T>::attestation_relation(params, vk, show, &tag, &x_q).expect("R_att");
    let ctx = pcreds.attestation_context(vk).expect("ctx");
    let proof = fiat_shamir::prove(&relation, witness, &ctx, rng).expect("a witness of R_att");
    let attestation = Attestation {
        tag,
        show: show.clone(),
        proof,
    };
    assert_eq!(
        pcreds.check_attestation(hvk, recipient, &attestation),
        Ok(())
    );
}

/// A membership proof on `message` that carries `show` with a Fiat–Shamir proof on `witness`,
/// checked by the protocol's verifier.
fn accepted_membership_proof<B: Algebra, T: Forge>(
    pcreds: &Protocol<Bk<B, T>>,
    hvk: &HelperKey<Bk<B, T>>,
    show: &B::Show,
    witness: &[Fr],
    message: &[u8],
    rng: &mut StdRng,
) {
    let (params, vk) = (pcreds.params(), hvk.vk());
    let relation = Bk::<B, T>::possession_relation(params, vk, show).expect("R_Possess");
    let ctx = pcreds.prove_context(vk, message).expect("ctx");
    let proof = fiat_shamir::prove(&relation, witness, &ctx, rng).expect("a witness of R_Possess");
    let membership = MembershipProof {
        show: show.clone(),
        proof,
    };
    assert_eq!(pcreds.check_membership(hvk, message, &membership), Ok(()));
}

/// One `#[test]` per base/tag pair for the generic check `$check::<B, T>(label, seed)`: the label
/// is `pcreds-snd/<check>/<pair>`, the seed is `$seed + 1`, `+ 2`, `+ 3`, `+ 4` for `Σ-PS` with
/// `Tag_DDH`, `Σ-PS` with `Tag_DY`, `Σ-BBS` with `Tag_DDH`, `Σ-BBS` with `Tag_DY`.
macro_rules! every_pair {
    ($check:ident, $seed:literal) => {
        mod $check {
            use super::{BBS, DDH, DY, PS};

            #[test]
            fn ps_ddh() {
                super::$check::<PS, DDH>(
                    concat!("pcreds-snd/", stringify!($check), "/ps+ddh").as_bytes(),
                    $seed + 1,
                );
            }

            #[test]
            fn ps_dy() {
                super::$check::<PS, DY>(
                    concat!("pcreds-snd/", stringify!($check), "/ps+dy").as_bytes(),
                    $seed + 2,
                );
            }

            #[test]
            fn bbs_ddh() {
                super::$check::<BBS, DDH>(
                    concat!("pcreds-snd/", stringify!($check), "/bbs+ddh").as_bytes(),
                    $seed + 3,
                );
            }

            #[test]
            fn bbs_dy() {
                super::$check::<BBS, DY>(
                    concat!("pcreds-snd/", stringify!($check), "/bbs+dy").as_bytes(),
                    $seed + 4,
                );
            }
        }
    };
}

// ---------------------------------------------------------------------------------------------
// (a) Special soundness: extraction from a forked Fiat–Shamir run
// ---------------------------------------------------------------------------------------------

/// `π_id`, `R_Tag` at `(id_Q, x_0)` under `(ssid, P̃)`: the protocol's own proof verifies for the
/// rebuilt statement and context; the forked proof is accepted in an attestation request; the
/// extracted key is the requester's and evaluates to `id_Q`.
fn extractor_on_identifier_proof<B: Algebra, T: Forge>(label: &[u8], seed: u64) {
    let mut dep = Deployment::<B, T>::new(label, 1, seed);
    let requester = dep.register();
    let ssid = dep.ssid();
    let contact = b"member-0@example";
    let (pcreds, hvk) = (&dep.pcreds, &dep.hvk);
    let params = pcreds.params();
    let x0 = *hvk.identifier_point();
    let request = pcreds
        .request_attestation(hvk, &requester, &ssid, contact, &mut dep.rng)
        .expect("π_id");
    let relation = Bk::<B, T>::identifier_relation(params, &request.id, &x0).expect("R_Tag");
    let ctx = pcreds.identifier_context(&ssid, contact);
    assert!(
        fiat_shamir::verify(&relation, &ctx, &request.proof),
        "the protocol's π_id is a proof of the rebuilt statement under the rebuilt context"
    );

    let witness = [*requester.expose_key()];
    let run = fork(&relation, &witness, &ctx, seed);
    let forked = AttestationRequest {
        id: request.id,
        proof: run.proof.clone(),
    };
    assert!(pcreds.verify_attestation_request(hvk, &forked, &ssid, contact));
    let extracted = run.extract(&relation);
    assert_eq!(extracted, witness, "the requester's key");
    assert_eq!(params.tag.eval(&extracted[0], &x0), Some(*requester.id()));
}

/// `π_att`, `R_att` at `(hvk, σ*, t, x_Q)`: from an attestation the recipient accepts, the
/// extractor recovers the source's witness; its ONE `usk` satisfies the tag clause and the
/// possession clauses separately; it yields a credential (`Algebra::check_extracted`); its
/// identifier `Tag(usk, x_0)` is the source's (which is how the simulator of the security proof
/// names the ideal source, pcreds-protocol.tex line 482), and the source's credential verifies
/// under the user built from the extracted key; any other value in its place satisfies neither
/// part.
fn extractor_on_attestation<B: Algebra, T: Forge>(label: &[u8], seed: u64) {
    let mut dep = Deployment::<B, T>::new(label, 1, seed);
    let recipient = dep.register();
    let (pcreds, hvk, source) = (&dep.pcreds, &dep.hvk, &dep.members[0]);
    let (params, vk) = (pcreds.params(), hvk.vk());
    let parts = attestation_parts(pcreds, hvk, source, recipient.id(), &mut dep.rng);
    let ctx = pcreds.attestation_context(vk).expect("ctx");
    let run = fork(&parts.relation, &parts.witness, &ctx, seed);
    let attestation = Attestation {
        tag: parts.tag,
        show: parts.show.clone(),
        proof: run.proof.clone(),
    };
    assert_eq!(
        pcreds.check_attestation(hvk, recipient.id(), &attestation),
        Ok(())
    );

    let extracted = run.extract(&parts.relation);
    assert_eq!(
        extracted, parts.witness,
        "linear relations: the prover's witness"
    );
    assert_eq!(extracted[0], *source.user.expose_key(), "the source's key");
    // one usk for every clause: the tag clause alone ...
    assert_eq!(params.tag.eval(&extracted[0], &parts.x_q), Some(parts.tag));
    // ... and the clauses of Π_Possess alone (the tag clause allocates no variable)
    let possession = Bk::<B, T>::possession_relation(params, vk, &parts.show).expect("R_Possess");
    assert_eq!(possession.num_scalars(), parts.relation.num_scalars());
    assert!(possession.is_satisfied_by(&extracted));
    assert_eq!(usk_sharing(&parts.relation), (true, 1));
    B::check_extracted(
        &params.base,
        vk,
        &parts.show,
        &extracted,
        source.cred.as_inner(),
    );
    let extracted_user = pcreds.user(hvk, extracted[0]).expect("Tag(usk, x_0) ≠ ⊥");
    assert_eq!(
        extracted_user.id(),
        source.user.id(),
        "the source's identifier"
    );
    assert!(pcreds.verify_credential(hvk, &extracted_user, &source.cred));
    let mut wrong = extracted.clone();
    wrong[0] += Fr::one();
    assert!(!parts.relation.is_satisfied_by(&wrong));
    assert!(!possession.is_satisfied_by(&wrong));
    assert_ne!(params.tag.eval(&wrong[0], &parts.x_q), Some(parts.tag));
}

/// `π_iss`, `R_iss` at `(hvk, Ĉ, id_Q)` under `(ssid, att⃗)`: the extracted witness is
/// `(usk, τ)` of the requester (`expose_key`, `expose_tape`); `usk` opens `id_Q` at `x_0` and,
/// with `τ`, the request `Ĉ = PrepareIssue(hvk, usk; τ)`. Hypothesis (iv) and Correctness for
/// every `τ`: the helper's actual reply to this request, unblinded with the EXTRACTED `(usk, τ)`,
/// is a credential that verifies on the extracted `usk`.
fn extractor_on_issuance<B: Algebra, T: Forge>(label: &[u8], seed: u64) {
    let mut dep = Deployment::<B, T>::new(label, 1, seed);
    let requester = dep.register();
    let attestations = dep.attestations(&requester);
    let ssid = dep.ssid();
    let (pcreds, hvk) = (&dep.pcreds, &dep.hvk);
    let (params, vk, x0) = (pcreds.params(), hvk.vk(), *hvk.identifier_point());
    let (message, state) = pcreds
        .request_credential(hvk, &requester, attestations, &ssid, &mut dep.rng)
        .expect("request");
    let relation = Bk::<B, T>::issuance_relation(params, vk, &message.request, &message.id, &x0)
        .expect("R_iss");
    let ctx = pcreds
        .issuance_context(vk, &ssid, &message.attestations)
        .expect("ctx");
    assert!(
        fiat_shamir::verify(&relation, &ctx, &message.proof),
        "the protocol's π_iss is a proof of the rebuilt statement under the rebuilt context"
    );

    let witness = [*requester.expose_key(), *state.expose_tape()];
    let run = fork(&relation, &witness, &ctx, seed);
    let forked = CredentialRequest {
        proof: run.proof.clone(),
        ..message.clone()
    };
    let evaluated = pcreds
        .evaluate_request(&dep.helper, &forked, &ssid)
        .expect("the forked π_iss is accepted");
    assert!(evaluated.is_valid());

    let extracted = run.extract(&relation);
    assert_eq!(extracted, witness, "(usk, τ) of the requester");
    assert_eq!(params.tag.eval(&extracted[0], &x0), Some(message.id));
    assert_eq!(
        B::prepare_issue(&params.base, vk, &extracted[0], &extracted[1]),
        Some(message.request.clone()),
        "R_PrepareIssue"
    );
    assert_ne!(
        B::prepare_issue(&params.base, vk, &(extracted[0] + Fr::one()), &extracted[1]),
        Some(message.request.clone())
    );
    assert_eq!(usk_sharing(&relation), (true, 1));

    let reply = pcreds
        .respond(&mut dep.helper, evaluated, Decision::Policy, &mut dep.rng)
        .expect("respond");
    let Reply::PreCredential(pre) = reply else {
        panic!("a valid request is issued");
    };
    let cred = <Bk<B, T> as Backend>::unblind(params, vk, &extracted[0], &pre, &extracted[1])
        .expect("the extracted witness completes the reply");
    assert!(<Bk<B, T> as Backend>::verify(
        params,
        vk,
        &extracted[0],
        &cred
    ));
}

/// `π_prove`, `R_Possess` at `(hvk, σ*)` under `m`: from a membership proof the verifier accepts,
/// the extractor recovers the holder's witness, which yields a credential, and the user built
/// from the extracted key is the holder (same identifier; its credential verifies); the
/// protocol's own membership proof is a proof of the statement rebuilt here.
fn extractor_on_membership_proof<B: Algebra, T: Forge>(label: &[u8], seed: u64) {
    let mut dep = Deployment::<B, T>::new(label, 1, seed);
    let (pcreds, hvk, holder) = (&dep.pcreds, &dep.hvk, &dep.members[0]);
    let (params, vk) = (pcreds.params(), hvk.vk());
    let message = b"posted anonymously";
    let (show, relation, witness) = membership_parts(pcreds, hvk, holder, &mut dep.rng);
    let ctx = pcreds.prove_context(vk, message).expect("ctx");
    let run = fork(&relation, &witness, &ctx, seed);
    let proof = MembershipProof {
        show: show.clone(),
        proof: run.proof.clone(),
    };
    assert_eq!(pcreds.check_membership(hvk, message, &proof), Ok(()));

    let extracted = run.extract(&relation);
    assert_eq!(extracted, witness);
    assert_eq!(extracted[0], *holder.user.expose_key(), "the holder's key");
    B::check_extracted(&params.base, vk, &show, &extracted, holder.cred.as_inner());
    let extracted_user = pcreds.user(hvk, extracted[0]).expect("Tag(usk, x_0) ≠ ⊥");
    assert_eq!(
        extracted_user.id(),
        holder.user.id(),
        "the holder's identifier"
    );
    assert!(pcreds.verify_credential(hvk, &extracted_user, &holder.cred));

    let own = pcreds
        .prove(hvk, &holder.user, &holder.cred, message, &mut dep.rng)
        .expect("Prove");
    let rebuilt = Bk::<B, T>::possession_relation(params, vk, &own.show).expect("R_Possess");
    assert!(fiat_shamir::verify(&rebuilt, &ctx, &own.proof));
}

every_pair!(extractor_on_identifier_proof, 0x5c01_0000);
every_pair!(extractor_on_attestation, 0x5c02_0000);
every_pair!(extractor_on_issuance, 0x5c03_0000);
every_pair!(extractor_on_membership_proof, 0x5c04_0000);

/// Lemma `lem:base-bbs` (v), case (b): a prover that knows the issuing key `x` (a corrupted
/// helper) shows a "credential" for a key that no credential certifies, with `r_1 = 0` and
/// `e = −x`: `D = B(usk, ρ)` (`r_3 = 1`), `Ā = D^s`, `B̄ = Ā^x`, `u` arbitrary and
/// `v = 1/s − x·u`. The verifier accepts the attestation (integrity is required only for an
/// honest helper, Remark "Helper-key convention"). The extracted witness has `r_1 = 0`, so the
/// case (a) formula `A = Ā^(r_3/r_1)` is undefined; case (b) sets `δ = v − e·u`, `e' = δ + e`,
/// `A = Ā^(r_3)` and `ω = (1, 1/r_3)`, and the credential verifies on the extracted key. Without
/// the third clause `D = B̄^u Ā^v` there is no `δ`.
#[test]
fn bbs_extraction_covers_a_prover_that_knows_the_issuing_key() {
    let label = b"pcreds-snd/bbs-case-b";
    let seed = 0x5c05_0001;
    let mut rng = StdRng::seed_from_u64(seed);
    let pcreds = Protocol::<Bk<BBS, DDH>>::setup(label).expect("Setup");
    let x = nonzero(&mut rng);
    let helper = helper_with_key(&pcreds, &BBSVerificationKey(G2::generator() * x), x);
    let hvk = pcreds.helper_key(helper.key().vk()).expect("hvk ∈ V_pp");
    let (params, vk) = (pcreds.params(), hvk.vk());
    let pp = &params.base;
    let impostor = pcreds.register(&hvk, &mut rng).expect("Register");
    let recipient = pcreds.register(&hvk, &mut rng).expect("Register");

    let (usk, rho) = (*impostor.expose_key(), Fr::rand(&mut rng));
    let (s, u) = (nonzero(&mut rng), Fr::rand(&mut rng));
    let d = pp.b(&usk, &rho);
    let a_bar = d * s;
    let show = BBSShow {
        a_bar,
        b_bar: a_bar * x,
        d,
    };
    let v = s.inverse().expect("s ≠ 0") - x * u;
    let witness = [usk, rho, Fr::zero(), -x, Fr::one(), u, v];
    let x_q = pcreds.recipient_point(vk, recipient.id()).expect("H_req");
    let tag = params.tag.eval(&usk, &x_q).expect("Tag(usk, x_Q) ≠ ⊥");
    let relation =
        Bk::<BBS, DDH>::attestation_relation(params, vk, &show, &tag, &x_q).expect("R_att");
    assert!(relation.is_satisfied_by(&witness));
    let ctx = pcreds.attestation_context(vk).expect("ctx");
    let run = fork(&relation, &witness, &ctx, seed);
    let attestation = Attestation {
        tag,
        show: show.clone(),
        proof: run.proof.clone(),
    };
    assert_eq!(
        pcreds.check_attestation(&hvk, recipient.id(), &attestation),
        Ok(())
    );

    let extracted = run.extract(&relation);
    assert_eq!(extracted, witness);
    let &[usk_x, rho_x, r1_x, e_x, r3_x, u_x, v_x] = extracted.as_slice() else {
        panic!("seven variables");
    };
    assert!(r1_x.is_zero(), "case (b)");
    let delta = v_x - e_x * u_x;
    assert!(!delta.is_zero(), "δ ≠ 0 because D ≠ 1");
    let cred = BBSCredential {
        a: a_bar * r3_x,
        e: delta + e_x,
        rho: rho_x,
    };
    assert!(<BBS as Base<E>>::verify(pp, vk, &usk_x, &cred));
    let omega_2 = r3_x.inverse().expect("r_3 ≠ 0");
    assert_eq!(bbs_rerand(pp, &usk_x, &cred, Fr::one(), omega_2), show);
    assert_eq!(params.tag.eval(&usk_x, &x_q), Some(tag));
}

// ---------------------------------------------------------------------------------------------
// (b) The shared witness
// ---------------------------------------------------------------------------------------------

/// `R_att` and `R_iss` share ONE variable `usk` between the clauses of the base and the tag
/// clause. A statement whose tag (identifier) belongs to another key than the credential
/// (request) therefore has no witness: neither key satisfies both parts, and the prover of
/// `fiat_shamir` and the backend's provers refuse. Contrast: the same clauses with two key
/// variables (an unshared composition) accept a source's credential with an uncredentialed key's
/// tag, and the extractor then returns two different keys; such a proof is no attestation.
fn shared_witness<B: Algebra, T: Forge>(label: &[u8], seed: u64) {
    let mut dep = Deployment::<B, T>::new(label, 1, seed);
    let recipient = dep.register();
    let outsider = dep.register();
    let ssid = dep.ssid();
    let (pcreds, hvk, source) = (&dep.pcreds, &dep.hvk, &dep.members[0]);
    let (params, vk, x0) = (pcreds.params(), hvk.vk(), *hvk.identifier_point());
    let outsider_key = *outsider.expose_key();
    let parts = attestation_parts(pcreds, hvk, source, recipient.id(), &mut dep.rng);
    let ctx = pcreds.attestation_context(vk).expect("ctx");

    // R_att with the outsider's tag for the recipient and the source's show
    let foreign = params
        .tag
        .eval(&outsider_key, &parts.x_q)
        .expect("Tag(usk', x_Q) ≠ ⊥");
    let relation = Bk::<B, T>::attestation_relation(params, vk, &parts.show, &foreign, &parts.x_q)
        .expect("R_att");
    assert!(parts.relation.is_satisfied_by(&parts.witness), "control");
    assert!(
        !relation.is_satisfied_by(&parts.witness),
        "the credential's key fails the tag clause"
    );
    let mut with_outsider = parts.witness.clone();
    with_outsider[0] = outsider_key;
    assert!(
        !relation.is_satisfied_by(&with_outsider),
        "the tag's key fails the clauses of the base"
    );
    for witness in [&parts.witness, &with_outsider] {
        assert_eq!(
            fiat_shamir::prove(&relation, witness, &ctx, &mut dep.rng).err(),
            Some(Error::WitnessDoesNotSatisfyRelation)
        );
    }
    let statement = AttestationStatement::<Bk<B, T>> {
        vk,
        tag: &foreign,
        point: &parts.x_q,
    };
    assert_eq!(
        <Bk<B, T> as Backend>::prove_attestation(
            params,
            &statement,
            source.user.expose_key(),
            source.cred.as_inner(),
            &ctx,
            &mut dep.rng,
        )
        .err(),
        Some(Error::WitnessDoesNotSatisfyRelation)
    );

    // the same clauses, unshared: one key variable for Π_Possess, another for the tag clause
    let mut unshared = PairingRelation::<E>::new();
    let possession_key = unshared.alloc_scalar();
    B::possession_clauses(&params.base, vk, &parts.show, &mut unshared, possession_key)
        .expect("Π_Possess");
    let tag_key = unshared.alloc_scalar();
    for equation in params.tag.tag_equations(tag_key, &foreign, &parts.x_q) {
        unshared.add_g1(equation).expect("tag clause");
    }
    assert_eq!(usk_sharing(&parts.relation), (true, 1));
    assert_eq!(
        usk_sharing(&unshared),
        (false, 1),
        "the tag clause is on another key"
    );
    let mut unshared_witness = parts.witness.clone();
    unshared_witness.push(outsider_key);
    let run = fork(&unshared, &unshared_witness, &ctx, seed);
    let extracted = run.extract(&unshared);
    assert_eq!(extracted[possession_key.index()], *source.user.expose_key());
    assert_eq!(extracted[tag_key.index()], outsider_key);
    let pooled = Attestation {
        tag: foreign,
        show: parts.show.clone(),
        proof: run.proof.clone(),
    };
    assert_eq!(
        pcreds.check_attestation(hvk, recipient.id(), &pooled),
        Err(Error::InvalidProof)
    );

    // R_iss with the outsider's identifier and the recipient's request
    let (message, state) = pcreds
        .request_credential(hvk, &recipient, Vec::new(), &ssid, &mut dep.rng)
        .expect("request");
    let relation = Bk::<B, T>::issuance_relation(params, vk, &message.request, outsider.id(), &x0)
        .expect("R_iss");
    let ctx = pcreds.issuance_context(vk, &ssid, &[]).expect("ctx");
    let tau = *state.expose_tape();
    for key in [*recipient.expose_key(), outsider_key] {
        assert!(!relation.is_satisfied_by(&[key, tau]));
        assert_eq!(
            fiat_shamir::prove(&relation, &[key, tau], &ctx, &mut dep.rng).err(),
            Some(Error::WitnessDoesNotSatisfyRelation)
        );
    }
    let statement = IssuanceStatement::<Bk<B, T>> {
        vk,
        request: &message.request,
        id: outsider.id(),
        x0: &x0,
    };
    assert_eq!(
        <Bk<B, T> as Backend>::prove_issuance(
            params,
            &statement,
            recipient.expose_key(),
            state.expose_tape(),
            &ctx,
            &mut dep.rng,
        )
        .err(),
        Some(Error::WitnessDoesNotSatisfyRelation)
    );
}

every_pair!(shared_witness, 0x5c06_0000);

// ---------------------------------------------------------------------------------------------
// (c) Special honest-verifier zero knowledge
// ---------------------------------------------------------------------------------------------

/// Special HVZK on `relation`: for three uniform challenges and the edge values `0` and `1`, the
/// simulator's `(A, z)` verifies interactively, `A` has one component per equation in each group
/// (as an honest commitment), `z` has one response per variable (the number the codec fixes for
/// `kind`), and `(c, z)` has the compact encoding of a proof of `kind`. Returned as `(c, z)`.
fn simulated<B: Algebra, T: Forge>(
    relation: &PairingRelation<E>,
    kind: ProofKind,
    rng: &mut StdRng,
) -> Vec<FSProof<Fr>> {
    let shape = |image: &PairingImage<E>| (image.g1.len(), image.g2.len(), image.gt.len());
    let equations = (
        relation.g1_equations().len(),
        relation.g2_equations().len(),
        relation.gt_equations().len(),
    );
    let (honest, _) = commit(relation, rng).expect("commit");
    assert_eq!(shape(&honest), equations);
    let challenges = [
        Fr::rand(rng),
        Fr::rand(rng),
        Fr::rand(rng),
        Fr::zero(),
        Fr::one(),
    ];
    challenges
        .into_iter()
        .map(|challenge| {
            let (commitment, responses) = simulate(relation, &challenge, rng).expect("simulate");
            assert!(verify(relation, &commitment, &challenge, &responses));
            assert_eq!(shape(&commitment), equations);
            assert_eq!(responses.len(), relation.num_scalars());
            assert_eq!(responses.len(), Bk::<B, T>::responses(kind));
            let proof = FSProof {
                challenge,
                responses,
            };
            let mut wire = Vec::new();
            <Bk<B, T> as Backend>::serialize_proof_compact(kind, &proof, &mut wire)
                .expect("the shape of a proof of this kind");
            assert_eq!(
                wire.len(),
                <Bk<B, T> as Backend>::proof_compact_size(&proof)
            );
            proof
        })
        .collect()
}

/// The simulator on the four statements as their verifiers rebuild them from honest messages,
/// and on a FALSE statement (an attestation with an uncredentialed key's tag): it needs no
/// witness, so an accepting transcript at a challenge fixed in advance is no evidence. As
/// Fiat–Shamir proofs the simulated transcripts are rejected, by `fiat_shamir::verify` and by the
/// protocol's verifiers: `c ≠ H_1(ctx, statement, A)` except with probability `1/p` per
/// transcript in the random-oracle model, for the uniform `c` and for `c ∈ {0, 1}` alike.
fn simulator<B: Algebra, T: Forge>(label: &[u8], seed: u64) {
    let mut dep = Deployment::<B, T>::new(label, 1, seed);
    let requester = dep.register();
    let outsider = dep.register();
    let attestation = dep.attestation(0, &requester);
    let ssid = dep.ssid();
    let contact = b"member-0@example";
    let (pcreds, hvk, holder) = (&dep.pcreds, &dep.hvk, &dep.members[0]);
    let (params, vk, x0) = (pcreds.params(), hvk.vk(), *hvk.identifier_point());
    let x_q = pcreds.recipient_point(vk, requester.id()).expect("H_req");
    let request = pcreds
        .request_attestation(hvk, &requester, &ssid, contact, &mut dep.rng)
        .expect("π_id");
    let (message, _) = pcreds
        .request_credential(
            hvk,
            &requester,
            vec![attestation.clone()],
            &ssid,
            &mut dep.rng,
        )
        .expect("request");
    let membership = pcreds
        .prove(hvk, &holder.user, &holder.cred, b"m", &mut dep.rng)
        .expect("Prove");
    let mut rng = StdRng::seed_from_u64(seed ^ SIMULATOR);

    let relation = Bk::<B, T>::identifier_relation(params, &request.id, &x0).expect("R_Tag");
    let ctx = pcreds.identifier_context(&ssid, contact);
    for proof in simulated::<B, T>(&relation, ProofKind::Identifier, &mut rng) {
        assert!(!fiat_shamir::verify(&relation, &ctx, &proof));
        let forged = AttestationRequest {
            id: request.id,
            proof,
        };
        assert_eq!(
            pcreds
                .receive_attestation_request(hvk, &forged, &ssid, contact)
                .err(),
            Some(Error::InvalidProof)
        );
    }

    let relation =
        Bk::<B, T>::attestation_relation(params, vk, &attestation.show, &attestation.tag, &x_q)
            .expect("R_att");
    let ctx = pcreds.attestation_context(vk).expect("ctx");
    for proof in simulated::<B, T>(&relation, ProofKind::Attestation, &mut rng) {
        assert!(!fiat_shamir::verify(&relation, &ctx, &proof));
        let forged = Attestation {
            proof,
            ..attestation.clone()
        };
        assert_eq!(
            pcreds.check_attestation(hvk, requester.id(), &forged),
            Err(Error::InvalidProof)
        );
    }

    let foreign = params
        .tag
        .eval(outsider.expose_key(), &x_q)
        .expect("Tag(usk', x_Q) ≠ ⊥");
    let false_statement =
        Bk::<B, T>::attestation_relation(params, vk, &attestation.show, &foreign, &x_q)
            .expect("R_att");
    for proof in simulated::<B, T>(&false_statement, ProofKind::Attestation, &mut rng) {
        assert!(!fiat_shamir::verify(&false_statement, &ctx, &proof));
        let forged = Attestation {
            tag: foreign,
            show: attestation.show.clone(),
            proof,
        };
        assert_eq!(
            pcreds.check_attestation(hvk, requester.id(), &forged),
            Err(Error::InvalidProof)
        );
    }

    let relation = Bk::<B, T>::issuance_relation(params, vk, &message.request, &message.id, &x0)
        .expect("R_iss");
    let ctx = pcreds
        .issuance_context(vk, &ssid, &message.attestations)
        .expect("ctx");
    for proof in simulated::<B, T>(&relation, ProofKind::Issuance, &mut rng) {
        assert!(!fiat_shamir::verify(&relation, &ctx, &proof));
        let forged = CredentialRequest {
            proof,
            ..message.clone()
        };
        assert_eq!(
            pcreds.evaluate_request(&dep.helper, &forged, &ssid).err(),
            Some(Error::InvalidProof)
        );
    }

    let relation =
        Bk::<B, T>::possession_relation(params, vk, &membership.show).expect("R_Possess");
    let ctx = pcreds.prove_context(vk, b"m").expect("ctx");
    for proof in simulated::<B, T>(&relation, ProofKind::Possession, &mut rng) {
        assert!(!fiat_shamir::verify(&relation, &ctx, &proof));
        let forged = MembershipProof {
            show: membership.show.clone(),
            proof,
        };
        assert_eq!(
            pcreds.check_membership(hvk, b"m", &forged),
            Err(Error::InvalidProof)
        );
    }
}

every_pair!(simulator, 0x5c07_0000);

// ---------------------------------------------------------------------------------------------
// (d) The weak Fiat–Shamir attack
// ---------------------------------------------------------------------------------------------

/// The "weak" transform: the challenge from the tag of `ctx` (which names the ciphersuite of
/// `relation` and nothing else of it) and the commitment `A`, without the statement.
fn weak_challenge(relation: &PairingRelation<E>, ctx: &[u8], commitment: &PairingImage<E>) -> Fr {
    let tag = fiat_shamir::tag(relation, ctx);
    let mut sponge = DuplexSponge::new(&derive_session_id(&tag));
    sponge.absorb(
        &relation
            .serialize_image(commitment)
            .expect("a commitment of the shape of the relation"),
    );
    squeeze_scalar(&mut sponge)
}

/// Verification under the weak transform.
fn weak_verify(relation: &PairingRelation<E>, ctx: &[u8], proof: &FSProof<Fr>) -> bool {
    relation
        .recompute_commitment(&proof.challenge, &proof.responses)
        .is_ok_and(|commitment| weak_challenge(relation, ctx, &commitment) == proof.challenge)
}

/// The cheating prover of the weak Fiat–Shamir attack, on a relation whose LAST `G_1` equation is
/// a tag clause on `usk` (the attestation and issuance relations): honest masks from the tape
/// `tape` for the clauses it can prove, the element `tag_commitment` of its choice for the tag
/// clause, the challenge `challenge(A)`, the responses on `witness`, and only THEN the tag at
/// `point` that makes the tag clause accept. Returns `(A, (c, z), t)`.
fn cheat<T: Forge>(
    tag_function: &T,
    relation: &PairingRelation<E>,
    witness: &[Fr],
    point: &Fr,
    tag_commitment: G1,
    tape: u64,
    challenge: impl FnOnce(&PairingImage<E>) -> Fr,
) -> (PairingImage<E>, FSProof<Fr>, G1) {
    let (mut commitment, state) =
        commit(relation, &mut StdRng::seed_from_u64(tape)).expect("commit");
    *commitment.g1.last_mut().expect("a tag clause") = tag_commitment;
    let c = challenge(&commitment);
    let responses = respond(state, witness, &c).expect("respond");
    let tag = tag_function.solve(point, &tag_commitment, &c, &responses[0]);
    (
        commitment,
        FSProof {
            challenge: c,
            responses,
        },
        tag,
    )
}

/// The weak Fiat–Shamir attack on `π_att` (W1 of the reference-implementation review). A source
/// with ONE credential commits honestly to its possession clauses and freely to the tag clause,
/// and solves for the tag after the challenge: a valid tag in `T` of a key it has no credential
/// for, a fresh one per attempt.
///
/// (1) Against the weak transform the forgery verifies, and five attempts give five pairwise
/// distinct tags, which a helper would count as five sources. (2) The crate hashes the statement,
/// which contains the tag, so the verifier's challenge differs: `fiat_shamir::verify` and
/// `check_attestation` reject. (3) Solving for the tag with the challenge of the CURRENT statement
/// changes the statement and with it the challenge: eight rounds of chasing a fixed point all fail.
fn weak_fiat_shamir_on_attestation<B: Algebra, T: Forge>(label: &[u8], seed: u64) {
    let mut dep = Deployment::<B, T>::new(label, 1, seed);
    let recipient = dep.register();
    let (pcreds, hvk) = (&dep.pcreds, &dep.hvk);
    let (params, vk) = (pcreds.params(), hvk.vk());
    let parts = attestation_parts(pcreds, hvk, &dep.members[0], recipient.id(), &mut dep.rng);
    let ctx = pcreds.attestation_context(vk).expect("ctx");
    let mut adversary = StdRng::seed_from_u64(seed ^ ADVERSARY);
    let tape = seed ^ CHEATING_TAPE;
    let statement = |tag: &G1| {
        Bk::<B, T>::attestation_relation(params, vk, &parts.show, tag, &parts.x_q).expect("R_att")
    };

    let mut minted: Vec<G1> = Vec::new();
    for _ in 0..5 {
        let (commitment, proof, forged) = cheat(
            &params.tag,
            &parts.relation,
            &parts.witness,
            &parts.x_q,
            G1::rand(&mut adversary),
            tape,
            |a| weak_challenge(&parts.relation, &ctx, a),
        );
        let relation = statement(&forged);
        assert!(verify(
            &relation,
            &commitment,
            &proof.challenge,
            &proof.responses
        ));
        assert!(
            weak_verify(&relation, &ctx, &proof),
            "the weak transform is broken"
        );
        assert!(
            !relation.is_satisfied_by(&parts.witness),
            "false for the only key with a credential"
        );
        assert_eq!(
            <Bk<B, T> as Backend>::check_tag(params, &forged, &parts.x_q, "t"),
            Ok(()),
            "an admissible tag"
        );
        assert!(!fiat_shamir::verify(&relation, &ctx, &proof));
        let attestation = Attestation {
            tag: forged,
            show: parts.show.clone(),
            proof,
        };
        assert_eq!(
            pcreds.check_attestation(hvk, recipient.id(), &attestation),
            Err(Error::InvalidProof)
        );
        assert!(!minted.contains(&forged) && forged != parts.tag);
        minted.push(forged);
    }

    let tag_commitment = G1::rand(&mut adversary);
    let mut tag = parts.tag;
    for round in 0..8 {
        let current = statement(&tag);
        let (commitment, proof, next) = cheat(
            &params.tag,
            &parts.relation,
            &parts.witness,
            &parts.x_q,
            tag_commitment,
            tape,
            |a| fiat_shamir::challenge(&current, &ctx, a).expect("H_1"),
        );
        let relation = statement(&next);
        assert!(verify(
            &relation,
            &commitment,
            &proof.challenge,
            &proof.responses
        ));
        assert!(
            !fiat_shamir::verify(&relation, &ctx, &proof),
            "round {round}"
        );
        assert_ne!(next, tag, "round {round}");
        tag = next;
    }
}

/// The weak Fiat–Shamir attack on `π_iss`: a requester with its own key and request `Ĉ` solves
/// for the IDENTIFIER after the challenge, a fresh identifier of a key nobody holds. Under the
/// weak transform the helper would accept `Ĉ`, a request on the requester's key, under as many
/// identifiers it has never issued to as the requester likes: one key would obtain many
/// credentials although the helper issues at most once per identifier. The crate's transform
/// rejects every such request.
fn weak_fiat_shamir_on_issuance<B: Algebra, T: Forge>(label: &[u8], seed: u64) {
    let mut dep = Deployment::<B, T>::new(label, 1, seed);
    let requester = dep.register();
    let ssid = dep.ssid();
    let (pcreds, hvk) = (&dep.pcreds, &dep.hvk);
    let (params, vk, x0) = (pcreds.params(), hvk.vk(), *hvk.identifier_point());
    let (message, state) = pcreds
        .request_credential(hvk, &requester, Vec::new(), &ssid, &mut dep.rng)
        .expect("request");
    let relation = Bk::<B, T>::issuance_relation(params, vk, &message.request, &message.id, &x0)
        .expect("R_iss");
    let witness = [*requester.expose_key(), *state.expose_tape()];
    let ctx = pcreds.issuance_context(vk, &ssid, &[]).expect("ctx");
    let mut adversary = StdRng::seed_from_u64(seed ^ ADVERSARY);

    for _ in 0..3 {
        let (commitment, proof, forged_id) = cheat(
            &params.tag,
            &relation,
            &witness,
            &x0,
            G1::rand(&mut adversary),
            seed ^ CHEATING_TAPE,
            |a| weak_challenge(&relation, &ctx, a),
        );
        let forged = Bk::<B, T>::issuance_relation(params, vk, &message.request, &forged_id, &x0)
            .expect("R_iss");
        assert!(verify(
            &forged,
            &commitment,
            &proof.challenge,
            &proof.responses
        ));
        assert!(
            weak_verify(&forged, &ctx, &proof),
            "the weak transform is broken"
        );
        assert_ne!(forged_id, message.id);
        assert!(!forged.is_satisfied_by(&witness));
        assert_eq!(
            <Bk<B, T> as Backend>::check_tag(params, &forged_id, &x0, "id_Q"),
            Ok(())
        );
        assert!(!fiat_shamir::verify(&forged, &ctx, &proof));
        let request = CredentialRequest {
            id: forged_id,
            attestations: Vec::new(),
            request: message.request.clone(),
            proof,
        };
        assert_eq!(
            pcreds.evaluate_request(&dep.helper, &request, &ssid).err(),
            Some(Error::InvalidProof)
        );
    }
    assert!(
        pcreds
            .evaluate_request(&dep.helper, &message, &ssid)
            .is_ok()
    );
}

every_pair!(weak_fiat_shamir_on_attestation, 0x5c08_0000);
every_pair!(weak_fiat_shamir_on_issuance, 0x5c09_0000);

// ---------------------------------------------------------------------------------------------
// (e) Contexts are the verifier's
// ---------------------------------------------------------------------------------------------

/// A proof on `witness` under the context the verifier rebuilds passes `check`; proofs under each
/// of the `others` contexts are well formed for their own context and are rejected by `check`.
fn only_the_rebuilt_context(
    relation: &PairingRelation<E>,
    witness: &[Fr],
    rebuilt: &[u8],
    others: &[Vec<u8>],
    rng: &mut StdRng,
    check: impl Fn(FSProof<Fr>) -> Result<(), Error>,
) {
    let proof = fiat_shamir::prove(relation, witness, rebuilt, rng).expect("prove");
    assert_eq!(check(proof), Ok(()), "the context the verifier rebuilds");
    for ctx in others {
        assert_ne!(ctx.as_slice(), rebuilt);
        let proof = fiat_shamir::prove(relation, witness, ctx, rng).expect("prove");
        assert!(fiat_shamir::verify(relation, ctx, &proof));
        assert_eq!(check(proof), Err(Error::InvalidProof));
    }
}

/// The protocol's verifiers take no context from the prover: they rebuild it from public data. A
/// proof of the right statement made under any other context (empty; another session, contact,
/// message or attestation list; another deployment; another role's oracle) is rejected.
fn contexts_are_rebuilt_by_the_verifier<B: Algebra, T: Forge>(label: &[u8], seed: u64) {
    let mut dep = Deployment::<B, T>::new(label, 1, seed);
    let elsewhere = Protocol::<Bk<B, T>>::setup(b"pcreds-snd/another deployment").expect("Setup");
    let requester = dep.register();
    let attestation = dep.attestation(0, &requester);
    let ssid = dep.ssid();
    let contact = b"member-0@example";
    let (pcreds, hvk, holder) = (&dep.pcreds, &dep.hvk, &dep.members[0]);
    let (params, vk, x0) = (pcreds.params(), hvk.vk(), *hvk.identifier_point());
    let mut rng = StdRng::seed_from_u64(seed ^ CONTEXTS);
    let m = b"posted";
    let digest = |ctx: [u8; 32]| ctx.to_vec();

    // π_id
    let relation = Bk::<B, T>::identifier_relation(params, requester.id(), &x0).expect("R_Tag");
    only_the_rebuilt_context(
        &relation,
        &[*requester.expose_key()],
        &pcreds.identifier_context(&ssid, contact),
        &[
            Vec::new(),
            digest(pcreds.identifier_context(b"another ssid", contact)),
            digest(pcreds.identifier_context(&ssid, b"another contact")),
            digest(elsewhere.identifier_context(&ssid, contact)),
            digest(pcreds.prove_context(vk, &ssid).expect("ctx")),
        ],
        &mut rng,
        |proof| {
            let request = AttestationRequest {
                id: *requester.id(),
                proof,
            };
            pcreds
                .receive_attestation_request(hvk, &request, &ssid, contact)
                .map(|_| ())
        },
    );

    // π_att
    let parts = attestation_parts(pcreds, hvk, holder, requester.id(), &mut rng);
    only_the_rebuilt_context(
        &parts.relation,
        &parts.witness,
        &pcreds.attestation_context(vk).expect("ctx"),
        &[
            Vec::new(),
            digest(elsewhere.attestation_context(vk).expect("ctx")),
            digest(pcreds.prove_context(vk, b"").expect("ctx")),
            digest(pcreds.identifier_context(b"", b"")),
        ],
        &mut rng,
        |proof| {
            let attestation = Attestation {
                tag: parts.tag,
                show: parts.show.clone(),
                proof,
            };
            pcreds.check_attestation(hvk, requester.id(), &attestation)
        },
    );

    // π_iss
    let attestations = vec![attestation];
    let (message, state) = pcreds
        .request_credential(hvk, &requester, attestations.clone(), &ssid, &mut rng)
        .expect("request");
    let relation = Bk::<B, T>::issuance_relation(params, vk, &message.request, &message.id, &x0)
        .expect("R_iss");
    only_the_rebuilt_context(
        &relation,
        &[*requester.expose_key(), *state.expose_tape()],
        &pcreds
            .issuance_context(vk, &ssid, &attestations)
            .expect("ctx"),
        &[
            Vec::new(),
            digest(
                pcreds
                    .issuance_context(vk, b"another ssid", &attestations)
                    .expect("ctx"),
            ),
            digest(pcreds.issuance_context(vk, &ssid, &[]).expect("ctx")),
            digest(
                elsewhere
                    .issuance_context(vk, &ssid, &attestations)
                    .expect("ctx"),
            ),
            digest(pcreds.attestation_context(vk).expect("ctx")),
        ],
        &mut rng,
        |proof| {
            let request = CredentialRequest {
                proof,
                ..message.clone()
            };
            pcreds
                .evaluate_request(&dep.helper, &request, &ssid)
                .map(|_| ())
        },
    );

    // π_prove
    let (show, relation, witness) = membership_parts(pcreds, hvk, holder, &mut rng);
    only_the_rebuilt_context(
        &relation,
        &witness,
        &pcreds.prove_context(vk, m).expect("ctx"),
        &[
            Vec::new(),
            digest(pcreds.prove_context(vk, b"another message").expect("ctx")),
            digest(elsewhere.prove_context(vk, m).expect("ctx")),
            digest(pcreds.attestation_context(vk).expect("ctx")),
        ],
        &mut rng,
        |proof| {
            let membership = MembershipProof {
                show: show.clone(),
                proof,
            };
            pcreds.check_membership(hvk, m, &membership)
        },
    );
}

every_pair!(contexts_are_rebuilt_by_the_verifier, 0x5c0a_0000);

// ---------------------------------------------------------------------------------------------
// (f) A proof is bound to its statement
// ---------------------------------------------------------------------------------------------

/// Where the binding to `hvk` lives. For `Σ-BBS` no clause mentions `vk`, so the relation under
/// another key is the SAME statement and the proof verifies for it under the first key's
/// context: only the context binds the key. For `Σ-PS` the relation itself changes.
fn assert_key_binding<B: Algebra>(
    relation: &PairingRelation<E>,
    under_other_key: &PairingRelation<E>,
    ctx: &[u8],
    other_ctx: &[u8],
    proof: &FSProof<Fr>,
) {
    assert!(fiat_shamir::verify(relation, ctx, proof));
    assert_eq!(relation == under_other_key, !B::CLAUSES_MENTION_VK);
    assert_eq!(
        fiat_shamir::verify(under_other_key, ctx, proof),
        !B::CLAUSES_MENTION_VK
    );
    assert!(!fiat_shamir::verify(under_other_key, other_ctx, proof));
}

/// A valid proof does not verify for another statement or context: `π_att` for another
/// recipient (`x_Q`), another tag, another show of the SAME credential (a true statement) or
/// another helper key; `π_iss` for another identifier, another request `Ĉ` of the same user,
/// another attestation list, session or helper key; `π_prove` for another message, show or
/// helper key; `π_id` for another session, contact or identifier. Under another key the
/// rejection is `InvalidCredential` where the public check of the show mentions `vk` (`Σ-BBS`)
/// and `InvalidProof` otherwise.
fn binding_of_statements<B: Algebra, T: Forge>(label: &[u8], seed: u64) {
    let mut dep = Deployment::<B, T>::new(label, 2, seed);
    let requester = dep.register();
    let other = dep.register();
    let attestation = dep.attestation(0, &requester);
    let from_second_source = dep.attestation(1, &requester);
    let again = dep.attestation(0, &requester);
    let ssid = dep.ssid();
    let second_helper = dep
        .pcreds
        .helper_keygen(Policy::threshold(2).expect("k ≥ 1"), &mut dep.rng);
    let hvk2 = dep
        .pcreds
        .helper_key(second_helper.key().vk())
        .expect("hvk ∈ V_pp");
    let (pcreds, hvk, holder) = (&dep.pcreds, &dep.hvk, &dep.members[0]);
    let (params, vk, vk2) = (pcreds.params(), hvk.vk(), hvk2.vk());
    let x0 = *hvk.identifier_point();
    let under_another_key = if B::SHOW_CHECK_MENTIONS_VK {
        Error::InvalidCredential
    } else {
        Error::InvalidProof
    };

    // π_att
    assert_eq!(
        pcreds.check_attestation(hvk, requester.id(), &attestation),
        Ok(())
    );
    assert_eq!(
        pcreds.check_attestation(hvk, other.id(), &attestation),
        Err(Error::InvalidProof),
        "another recipient point"
    );
    let moved = Attestation {
        tag: from_second_source.tag,
        ..attestation.clone()
    };
    assert_eq!(
        pcreds.check_attestation(hvk, requester.id(), &moved),
        Err(Error::InvalidProof),
        "another tag"
    );
    assert_eq!(again.tag, attestation.tag);
    let moved = Attestation {
        show: again.show.clone(),
        ..attestation.clone()
    };
    assert_eq!(
        pcreds.check_attestation(hvk, requester.id(), &moved),
        Err(Error::InvalidProof),
        "another show of the same credential"
    );
    assert_eq!(
        pcreds.check_attestation(&hvk2, requester.id(), &attestation),
        Err(under_another_key.clone()),
        "another helper key"
    );
    let x_q = pcreds.recipient_point(vk, requester.id()).expect("H_req");
    assert_ne!(
        pcreds.recipient_point(vk2, requester.id()).expect("H_req"),
        x_q,
        "x_Q depends on hvk"
    );
    let relation =
        Bk::<B, T>::attestation_relation(params, vk, &attestation.show, &attestation.tag, &x_q)
            .expect("R_att");
    let relation2 =
        Bk::<B, T>::attestation_relation(params, vk2, &attestation.show, &attestation.tag, &x_q)
            .expect("R_att");
    assert_key_binding::<B>(
        &relation,
        &relation2,
        &pcreds.attestation_context(vk).expect("ctx"),
        &pcreds.attestation_context(vk2).expect("ctx"),
        &attestation.proof,
    );

    // π_iss
    let attestations = vec![attestation.clone(), from_second_source.clone()];
    let (message, _) = pcreds
        .request_credential(hvk, &requester, attestations.clone(), &ssid, &mut dep.rng)
        .expect("request");
    assert!(
        pcreds
            .evaluate_request(&dep.helper, &message, &ssid)
            .is_ok()
    );
    let refused = |request: &CredentialRequest<Bk<B, T>>, ssid: &[u8]| {
        pcreds.evaluate_request(&dep.helper, request, ssid).err()
    };
    let moved = CredentialRequest {
        id: *other.id(),
        ..message.clone()
    };
    assert_eq!(
        refused(&moved, &ssid),
        Some(Error::InvalidProof),
        "another identifier"
    );
    let (second, _) = pcreds
        .request_credential(hvk, &requester, attestations.clone(), &ssid, &mut dep.rng)
        .expect("request");
    assert_ne!(second.request, message.request);
    let moved = CredentialRequest {
        request: second.request.clone(),
        ..message.clone()
    };
    assert_eq!(
        refused(&moved, &ssid),
        Some(Error::InvalidProof),
        "another request of the same user"
    );
    let mut moved = message.clone();
    moved.attestations.swap(0, 1);
    assert_eq!(
        refused(&moved, &ssid),
        Some(Error::InvalidProof),
        "reordered"
    );
    let mut moved = message.clone();
    moved.attestations.pop();
    assert_eq!(
        refused(&moved, &ssid),
        Some(Error::InvalidProof),
        "shortened"
    );
    assert_eq!(
        refused(&message, b"another ssid"),
        Some(Error::InvalidProof),
        "another session"
    );
    assert_eq!(
        pcreds
            .evaluate_request(&second_helper, &message, &ssid)
            .err(),
        Some(Error::InvalidProof),
        "another helper key"
    );
    let relation = Bk::<B, T>::issuance_relation(params, vk, &message.request, &message.id, &x0)
        .expect("R_iss");
    let relation2 = Bk::<B, T>::issuance_relation(params, vk2, &message.request, &message.id, &x0)
        .expect("R_iss");
    assert_key_binding::<B>(
        &relation,
        &relation2,
        &pcreds
            .issuance_context(vk, &ssid, &attestations)
            .expect("ctx"),
        &pcreds
            .issuance_context(vk2, &ssid, &attestations)
            .expect("ctx"),
        &message.proof,
    );

    // π_prove
    let m = b"hello";
    let proof = pcreds
        .prove(hvk, &holder.user, &holder.cred, m, &mut dep.rng)
        .expect("Prove");
    let another = pcreds
        .prove(hvk, &holder.user, &holder.cred, m, &mut dep.rng)
        .expect("Prove");
    assert_eq!(pcreds.check_membership(hvk, m, &proof), Ok(()));
    assert_eq!(
        pcreds.check_membership(hvk, b"goodbye", &proof),
        Err(Error::InvalidProof),
        "another message"
    );
    let moved = MembershipProof {
        show: another.show.clone(),
        proof: proof.proof.clone(),
    };
    assert_eq!(
        pcreds.check_membership(hvk, m, &moved),
        Err(Error::InvalidProof),
        "another show"
    );
    assert_eq!(
        pcreds.check_membership(&hvk2, m, &proof),
        Err(under_another_key),
        "another helper key"
    );
    let relation = Bk::<B, T>::possession_relation(params, vk, &proof.show).expect("R_Possess");
    let relation2 = Bk::<B, T>::possession_relation(params, vk2, &proof.show).expect("R_Possess");
    assert_key_binding::<B>(
        &relation,
        &relation2,
        &pcreds.prove_context(vk, m).expect("ctx"),
        &pcreds.prove_context(vk2, m).expect("ctx"),
        &proof.proof,
    );

    // π_id
    let contact = b"member-0@example";
    let request = pcreds
        .request_attestation(hvk, &requester, &ssid, contact, &mut dep.rng)
        .expect("π_id");
    assert!(pcreds.verify_attestation_request(hvk, &request, &ssid, contact));
    assert!(!pcreds.verify_attestation_request(hvk, &request, b"another ssid", contact));
    assert!(!pcreds.verify_attestation_request(hvk, &request, &ssid, b"another contact"));
    let moved = AttestationRequest {
        id: *other.id(),
        proof: request.proof.clone(),
    };
    assert_eq!(
        pcreds
            .receive_attestation_request(hvk, &moved, &ssid, contact)
            .err(),
        Some(Error::InvalidProof),
        "another identifier"
    );
}

every_pair!(binding_of_statements, 0x5c0b_0000);

// ---------------------------------------------------------------------------------------------
// (g) Malleability under the issuing key
// ---------------------------------------------------------------------------------------------

/// Remark "Malleability under the issuing key": a holder of `y` moves the responses of a `Σ-PS`
/// possession proof along `(z_usk, z_t) ↦ (z_usk + δ, z_t − y·δ)`, which keeps the commitment,
/// the challenge, the statement and the context: `π_prove` of a membership proof is accepted
/// mauled. In `π_att` and `π_iss` (`C = g_1^ρ Y^usk`, the same move on `(z_usk, z_ρ)`) the tag
/// clause is on `usk` as well and the move breaks it. The move needs `y`: with `y + 1` it fails.
#[test]
fn ps_possession_proof_is_malleable_under_the_issuing_key() {
    let label = b"pcreds-snd/malleable/ps";
    let mut rng = StdRng::seed_from_u64(0x5c0c_0001);
    let pcreds = Protocol::<Bk<PS, DDH>>::setup(label).expect("Setup");
    let (x, y) = (nonzero(&mut rng), nonzero(&mut rng));
    let g2 = G2::generator();
    let vk = PSVerificationKey::<E> {
        x2: g2 * x,
        y2: g2 * y,
        y1: G1::generator() * y,
    };
    let mut helper = helper_with_key(&pcreds, &vk, x);
    let hvk = pcreds.helper_key(helper.key().vk()).expect("hvk ∈ V_pp");
    let holder = issue_roots(&pcreds, &mut helper, &hvk, 1, &mut rng)
        .pop()
        .expect("one holder");
    let recipient = pcreds.register(&hvk, &mut rng).expect("Register");
    let delta = nonzero(&mut rng);
    let maul = |proof: &FSProof<Fr>, slope: Fr| {
        let mut mauled = proof.clone();
        mauled.responses[0] += delta;
        mauled.responses[1] -= slope * delta;
        mauled
    };

    let m = b"posted";
    let membership = pcreds
        .prove(&hvk, &holder.user, &holder.cred, m, &mut rng)
        .expect("Prove");
    let mauled = MembershipProof {
        proof: maul(&membership.proof, y),
        ..membership.clone()
    };
    assert_ne!(mauled, membership);
    assert_eq!(
        pcreds.check_membership(&hvk, m, &mauled),
        Ok(()),
        "mauled π_prove"
    );
    let wrong = MembershipProof {
        proof: maul(&membership.proof, y + Fr::one()),
        ..membership.clone()
    };
    assert_eq!(
        pcreds.check_membership(&hvk, m, &wrong),
        Err(Error::InvalidProof)
    );

    let attestation = attest_through_protocol(&pcreds, &hvk, &holder, &recipient, b"att", &mut rng);
    let mauled = Attestation {
        proof: maul(&attestation.proof, y),
        ..attestation.clone()
    };
    assert_eq!(
        pcreds.check_attestation(&hvk, recipient.id(), &mauled),
        Err(Error::InvalidProof),
        "the tag clause pins z_usk"
    );

    let (message, _) = pcreds
        .request_credential(&hvk, &recipient, Vec::new(), b"iss", &mut rng)
        .expect("request");
    let mauled = CredentialRequest {
        proof: maul(&message.proof, y),
        ..message.clone()
    };
    assert_eq!(
        pcreds.evaluate_request(&helper, &mauled, b"iss").err(),
        Some(Error::InvalidProof),
        "the tag clause at x_0 pins z_usk"
    );
    assert!(pcreds.evaluate_request(&helper, &message, b"iss").is_ok());
}

/// The same for `Σ-BBS`, which the Remark does not mention: the third possession clause
/// `D = B̄^u Ā^v`, with `B̄ = Ā^x` (the public check), lets a holder of `x` move
/// `(z_u, z_v) ↦ (z_u + δ, z_v − x·δ)`. The variables `u, v` (5 and 6 of
/// `(usk, ρ, r_1, e, r_3, u, v)`) occur in no other clause, the tag clause included, so BOTH
/// `π_prove` and `π_att` are accepted mauled. The move needs `x`: with `x + 1` it fails. (Not
/// tested, an argument: the two clauses of the IETF/TZ show admit no such move for a holder of
/// `x`, which would need `log_Ā D` or a relation among `D, h_u, h_r`.)
#[test]
fn bbs_possession_proof_is_malleable_under_the_issuing_key() {
    let label = b"pcreds-snd/malleable/bbs";
    let mut rng = StdRng::seed_from_u64(0x5c0c_0002);
    let pcreds = Protocol::<Bk<BBS, DDH>>::setup(label).expect("Setup");
    let x = nonzero(&mut rng);
    let mut helper = helper_with_key(&pcreds, &BBSVerificationKey(G2::generator() * x), x);
    let hvk = pcreds.helper_key(helper.key().vk()).expect("hvk ∈ V_pp");
    let holder = issue_roots(&pcreds, &mut helper, &hvk, 1, &mut rng)
        .pop()
        .expect("one holder");
    let recipient = pcreds.register(&hvk, &mut rng).expect("Register");
    let delta = nonzero(&mut rng);
    let maul = |proof: &FSProof<Fr>, slope: Fr| {
        let mut mauled = proof.clone();
        mauled.responses[5] += delta;
        mauled.responses[6] -= slope * delta;
        mauled
    };

    let m = b"posted";
    let membership = pcreds
        .prove(&hvk, &holder.user, &holder.cred, m, &mut rng)
        .expect("Prove");
    let mauled = MembershipProof {
        proof: maul(&membership.proof, x),
        ..membership.clone()
    };
    assert_ne!(mauled, membership);
    assert_eq!(
        pcreds.check_membership(&hvk, m, &mauled),
        Ok(()),
        "mauled π_prove"
    );
    let wrong = MembershipProof {
        proof: maul(&membership.proof, x + Fr::one()),
        ..membership.clone()
    };
    assert_eq!(
        pcreds.check_membership(&hvk, m, &wrong),
        Err(Error::InvalidProof)
    );

    let attestation = attest_through_protocol(&pcreds, &hvk, &holder, &recipient, b"att", &mut rng);
    let mauled = Attestation {
        proof: maul(&attestation.proof, x),
        ..attestation.clone()
    };
    assert_ne!(mauled, attestation);
    assert_eq!(
        pcreds.check_attestation(&hvk, recipient.id(), &mauled),
        Ok(()),
        "mauled π_att"
    );
}

// ---------------------------------------------------------------------------------------------
// (h) Recipient-scoped linkability
// ---------------------------------------------------------------------------------------------

/// The compressed encodings of the `G_1` elements of a show, 48 bytes each.
fn show_elements<S: CanonicalSerialize>(show: &S) -> Vec<Vec<u8>> {
    let mut bytes = Vec::new();
    show.serialize_compressed(&mut bytes)
        .expect("a show serializes");
    assert_eq!(bytes.len() % 48, 0);
    bytes.chunks(48).map(<[u8]>::to_vec).collect()
}

/// `F_PCreds`, "Attestation tags": a tag is fixed for its pair of source and recipient, and
/// different pairs have different tags. Two attestations from one source to one recipient share
/// the tag `Tag(usk_P, x_Q)` and nothing else (fresh shows sharing no group element, fresh
/// proofs); the same source's tag for another recipient differs, so does another source's tag
/// for the same recipient, and no tag is a member's identifier `Tag(usk, x_0)` (`x_Q ≠ x_0`).
fn recipient_scoped_linkability<B: Algebra, T: Forge>(label: &[u8], seed: u64) {
    let mut dep = Deployment::<B, T>::new(label, 2, seed);
    let (q1, q2) = (dep.register(), dep.register());
    let first = dep.attestation(0, &q1);
    let repeated = dep.attestation(0, &q1);
    let to_q2 = dep.attestation(0, &q2);
    let from_second_source = dep.attestation(1, &q1);
    let (pcreds, hvk) = (&dep.pcreds, &dep.hvk);
    let (params, vk) = (pcreds.params(), hvk.vk());

    assert_eq!(
        first.tag, repeated.tag,
        "one source, one recipient: one tag"
    );
    assert_ne!(first.proof, repeated.proof);
    for (a, b) in [(&first, &repeated), (&first, &from_second_source)] {
        let (a, b) = (show_elements(&a.show), show_elements(&b.show));
        assert_eq!(a.len(), B::NUM_SHOW_ELEMENTS);
        assert!(a.iter().all(|element| !b.contains(element)), "fresh shows");
    }
    assert_ne!(first.tag, to_q2.tag, "another recipient");
    assert_ne!(first.tag, from_second_source.tag, "another source");

    let (x0, x_q1, x_q2) = (
        *hvk.identifier_point(),
        pcreds.recipient_point(vk, q1.id()).expect("H_req"),
        pcreds.recipient_point(vk, q2.id()).expect("H_req"),
    );
    assert!(x_q1 != x0 && x_q2 != x0 && x_q1 != x_q2);
    let source_key = dep.members[0].user.expose_key();
    assert_eq!(params.tag.eval(source_key, &x_q1), Some(first.tag));
    assert_eq!(params.tag.eval(source_key, &x_q2), Some(to_q2.tag));
    for attestation in [&first, &to_q2, &from_second_source] {
        for member in &dep.members {
            assert_ne!(attestation.tag, *member.user.id());
        }
    }
}

every_pair!(recipient_scoped_linkability, 0x5c0d_0000);

// ---------------------------------------------------------------------------------------------
// (i) Proof-gated issuance
// ---------------------------------------------------------------------------------------------

/// Every single-field change of an attestation: the tag, every group element of the show, the
/// challenge and every response of `π_att`.
fn attestation_mutants<B: BaseTest, T: ProtocolTag<G1> + 'static>(
    attestation: &Attestation<Bk<B, T>>,
) -> Vec<Attestation<Bk<B, T>>> {
    let g = G1::generator();
    let mut mutants = vec![Attestation {
        tag: attestation.tag + g,
        ..attestation.clone()
    }];
    for show in B::show_variants(&attestation.show, g) {
        mutants.push(Attestation {
            show,
            ..attestation.clone()
        });
    }
    let mut changed = attestation.clone();
    changed.proof.challenge += Fr::one();
    mutants.push(changed);
    for r in 0..attestation.proof.responses.len() {
        let mut changed = attestation.clone();
        changed.proof.responses[r] += Fr::one();
        mutants.push(changed);
    }
    mutants
}

/// "Issuance runs on the evaluated request": every single-field change of a valid credential
/// request (`id_Q`; each attestation's tag, show elements, challenge and responses; `Ĉ`; the
/// challenge and responses of `π_iss`; the order and the number of the attestations) is refused
/// by `evaluate_request`, so `respond` is never reached and nothing is recorded. The number of
/// mutants is asserted against its formula, so the loop cannot silently shrink. A cheating
/// requester that re-proves `π_iss` over a list with a changed attestation gets its request
/// evaluated, but the changed attestation does not count (`|N''| = k − 1`), and the reply is
/// `Fail`. The unchanged request is then issued.
fn proof_gated_issuance<B: Algebra, T: Forge>(label: &[u8], seed: u64) {
    const K: usize = 2;
    let mut dep = Deployment::<B, T>::new(label, K, seed);
    let requester = dep.register();
    let attestations = dep.attestations(&requester);
    let ssid = dep.ssid();
    let (message, state) = dep
        .pcreds
        .request_credential(&dep.hvk, &requester, attestations, &ssid, &mut dep.rng)
        .expect("request");
    let evaluated = dep
        .pcreds
        .evaluate_request(&dep.helper, &message, &ssid)
        .expect("control");
    assert!(evaluated.is_valid());
    assert_eq!(evaluated.tags().len(), K);

    let g = G1::generator();
    let mut mutants = vec![CredentialRequest {
        id: message.id + g,
        ..message.clone()
    }];
    for j in 0..K {
        for changed in attestation_mutants(&message.attestations[j]) {
            let mut mutant = message.clone();
            mutant.attestations[j] = changed;
            mutants.push(mutant);
        }
    }
    let mut mutant = message.clone();
    mutant.request = G1Request(message.request.0 + g);
    mutants.push(mutant);
    let mut mutant = message.clone();
    mutant.proof.challenge += Fr::one();
    mutants.push(mutant);
    for r in 0..message.proof.responses.len() {
        let mut mutant = message.clone();
        mutant.proof.responses[r] += Fr::one();
        mutants.push(mutant);
    }
    let mut mutant = message.clone();
    mutant.attestations.swap(0, 1);
    mutants.push(mutant);
    let mut mutant = message.clone();
    mutant.attestations.pop();
    mutants.push(mutant);
    let mut mutant = message.clone();
    mutant
        .attestations
        .push(message.attestations[K - 1].clone());
    mutants.push(mutant);

    let per_attestation = 1 + B::NUM_SHOW_ELEMENTS + 1 + (1 + B::POSSESSION_VARIABLES);
    let expected = 1 + K * per_attestation + 1 + 1 + (1 + B::ISSUANCE_VARIABLES) + 3;
    assert_eq!(mutants.len(), expected, "the mutation loop must not shrink");
    for (n, mutant) in mutants.iter().enumerate() {
        // `att⃗` is part of the context of `π_iss`, so an added attestation breaks the proof too
        // (there is no limit on the number of attestations by default).
        let expected = Error::InvalidProof;
        assert_eq!(
            dep.pcreds
                .evaluate_request(&dep.helper, mutant, &ssid)
                .err(),
            Some(expected),
            "mutant {n}"
        );
    }
    assert_eq!(
        dep.helper.store().len(),
        K,
        "only the root members were issued to"
    );

    let mut cheats = Vec::new();
    for j in 0..K {
        for changed in attestation_mutants(&message.attestations[j]) {
            let mut list = message.attestations.clone();
            list[j] = changed;
            cheats.push(list);
        }
    }
    assert_eq!(cheats.len(), K * per_attestation);
    for list in cheats {
        let cheat_ssid = dep.ssid();
        let (cheat, _) = dep
            .pcreds
            .request_credential(&dep.hvk, &requester, list, &cheat_ssid, &mut dep.rng)
            .expect("request");
        let evaluated = dep
            .pcreds
            .evaluate_request(&dep.helper, &cheat, &cheat_ssid)
            .expect("a fresh π_iss over the changed list");
        assert_eq!(evaluated.tags().len(), K - 1);
        assert!(!evaluated.is_valid());
        assert_eq!(
            dep.pcreds
                .respond(&mut dep.helper, evaluated, Decision::Policy, &mut dep.rng)
                .expect("respond"),
            Reply::Fail
        );
    }
    assert_eq!(dep.helper.store().len(), K);

    let outcome = dep
        .answer(&requester, &message, state, &ssid, Decision::Policy)
        .expect("issuance");
    assert!(
        dep.pcreds
            .verify_credential(&dep.hvk, &requester, &outcome.credential())
    );
    assert_eq!(dep.helper.store().len(), K + 1);
}

every_pair!(proof_gated_issuance, 0x5c0e_0000);

// ---------------------------------------------------------------------------------------------
// (j) Attack A7: the helper tries to identify the source of a show from its issuance records
// ---------------------------------------------------------------------------------------------

/// A helper whose issuing key the harness chose: restored from the encoding
/// `pp-digest ‖ vk ‖ sk` (`sk = x` for both bases; `Σ-PS` keeps only `x`), under `Pol_1`.
fn helper_with_key<B: Algebra, T: Forge>(
    pcreds: &Protocol<Bk<B, T>>,
    vk: &B::VerificationKey,
    x: Fr,
) -> Helper<Bk<B, T>> {
    let mut bytes = Vec::new();
    pcreds
        .parameters_digest()
        .serialize_compressed(&mut bytes)
        .expect("digest");
    vk.serialize_compressed(&mut bytes).expect("vk");
    x.serialize_compressed(&mut bytes).expect("sk");
    pcreds
        .restore_helper(
            &bytes,
            Policy::threshold(1).expect("k ≥ 1"),
            IssuanceRecord::new(),
        )
        .expect("a key pair of this deployment")
}

/// A root user the helper admitted: the user, its credential and `τ`, and what the helper saw
/// and returned, the request `Ĉ` and the pre-credential.
struct Issued<B: Base<E>, T: ProtocolTag<G1> + 'static> {
    user: User<Bk<B, T>>,
    cred: Credential<Bk<B, T>>,
    tau: Fr,
    request: G1Request<E>,
    pre: B::PreCredential,
}

/// `n` root admissions (`d = root` on ordinary requests) through the protocol.
fn issue_roots<B: Algebra, T: Forge>(
    pcreds: &Protocol<Bk<B, T>>,
    helper: &mut Helper<Bk<B, T>>,
    hvk: &HelperKey<Bk<B, T>>,
    n: usize,
    rng: &mut StdRng,
) -> Vec<Issued<B, T>> {
    (0..n)
        .map(|i| {
            let user = pcreds.register(hvk, rng).expect("Register");
            let ssid = format!("root-{i}").into_bytes();
            let (message, state) = pcreds
                .request_credential(hvk, &user, Vec::new(), &ssid, rng)
                .expect("request");
            let evaluated = pcreds
                .evaluate_request(helper, &message, &ssid)
                .expect("π_iss");
            let reply = pcreds
                .respond(helper, evaluated, Decision::Root, rng)
                .expect("respond");
            let Reply::PreCredential(pre) = reply else {
                panic!("a root admission issues");
            };
            let tau = *state.expose_tape();
            let cred = pcreds.unblind(hvk, &user, &pre, state).expect("Unblind");
            Issued {
                user,
                cred,
                tau,
                request: message.request,
                pre,
            }
        })
        .collect()
}

/// `AttestationRequest` and `AttestationRequestResponse` through the protocol from the issued
/// user `source` to `recipient`, checked.
fn attest_through_protocol<B: Algebra, T: Forge>(
    pcreds: &Protocol<Bk<B, T>>,
    hvk: &HelperKey<Bk<B, T>>,
    source: &Issued<B, T>,
    recipient: &User<Bk<B, T>>,
    ssid: &[u8],
    rng: &mut StdRng,
) -> Attestation<Bk<B, T>> {
    let contact = b"source@example";
    let request = pcreds
        .request_attestation(hvk, recipient, ssid, contact, rng)
        .expect("π_id");
    let pending = pcreds
        .receive_attestation_request(hvk, &request, ssid, contact)
        .expect("π_id verifies");
    let attestation = pcreds
        .attest(hvk, &source.user, &source.cred, pending, rng)
        .expect("attest");
    assert_eq!(
        pcreds.check_attestation(hvk, recipient.id(), &attestation),
        Ok(())
    );
    attestation
}

/// The shows that reach the helper from the `sources` (indices into `issued`): for each source,
/// attestations for two recipients and a membership proof, all made by the protocol and checked
/// by its verifiers. Returned with the index of their source.
fn honest_shows<B: Algebra, T: Forge>(
    pcreds: &Protocol<Bk<B, T>>,
    hvk: &HelperKey<Bk<B, T>>,
    issued: &[Issued<B, T>],
    sources: &[usize],
    rng: &mut StdRng,
) -> Vec<(usize, B::Show)> {
    let recipients = [
        pcreds.register(hvk, rng).expect("Register"),
        pcreds.register(hvk, rng).expect("Register"),
    ];
    let message = b"anonymous post";
    let mut shows = Vec::new();
    for &p in sources {
        let source = &issued[p];
        for (j, recipient) in recipients.iter().enumerate() {
            let ssid = format!("a7-{p}-{j}").into_bytes();
            let attestation = attest_through_protocol(pcreds, hvk, source, recipient, &ssid, rng);
            shows.push((p, attestation.show));
        }
        let proof = pcreds
            .prove(hvk, &source.user, &source.cred, message, rng)
            .expect("Prove");
        assert_eq!(pcreds.check_membership(hvk, message, &proof), Ok(()));
        shows.push((p, proof.show));
    }
    shows
}

/// The helper's scalars for one record, for the two-term tests: `±1`, and `±k`, `±k⁻¹` for every
/// named `k`.
fn helper_scalars(named: &[(&str, Fr)]) -> Vec<(String, Fr)> {
    let mut scalars = vec![("1".to_owned(), Fr::one()), ("−1".to_owned(), -Fr::one())];
    for (name, k) in named {
        scalars.push(((*name).to_owned(), *k));
        scalars.push((format!("−{name}"), -*k));
        if let Some(inverse) = k.inverse() {
            scalars.push((format!("{name}⁻¹"), inverse));
            scalars.push((format!("−{name}⁻¹"), -inverse));
        }
    }
    scalars
}

/// Every two-term test `S = k·R` for `R` in `show`, `S` in `others` other than `R`, and `k` in
/// `scalars`, named `"S = k·R"`.
fn two_term_tests(
    show: &[(&str, G1)],
    others: &[(&str, G1)],
    scalars: &[(String, Fr)],
    tests: &mut Vec<(String, bool)>,
) {
    for (r_name, r) in show {
        for (k_name, k) in scalars {
            let kr = *r * k;
            for (s_name, s) in others {
                if s_name != r_name {
                    tests.push((format!("{s_name} = {k_name}·{r_name}"), kr == *s));
                }
            }
        }
    }
}

/// What the helper keeps of a `Σ-BBS` issuance it answered: the request `C` and the
/// pre-credential `(A, e)`, `A = C^{1/(x+e)}`.
struct BbsRecord {
    c: G1,
    a: G1,
    e: Fr,
}

/// The number of tests of `bbs_battery`: 2 + 3 show elements × 14 scalars × 4 other elements.
const BBS_BATTERY: usize = 2 + 3 * 14 * 4;
/// The tests of `bbs_battery` that hold for EVERY show that passes the public check, whatever
/// its source: `B̄ = Ā^x` is that check.
const BBS_ALWAYS: [&str; 2] = ["B̄ = x·Ā", "Ā = x⁻¹·B̄"];

/// The tests a `Σ-BBS` helper runs on a show `(Ā, B̄, D)` with its key `x` and ONE record
/// `(C_i, A_i, e_i)`, as `(name, fired)` (additive notation for `G_1`):
///
/// * `e(Ā, X̃·g̃^e_i) = e(D, g̃)`, the single-randomizer pairing test (review note R3), which
///   needs only the list of `e`s;
/// * `D − B̄ = e_i·Ā`, the anchor test: `(Ā, D − B̄)` is a public pair `(R, R^e)` in a
///   single-randomizer show;
/// * `S = k·R` for `R ∈ {Ā, B̄, D}`, `S` another of `{Ā, B̄, D, A_i, C_i}`, and
///   `k ∈ {±1, ±x^(±1), ±e_i^(±1), ±(x+e_i)^(±1)}`: every two-term relation with the helper's
///   scalars between the show and the recorded `A_i` and `C_i`. (With `g̃` and `X̃ = g̃^x` the
///   only `G_2` elements, every pairing test among `G_1` elements is a linear relation among
///   them with known scalars; the battery has the two-term ones.)
///
/// Why the answers do not depend on which credential was shown (Fact 2 of Lemma
/// `lem:base-bbs`, base-instantiations.tex line 259): for EVERY verifying credential the show is
/// `(U, x·U, V)` with `U, V` independent and uniform on `G_1 \ {1}`, so the `e`, `A`, `ρ` and
/// `usk` of the credential do not enter its distribution, and ANY test that is a function of the
/// show, the key and the records, in the battery or not, has the same distribution of answers
/// whichever credential was shown. For the battery: the first two tests are the event
/// `V = (x + e_i)·U`, of probability `1/(p−1)` (`x + e_i ≠ 0` by `BlindIssue`); a test `S = k·R`
/// between `V` and one of `U`, `x·U`, `A_i`, `C_i`, or between `U` (or `x·U`) and `A_i` or `C_i`,
/// is an event of probability `1/(p−1)` (`k ≠ 0`); a test between `U` and `x·U` holds iff `k = x`
/// (resp. `k = x⁻¹`), the same answer for every show that passes the public check.
fn bbs_battery(show: &BBSShow<E>, record: &BbsRecord, x: Fr, x_tilde: G2) -> Vec<(String, bool)> {
    let g2 = G2::generator();
    let mut tests = vec![
        (
            "e(Ā, X̃·g̃^e_i) = e(D, g̃)".to_owned(),
            pairing_product_is_identity::<E>(&[
                (show.a_bar, x_tilde + g2 * record.e),
                (-show.d, g2),
            ]),
        ),
        (
            "D − B̄ = e_i·Ā".to_owned(),
            show.d - show.b_bar == show.a_bar * record.e,
        ),
    ];
    let elements = [("Ā", show.a_bar), ("B̄", show.b_bar), ("D", show.d)];
    let others = [
        ("Ā", show.a_bar),
        ("B̄", show.b_bar),
        ("D", show.d),
        ("A_i", record.a),
        ("C_i", record.c),
    ];
    let scalars = helper_scalars(&[("x", x), ("e_i", record.e), ("(x+e_i)", x + record.e)]);
    two_term_tests(&elements, &others, &scalars, &mut tests);
    tests
}

/// What the helper keeps of a `Σ-PS` issuance it answered: the request `C` and the
/// pre-credential `(σ̂_1, σ̂_2) = (g_1^u, (g_1^x C)^u)`.
struct PsRecord {
    c: G1,
    pre: PSPair<E>,
}

/// The number of tests of `ps_battery`: 3 show elements × 10 scalars × 6 other elements.
const PS_BATTERY: usize = 3 * 10 * 6;

/// The tests a `Σ-PS` helper runs on a show `(σ'_1, σ'_2)` with its key `(x, y)` (a corrupted
/// helper keeps `y`) and ONE record `(C_i, σ̂_{1,i}, σ̂_{2,i})`: `S = k·R` for
/// `R ∈ {σ'_1, σ'_2, W}` with `W = σ'_2 − x·σ'_1` (`= (y·usk + t)·σ'_1`), `S` another of
/// `{σ'_1, σ'_2, W, σ̂_{1,i}, σ̂_{2,i}, C_i, Ŵ_i}` with `Ŵ_i = σ̂_{2,i} − x·σ̂_{1,i}`
/// (`= u_i·C_i`), and `k ∈ {±1, ±x^(±1), ±y^(±1)}`.
///
/// Why the answers do not depend on which credential was shown (show simulatability in Lemma
/// `lem:base-ps`, base-instantiations.tex line 136): for EVERY verifying credential and key the
/// show is uniform on `(G_1 \ {1}) × G_1`, so ANY test that is a function of the show, the key
/// and the records, in the battery or not, has the same distribution of answers whichever
/// credential was shown. For the battery: `σ'_1` is uniform on `G_1 \ {1}`, and `σ'_2`, hence
/// `W`, is uniform on `G_1` and independent of `σ'_1`, so each test is an event of probability at
/// most `1/(p−1)` (`W = 1·σ'_2` would need `x·σ'_1 = 0`, which no show has). A helper that also
/// kept its blinding exponents `u_i` learns `log σ̂_{1,i}`, which adds nothing: `σ'_1 = σ_1^r` is
/// uniform whatever `σ_1` is.
fn ps_battery(show: &PSPair<E>, record: &PsRecord, x: Fr, y: Fr) -> Vec<(String, bool)> {
    let w = show.s2 - show.s1 * x;
    let w_hat = record.pre.s2 - record.pre.s1 * x;
    let elements = [("σ'₁", show.s1), ("σ'₂", show.s2), ("W", w)];
    let others = [
        ("σ'₁", show.s1),
        ("σ'₂", show.s2),
        ("W", w),
        ("σ̂₁_i", record.pre.s1),
        ("σ̂₂_i", record.pre.s2),
        ("C_i", record.c),
        ("Ŵ_i", w_hat),
    ];
    let mut tests = Vec::with_capacity(PS_BATTERY);
    two_term_tests(
        &elements,
        &others,
        &helper_scalars(&[("x", x), ("y", y)]),
        &mut tests,
    );
    tests
}

/// For a show of the credential `source`: every test has the same answer on the record of every
/// candidate (`answers[i]` is the battery on record `i`), true for the tests in `always` and
/// false for all others.
fn assert_singles_out_nobody(answers: &[Vec<(String, bool)>], always: &[&str], source: usize) {
    for (t, (name, _)) in answers[0].iter().enumerate() {
        let expected = always.contains(&name.as_str());
        for (i, candidate) in answers.iter().enumerate() {
            assert_eq!(candidate[t].0, *name, "one battery for every candidate");
            assert_eq!(
                candidate[t].1, expected,
                "`{name}` on the record of credential {i}, for a show of credential {source}"
            );
        }
    }
}

/// For a degenerate show `what` of the credential `source`: apart from the tests in `always`, no
/// test fires on the record of any other candidate, and every test in `identifying` fires on the
/// record of `source`.
fn assert_singles_out(
    answers: &[Vec<(String, bool)>],
    source: usize,
    always: &[&str],
    identifying: &[&str],
    what: &str,
) {
    for (i, candidate) in answers.iter().enumerate() {
        for (name, fired) in candidate {
            if always.contains(&name.as_str()) {
                assert!(*fired, "{what}: `{name}` holds for every show");
            } else if i != source {
                assert!(
                    !*fired,
                    "{what}: `{name}` fired on the record of credential {i}"
                );
            }
        }
    }
    for name in identifying {
        assert!(
            answers[source]
                .iter()
                .any(|(test, fired)| test.as_str() == *name && *fired),
            "{what}: `{name}` identifies the source"
        );
    }
}

/// Attack A7 on `Σ-BBS` (review note R3, base-instantiations.tex line 232: on the reference
/// implementation, a helper holding 20 issued `e`s identified every anonymous source of the
/// earlier show shape). A helper with key `x` admits `N = 10` users and records every
/// `(C_i, A_i, e_i)`. Three of them send nine shows (two attestations and one membership proof
/// each, made and checked by the protocol). On every show, every test of `bbs_battery` gives the
/// same answer on all ten records: true for the two forms of the public check `B̄ = x·Ā`, false
/// for the rest. Probability that a false test fires on an honest show: at most `2/(p−1)` per
/// evaluation, the larger of `1/(p−1)` for an event about the show (`bbs_battery`) and `2/(p−1)`
/// for an event about `(k, x, e_i)` alone such as `x² = 1`, over the uniform `x` and `e_i`; here
/// `9 · 10 · 170 = 15300 < 2^14` evaluations and `p − 1 > 2^254` (BLS12-381), so less than
/// `2^-239` in all (computed: `log_2(2 · 15300/(p−1)) ≈ −239.96`).
///
/// Controls: the source's shows with degenerate randomizers (`r_1 = 1`, the single-randomizer
/// show the protocol box replaced; `r_2 = 1`; `r_1·r_2 = 1`; no re-randomization) pass the
/// verifier, inside an attestation and a membership proof with valid proofs, so the verifier
/// cannot enforce the randomizers; each is identified, for its source only, by the tests listed.
#[test]
fn a7_bbs_records_do_not_single_out_the_source() {
    const N: usize = 10;
    let label = b"pcreds-snd/a7/bbs";
    let mut rng = StdRng::seed_from_u64(0x5c0f_0001);
    let pcreds = Protocol::<Bk<BBS, DDH>>::setup(label).expect("Setup");
    let x = nonzero(&mut rng);
    let mut helper = helper_with_key(&pcreds, &BBSVerificationKey(G2::generator() * x), x);
    let hvk = pcreds.helper_key(helper.key().vk()).expect("hvk ∈ V_pp");
    let x_tilde = hvk.vk().0;
    let issued = issue_roots(&pcreds, &mut helper, &hvk, N, &mut rng);
    let records: Vec<BbsRecord> = issued
        .iter()
        .map(|issuance| BbsRecord {
            c: issuance.request.0,
            a: issuance.pre.a,
            e: issuance.pre.e,
        })
        .collect();
    let battery = |show: &BBSShow<E>| -> Vec<Vec<(String, bool)>> {
        records
            .iter()
            .map(|record| bbs_battery(show, record, x, x_tilde))
            .collect()
    };

    let shows = honest_shows(&pcreds, &hvk, &issued, &[0, N / 2, N - 1], &mut rng);
    assert_eq!(shows.len(), 9);
    let mut evaluations = 0;
    for (source, show) in &shows {
        let answers = battery(show);
        assert!(answers.iter().all(|tests| tests.len() == BBS_BATTERY));
        evaluations += answers.len() * BBS_BATTERY;
        assert_singles_out_nobody(&answers, &BBS_ALWAYS, *source);
    }
    assert_eq!(evaluations, 15_300);

    let source = N / 2;
    let (usk, cred) = (
        *issued[source].user.expose_key(),
        issued[source].cred.as_inner(),
    );
    let pp = &pcreds.params().base;
    let recipient = pcreds.register(&hvk, &mut rng).expect("Register");
    let r = nonzero(&mut rng);
    let controls: [(&str, Fr, Fr, &[&str]); 4] = [
        (
            "r_1 = 1",
            Fr::one(),
            r,
            &[
                "e(Ā, X̃·g̃^e_i) = e(D, g̃)",
                "D − B̄ = e_i·Ā",
                "D = (x+e_i)·Ā",
                "Ā = (x+e_i)⁻¹·D",
            ],
        ),
        ("r_2 = 1", r, Fr::one(), &["C_i = 1·D"]),
        (
            "r_1·r_2 = 1",
            r,
            r.inverse().expect("r ≠ 0"),
            &["A_i = 1·Ā", "C_i = (x+e_i)·Ā"],
        ),
        (
            "no re-randomization",
            Fr::one(),
            Fr::one(),
            &["A_i = 1·Ā", "C_i = 1·D", "D = (x+e_i)·Ā", "D − B̄ = e_i·Ā"],
        ),
    ];
    for (what, r1, r2, identifying) in controls {
        let show = bbs_rerand(pp, &usk, cred, r1, r2);
        let witness = bbs_show_witness(usk, cred, r1, r2);
        accepted_attestation(
            &pcreds,
            &hvk,
            &usk,
            &show,
            &witness,
            recipient.id(),
            &mut rng,
        );
        accepted_membership_proof(&pcreds, &hvk, &show, &witness, b"post", &mut rng);
        assert_singles_out(&battery(&show), source, &BBS_ALWAYS, identifying, what);
    }
}

/// Attack A7 on `Σ-BBS`, the reason exactly: for every show `σ*` from the source `P` and EVERY
/// issued credential `j`, the harness computes randomizers `(r_1^(j), r_2^(j)) ∈ (Z_p^*)^2` with
/// `ReRand(cred_j; r^(j)) = σ*` and checks the equality. By Fact 2 the map
/// `(r_1, r_2) ↦ ReRand(cred_j; r_1, r_2)` is a bijection from `(Z_p^*)^2` onto the shows that
/// pass the public check, so each credential produces `σ*` with the same probability
/// `1/(p−1)^2`: the helper's records, and every test on them, are equally consistent with every
/// candidate. (The bijection is the paper's argument; the test checks existence on the samples.)
///
/// To compute discrete logarithms, the deployment uses generators `h = g_1^a` with exponents the
/// harness chose (`setup_with_params`). Such parameters are insecure (whoever knows the exponents
/// shows credentials it does not have); here they are a measuring instrument and every party is
/// honest. With `c_j = a_0 + a_u·usk_j + a_r·ρ_j` (`C_j = g_1^c_j`, `A_j = g_1^(c_j/(x+e_j))`) and
/// the source's show `D = g_1^d`, `Ā = g_1^a`: `r_2^(j) = d/c_j`, `r_1^(j) = a·(x+e_j)/d`.
#[test]
fn a7_bbs_every_issued_credential_explains_every_show() {
    const N: usize = 6;
    let label = b"pcreds-snd/a7/bbs-known-exponents";
    let mut rng = StdRng::seed_from_u64(0x5c0f_0002);
    let g = G1::generator();
    let (a0, au, ar) = (nonzero(&mut rng), nonzero(&mut rng), nonzero(&mut rng));
    let params = PairingParams::<E, BBS, DDH> {
        base: BBSParams {
            h0: g * a0,
            hu: g * au,
            hr: g * ar,
        },
        tag: DDH::setup(label).expect("pp_Tag"),
    };
    let pcreds = Protocol::<Bk<BBS, DDH>>::setup_with_params(label, params).expect("Setup");
    let x = nonzero(&mut rng);
    let mut helper = helper_with_key(&pcreds, &BBSVerificationKey(G2::generator() * x), x);
    let hvk = pcreds.helper_key(helper.key().vk()).expect("hvk ∈ V_pp");
    let issued = issue_roots(&pcreds, &mut helper, &hvk, N, &mut rng);
    let pp = &pcreds.params().base;
    let log_c = |issuance: &Issued<BBS, DDH>| {
        a0 + au * issuance.user.expose_key() + ar * issuance.cred.as_inner().rho
    };
    let inverse = |value: Fr| value.inverse().expect("nonzero");
    for issuance in &issued {
        assert_eq!(issuance.cred.as_inner().rho, issuance.tau, "ρ = τ");
        assert_eq!(g * log_c(issuance), issuance.request.0, "log C");
        assert_eq!(
            g * (log_c(issuance) * inverse(x + issuance.pre.e)),
            issuance.pre.a,
            "log A"
        );
    }

    let recipient = pcreds.register(&hvk, &mut rng).expect("Register");
    let mut explained = 0;
    for p in [0, N - 1] {
        let (usk, cred) = (*issued[p].user.expose_key(), issued[p].cred.as_inner());
        for in_attestation in [true, false] {
            let (show, omega) = BBS::rerand(pp, hvk.vk(), &usk, cred, &mut rng);
            let witness = possession_witness::<BBS>(usk, cred, &omega);
            if in_attestation {
                accepted_attestation(
                    &pcreds,
                    &hvk,
                    &usk,
                    &show,
                    &witness,
                    recipient.id(),
                    &mut rng,
                );
            } else {
                accepted_membership_proof(&pcreds, &hvk, &show, &witness, b"post", &mut rng);
            }
            let (r1, r2) = (witness[2], inverse(witness[4]));
            let d = log_c(&issued[p]) * r2;
            let a = log_c(&issued[p]) * r1 * r2 * inverse(x + cred.e);
            assert_eq!((g * d, g * a), (show.d, show.a_bar));
            for (j, candidate) in issued.iter().enumerate() {
                let r2_j = d * inverse(log_c(candidate));
                let r1_j = a * (x + candidate.cred.as_inner().e) * inverse(d);
                assert!(!r1_j.is_zero() && !r2_j.is_zero());
                let rebuilt = bbs_rerand(
                    pp,
                    candidate.user.expose_key(),
                    candidate.cred.as_inner(),
                    r1_j,
                    r2_j,
                );
                assert_eq!(rebuilt, show, "credential {j} explains the show of {p}");
                if j == p {
                    assert_eq!((r1_j, r2_j), (r1, r2));
                }
                explained += 1;
            }
        }
    }
    assert_eq!(explained, 2 * 2 * N);
}

/// Attack A7 on `Σ-PS`: a helper with key `(x, y)` admits `N = 10` users and records every
/// `(C_i, σ̂_{1,i}, σ̂_{2,i})`. On the nine shows of three sources, every test of `ps_battery`
/// gives the same answer, false, on all ten records. Probability that a test fires on an honest
/// show: at most `1/(p−1)` per evaluation (`ps_battery`), `9 · 10 · 180 = 16200 < 2^14`
/// evaluations, so less than `2^-240` in all (computed: `log_2(16200/(p−1)) ≈ −240.87`).
///
/// Controls: the source's shows with `r = 1`, and with `r = 1, t = τ` (which is the
/// pre-credential `σ̂` itself), pass the verifier inside an attestation and a membership proof
/// and are identified, for their source only.
#[test]
fn a7_ps_records_do_not_single_out_the_source() {
    const N: usize = 10;
    let label = b"pcreds-snd/a7/ps";
    let mut rng = StdRng::seed_from_u64(0x5c0f_0003);
    let pcreds = Protocol::<Bk<PS, DDH>>::setup(label).expect("Setup");
    let (x, y) = (nonzero(&mut rng), nonzero(&mut rng));
    let g2 = G2::generator();
    let vk = PSVerificationKey::<E> {
        x2: g2 * x,
        y2: g2 * y,
        y1: G1::generator() * y,
    };
    let mut helper = helper_with_key(&pcreds, &vk, x);
    let hvk = pcreds.helper_key(helper.key().vk()).expect("hvk ∈ V_pp");
    let issued = issue_roots(&pcreds, &mut helper, &hvk, N, &mut rng);
    let records: Vec<PsRecord> = issued
        .iter()
        .map(|issuance| PsRecord {
            c: issuance.request.0,
            pre: issuance.pre.clone(),
        })
        .collect();
    let battery = |show: &PSPair<E>| -> Vec<Vec<(String, bool)>> {
        records
            .iter()
            .map(|record| ps_battery(show, record, x, y))
            .collect()
    };

    let shows = honest_shows(&pcreds, &hvk, &issued, &[0, N / 2, N - 1], &mut rng);
    assert_eq!(shows.len(), 9);
    let mut evaluations = 0;
    for (source, show) in &shows {
        let answers = battery(show);
        assert!(answers.iter().all(|tests| tests.len() == PS_BATTERY));
        evaluations += answers.len() * PS_BATTERY;
        assert_singles_out_nobody(&answers, &[], *source);
    }
    assert_eq!(evaluations, 16_200);

    let source = N / 2;
    let holder = &issued[source];
    let (usk, cred) = (*holder.user.expose_key(), holder.cred.as_inner());
    let recipient = pcreds.register(&hvk, &mut rng).expect("Register");
    let controls: [(&str, Fr, &[&str]); 2] = [
        ("r = 1", Fr::rand(&mut rng), &["σ̂₁_i = 1·σ'₁"]),
        (
            "r = 1, t = τ",
            holder.tau,
            &["σ̂₁_i = 1·σ'₁", "σ̂₂_i = 1·σ'₂", "Ŵ_i = 1·W"],
        ),
    ];
    for (what, t, identifying) in controls {
        let show = ps_rerand(cred, Fr::one(), t);
        if t == holder.tau {
            assert_eq!(show, holder.pre, "the pre-credential is a valid show");
        }
        let witness = [usk, t];
        accepted_attestation(
            &pcreds,
            &hvk,
            &usk,
            &show,
            &witness,
            recipient.id(),
            &mut rng,
        );
        accepted_membership_proof(&pcreds, &hvk, &show, &witness, b"post", &mut rng);
        assert_singles_out(&battery(&show), source, &[], identifying, what);
    }
}
