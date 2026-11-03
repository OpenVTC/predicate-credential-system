//! The attack lab: experiments run live on request, each from the state of step 9 (bob
//! admitted on carol's and alice's attestations) of the same seed, so that the values match the
//! walkthrough's.
//!
//! An experiment reports what the code returned, verbatim. Where an attack needs a secret (a
//! vetter forging with her own key), the experiment reads it through the engines' demo hooks.

use ark_bls12_381::{Fq, G1Affine};
use ark_ec::{AffineRepr, CurveConfig};
use ark_ff::Zero;
use chrono::NaiveDate;
use pcs_vetting_prototype::{
    applicant::ApplicantEngine,
    meta::{ProofContext, id_binding},
    scheme::{Base, Fr, G1, Open, hidden_vetting_predicate, point_text},
    trace,
    vetter::VetterEngine,
    vtc::Submission,
};
use predicate_credential_system::{
    cred::{CredentialBase, SigmaFriendlyCredentialBase},
    kiprf::KIPRF,
    pcs::{Attestation, UserSecretKey},
    sigma::{FSProof, LinearRelation, PairingRelation, commit, fiat_shamir, respond},
};
use rand::{SeedableRng, rngs::StdRng};
use serde_json::{Value as J, json};
use vta_sdk::protocols::vetting::VettingMethod;

use crate::{
    model::{Check, Fig, Run, Stage, Val, line, line_ok},
    scenario::{self, PERIOD, R, World, vet, vtc_submit},
};

pub struct Info {
    pub id: &'static str,
    /// `attack` (the code must refuse), `defence` (a mechanism at work), `limit` (accepted: the
    /// cryptography does not prevent it).
    pub kind: &'static str,
    pub title: &'static str,
    pub threat: &'static str,
    /// The stage it belongs with.
    pub stage: &'static str,
}

pub const LAB: &[Info] = &[
    Info {
        id: "tamper",
        kind: "attack",
        title: "Edit a statement after it was signed",
        threat: "bob, or anyone on the path, edits carol's statement metadata, e.g. from video to in person.",
        stage: "receive",
    },
    Info {
        id: "same-vetter",
        kind: "attack",
        title: "Count one vetter twice",
        threat: "bob asks carol for a second attestation and presents both as two vetters.",
        stage: "prove-k2",
    },
    Info {
        id: "replay",
        kind: "attack",
        title: "Replay or transplant a proof",
        threat: "An observer resubmits bob's proof, or reuses it for another join DID.",
        stage: "prove-k1",
    },
    Info {
        id: "steal",
        kind: "attack",
        title: "Use another applicant's attestations",
        threat: "frank presents, as his own, the attestations bob received.",
        stage: "receive",
    },
    Info {
        id: "cofactor",
        kind: "attack",
        title: "Shift a tag by a point of order 3",
        threat: "alice attests for bob twice, once with $T + P_3$, so that one vetter passes as two.",
        stage: "prove-k2",
    },
    Info {
        id: "twin-key",
        kind: "attack",
        title: "Enrol a second key",
        threat: "alice enrols a second key to get a second tag for every applicant.",
        stage: "vetter-key",
    },
    Info {
        id: "capacity",
        kind: "defence",
        title: "Run out of tokens",
        threat: "A vetter accepts more requests than her tokens allow, and asks for an extra drip.",
        stage: "tokens",
    },
    Info {
        id: "rotation",
        kind: "defence",
        title: "Rotate the period, then drop the old one",
        threat: "The VTC moves to 2026-10, and then removes 2026-09 in an emergency.",
        stage: "setup",
    },
    Info {
        id: "self-vetting",
        kind: "limit",
        title: "Vouch for your own second persona",
        threat: "alice opens a fresh application of her own and vets it herself.",
        stage: "summary",
    },
];

/// The options of the `tamper` experiment.
pub const TAMPER_FIELDS: &[(&str, &str)] = &[
    ("method", "method: video → inPerson"),
    ("claims", "claimsVerified: add address"),
    ("validUntil", "validUntil: one year later"),
    ("serial", "tokenSerial: alice's serial"),
    ("community", "community: another VTC"),
];

pub fn catalog() -> J {
    J::Array(
        LAB.iter()
            .map(|i| {
                let mut j = json!({ "id": i.id, "kind": i.kind, "title": i.title, "threat": i.threat, "stage": i.stage });
                if i.id == "tamper" {
                    j["params"] = json!(TAMPER_FIELDS.iter().map(|(v, l)| json!({ "value": v, "label": l })).collect::<Vec<_>>());
                }
                j
            })
            .collect(),
    )
}

/// Run experiment `id` for `seed`. `nonce` reseeds the randomness the experiment itself draws,
/// so "run again" gives fresh forgeries.
pub fn run(id: &str, seed: u64, param: Option<&str>, nonce: u64) -> Result<J, String> {
    let info = LAB
        .iter()
        .find(|i| i.id == id)
        .ok_or("unknown experiment")?;
    let (mut run, mut w) = scenario::admitted(seed).map_err(|e| e.to_string())?;
    if nonce != 0 {
        w.rng = StdRng::seed_from_u64(seed ^ nonce.rotate_left(17) ^ 0x6c61_625f_6e6f_6e63);
    }
    let (out, calls) = trace::record(|| match id {
        "tamper" => tamper(&mut run, &mut w, param.unwrap_or("method")),
        "same-vetter" => same_vetter(&mut run, &mut w),
        "replay" => replay(&mut run, &mut w),
        "steal" => steal(&mut run, &mut w),
        "cofactor" => cofactor(&mut run, &mut w),
        "twin-key" => twin_key(&mut run, &mut w),
        "capacity" => capacity(&mut run, &mut w),
        "rotation" => rotation(&mut run, &mut w),
        "self-vetting" => self_vetting(&mut run, &mut w),
        _ => Err("unknown experiment".into()),
    });
    let (mut stage, verdict) = out.map_err(|e| e.to_string())?;
    stage.calls(calls);
    Ok(json!({
        "id": info.id, "kind": info.kind, "title": info.title, "threat": info.threat,
        "verdict": verdict, "stage": stage.to_json(), "values": run.values(),
    }))
}

type Out = R<(Stage, J)>;

fn verdict(tone: &str, text: &str) -> J {
    json!({ "tone": tone, "text": text })
}

fn shown<T, E: std::fmt::Display>(r: &Result<T, E>) -> String {
    match r {
        Ok(_) => "Ok".to_string(),
        Err(e) => format!("Err({e})"),
    }
}

fn new_stage(id: &str, title: &str, who: &str, lede: &str) -> Stage {
    Stage::new(id, "Lab", title, who, lede)
}

/// A proof context `app_0` for bob's join DID under `challenge`.
fn app0(w: &World, id: &G1, join_did: &str, challenge: &str) -> R<Vec<u8>> {
    let id_text = point_text(id)?;
    Ok(ProofContext {
        challenge: challenge.to_string(),
        audience: w.vtc.audience().to_string(),
        join_did: join_did.to_string(),
        id_binding: id_binding(
            &id_text,
            &w.vtc.community,
            w.vtc.requirements_digest(),
            join_did,
        ),
    }
    .context_bytes()?)
}

fn index_of(sub: &Submission, tag: &G1) -> R<usize> {
    Ok(sub
        .proof
        .attestations
        .iter()
        .position(|a| a.tag == *tag)
        .ok_or("tag not in the submission")?)
}

// ---------------------------------------------------------------------------------------------

fn tamper(run: &mut Run, w: &mut World, field: &str) -> Out {
    let hvk = w.vtc.hvk().clone();
    let bob_id = *w.bob.id();
    let s_b = w.vtc.open().tag_point(&bob_id)?;
    let att = w.a_carol.attestation.clone();
    let honest = w.a_carol.meta.clone();
    let mut edited = honest.clone();
    let (name, before, after) = match field {
        "claims" => {
            edited.claims_verified.push("address".into());
            (
                "claimsVerified",
                honest.claims_verified.join(", "),
                edited.claims_verified.join(", "),
            )
        }
        "validUntil" => {
            edited.valid_until = NaiveDate::from_ymd_opt(2028, 1, 18).ok_or("date")?;
            (
                "validUntil",
                honest.valid_until.to_string(),
                edited.valid_until.to_string(),
            )
        }
        "serial" => {
            edited.token_serial = w.a_alice.meta.token_serial.clone();
            (
                "tokenSerial",
                honest.token_serial.clone(),
                edited.token_serial.clone(),
            )
        }
        "community" => {
            edited.community = "did:example:another-vtc".into();
            (
                "community",
                honest.community.clone(),
                edited.community.clone(),
            )
        }
        _ => {
            edited.method = VettingMethod::InPerson;
            (
                "method",
                honest.method.to_string(),
                edited.method.to_string(),
            )
        }
    };
    let app = honest.context_bytes()?;
    let app2 = edited.context_bytes()?;
    let rel = w
        .vtc
        .open()
        .attestation_relation(&hvk, &att.shown, &att.phi, &att.tag, &s_b)?;
    let a = rel.recompute_commitment(&att.proof.challenge, &att.proof.responses)?;
    let ctx = w.vtc.open().attestation_context_with_app(
        &hvk,
        &bob_id,
        &att.phi,
        &att.tag,
        &att.shown,
        Some(app.as_slice()),
    )?;
    let ctx2 = w.vtc.open().attestation_context_with_app(
        &hvk,
        &bob_id,
        &att.phi,
        &att.tag,
        &att.shown,
        Some(app2.as_slice()),
    )?;
    let c1 = fiat_shamir::challenge(&rel, &ctx, &a)?;
    let c2 = fiat_shamir::challenge(&rel, &ctx2, &a)?;
    run.val(Val::bytes("lab.ctx", r"\ctx_1", &ctx));
    run.val(
        Val::bytes("lab.ctx2", r"\ctx_1^{\mathrm{edit}}", &ctx2)
            .note("$ctx_1$ with the edited $app_1$."),
    );
    run.val(Val::fr("lab.c1", r"c'", &c1));
    run.val(Val::fr("lab.c2", r"c''", &c2));
    let verify_edit = trace::span(
        "bob",
        "PCS::check_attestation_in_context",
        "VerifyAtt under the edited app_1",
        || {
            w.vtc
                .open()
                .check_attestation_in_context(&hvk, &bob_id, &att, &app2)
        },
    );
    // The VTC: bob's k = 2 proof, with the edited metadata beside carol's attestation.
    let mut sub = w.sub2.clone();
    let j = index_of(&sub, &att.tag)?;
    sub.statements[j].0 = edited.clone();
    sub.challenge = w.vtc.challenge(&mut w.rng);
    let at_vtc = vtc_submit(&mut w.vtc, &sub);

    let mut s = new_stage(
        "lab-tamper",
        "Edit a statement after it was signed",
        "bob → VTC, with carol's metadata edited",
        "carol's attestation is bound to its metadata through $\\ctx_1$, which is hashed into \
         the challenge of $\\pi_1$. Edit one field and the verifier recomputes a different \
         challenge.",
    );
    s.kv(
        "The edit",
        vec![
            ("field", name.to_string()),
            ("signed", before),
            ("presented", after),
        ],
    );
    s.derive(
        "What the verifier recomputes",
        "The commitment $A'$ depends only on the proof and the statement (with $Y_T = e(\\sigma'_2, \\tilde g)\\, e(\\sigma'_1, \\tilde X \\tilde Y_2^{\\varphi_v})^{-1}$, the target of the pairing clause), so it is the same in both lines; the challenge hashes it together with the context.",
        vec![
            line(r"A' := \bigl(e(\sigma'_1, \tilde Y_1)^{z} \cdot Y_T^{-c},\ H_2(s_B)^{z} \cdot T_1^{-c}\bigr)", &[]),
            line_ok(r"H_1(\V{lab.ctx}{\ctx_1}, \text{statement}, A') = \V{lab.c1}{c'} \overset{?}{=} \V{carol.pi.c}{c}", &["lab.ctx", "lab.c1", "carol.pi.c"], c1 == att.proof.challenge, "the metadata carol signed: the challenge matches"),
            line_ok(r"H_1(\V{lab.ctx2}{\ctx_1^{\mathrm{edit}}}, \text{statement}, A') = \V{lab.c2}{c''} \overset{?}{=} \V{carol.pi.c}{c}", &["lab.ctx2", "lab.c2", "carol.pi.c"], c2 == att.proof.challenge, "the edited metadata: a different challenge, so $\\pi_1$ fails"),
        ],
    );
    s.checks(
        "What the code returned",
        vec![
            Check::new(verify_edit.is_err(), "bob's engine rejects the edited statement on receipt").observed(shown(&verify_edit)).by("bob's engine"),
            Check::new(at_vtc.is_err(), "the VTC rejects the whole proof: the attestation does not verify under the context it rebuilds").observed(shown(&at_vtc)).by("VTC"),
        ],
    );
    s.p("The token serial is part of $app_1$ too: a token cannot be moved from one attestation to another.");
    let blocked = verify_edit.is_err() && at_vtc.is_err();
    Ok((
        s,
        verdict(
            if blocked { "blocked" } else { "accepted" },
            if blocked {
                "Rejected: $\\pi_1$ does not verify under the edited context."
            } else {
                "Accepted: this should not happen."
            },
        ),
    ))
}

fn same_vetter(run: &mut Run, w: &mut World) -> Out {
    let hvk = w.vtc.hvk().clone();
    let bob_id = *w.bob.id();
    let a2 = vet(
        &w.vtc,
        &mut w.vetters[1],
        &w.bob,
        VettingMethod::InPerson,
        &mut w.rng,
    )?;
    let a1 = w.a_carol.clone();
    run.val(
        Val::g1("lab.T1b", r"T_1'", &a2.attestation.tag)
            .note("carol's tag in her second attestation for bob."),
    );
    run.val(Val::g1(
        "lab.sh1b",
        r"\sigma''_1",
        &a2.attestation.shown.sigma_1,
    ));
    // bob's own engine would keep one per tag; bob builds the proof by hand instead.
    let usk = UserSecretKey::from_scalar(*w.bob.usk_scalar());
    let c = w.vtc.challenge(&mut w.rng);
    let app0 = app0(w, &bob_id, &w.bob.join_did, &c)?;
    let apps = [a1.meta.context_bytes()?, a2.meta.context_bytes()?];
    let app_refs: Vec<&[u8]> = apps.iter().map(Vec::as_slice).collect();
    let f2 = hidden_vetting_predicate(2);
    let atts = [a1.attestation.clone(), a2.attestation.clone()];
    let prove = trace::span(
        "bob",
        "PCS::prove_in_context",
        "Prove with two attestations from carol",
        || {
            w.vtc.open().prove_in_context(
                &hvk, &f2, &bob_id, &usk, &atts, &app_refs, &app0, &mut w.rng,
            )
        },
    );
    // Spliced by hand into bob's real k = 2 proof, in place of alice's attestation.
    let mut sub = w.sub2.clone();
    let j = index_of(&sub, &w.a_alice.attestation.tag)?;
    sub.proof.attestations[j] = a2.attestation.clone();
    sub.statements[j] = (a2.meta.clone(), a2.token.clone());
    sub.challenge = w.vtc.challenge(&mut w.rng);
    let at_vtc = vtc_submit(&mut w.vtc, &sub);

    let mut s = new_stage(
        "lab-same-vetter",
        "Count one vetter twice",
        "carol → bob → VTC",
        "carol attests for bob a second time, in person. The two attestations look \
         unrelated: fresh randomisation, fresh proof, a different token. But the tag is a \
         deterministic function of carol's key and bob's point.",
    );
    s.fig(
        Fig::new(&["carol", "bob", "vtc"], "Two attestations from one vetter.")
            .send("carol", "bob", r"att_1 = (\V{carol.T}{T_1}, \cred^*_1, \varphi_v, \pi_1) \quad \text{(video)}", &["carol.T"], None)
            .send("carol", "bob", r"att'_1 = (\V{lab.T1b}{T'_1}, \cred^{*\prime}_1, \varphi_v, \pi'_1) \quad \text{(in person)}", &["lab.T1b"], None)
            .check("bob", r"\mathsf{Prove}(f_2, (att_1, att'_1))", prove.is_ok(), "refused by bob's own prover")
            .send("bob", "vtc", r"\pi \text{ with } att_1, att'_1 \text{ spliced in by hand}", &[], None)
            .check("vtc", r"|\{T_1, T'_1\}| = 2", at_vtc.is_ok(), "$\\CheckAtts$ refuses: two attestations carry the same tag"),
    );
    s.checks(
        "What the code returned",
        vec![
            Check::new(
                a1.attestation.tag == a2.attestation.tag,
                "the tags are equal",
            )
            .tex(r"\V{carol.T}{T_1} = \V{lab.T1b}{T'_1}")
            .by("anyone"),
            Check::new(
                a1.attestation.shown != a2.attestation.shown,
                "the shown credentials differ: unlinkable as credentials",
            )
            .tex(r"\cred^*_1 \ne \cred^{*\prime}_1")
            .by("anyone"),
            Check::new(prove.is_err(), "bob's prover refuses")
                .observed(shown(&prove))
                .by("bob's engine"),
            Check::new(at_vtc.is_err(), "the VTC refuses the spliced proof")
                .observed(shown(&at_vtc))
                .by("VTC"),
        ],
    );
    s.p("Key injectivity runs the other way: two *different* vetters can never collide on a tag, since $H_2(s_B)$ has prime order. Equal tags mean one vetter; distinct tags mean distinct vetters.");
    let blocked = prove.is_err() && at_vtc.is_err();
    Ok((
        s,
        verdict(
            if blocked { "blocked" } else { "accepted" },
            "Rejected: two attestations carry the same tag.",
        ),
    ))
}

fn replay(run: &mut Run, w: &mut World) -> Out {
    let _ = run;
    let r1 = vtc_submit(&mut w.vtc, &w.sub2);
    let mut s2 = w.sub2.clone();
    s2.challenge = w.vtc.challenge(&mut w.rng);
    let r2 = vtc_submit(&mut w.vtc, &s2);
    let mut s3 = w.sub2.clone();
    s3.challenge = w.vtc.challenge(&mut w.rng);
    s3.join_did = "did:example:mallory".into();
    let r3 = vtc_submit(&mut w.vtc, &s3);

    let mut s = new_stage(
        "lab-replay",
        "Replay or transplant a proof",
        "mallory → VTC, with bob's proof",
        "mallory has a copy of bob's admitted submission. She resubmits it, then asks for a \
         fresh challenge, then tries it for her own join DID.",
    );
    s.fig(
        Fig::new(
            &["mallory", "vtc"],
            "Three replays of bob's $k = 2$ submission.",
        )
        .send(
            "mallory",
            "vtc",
            r"\text{bob's submission, unchanged}",
            &["sub2.challenge"],
            None,
        )
        .check(
            "vtc",
            r"\mathsf{challenge} \text{ known and unused}",
            r1.is_ok(),
            "the challenge was consumed when bob submitted",
        )
        .send("vtc", "mallory", r"\mathsf{challenge}'", &[], Some(16))
        .send(
            "mallory",
            "vtc",
            r"\text{bob's } \pi \text{ under } \mathsf{challenge}'",
            &[],
            None,
        )
        .check(
            "vtc",
            r"\VerifyFS(\ctx_0', \pi_0) = 1",
            r2.is_ok(),
            "$app_0$ contains the challenge, so $\\ctx_0$ changed and $\\pi_0$ fails",
        )
        .send(
            "mallory",
            "vtc",
            r"\text{bob's } \pi \text{ for } \mathsf{joinDid} = \texttt{did:example:mallory}",
            &[],
            None,
        )
        .check(
            "vtc",
            r"\VerifyFS(\ctx_0'', \pi_0) = 1",
            r3.is_ok(),
            "$app_0$ binds the join DID through $idBinding$",
        ),
    );
    s.checks(
        "What the code returned",
        vec![
            Check::new(
                r1.is_err(),
                "the replay is refused before any cryptography: the challenge is single use",
            )
            .observed(shown(&r1))
            .by("VTC"),
            Check::new(
                r2.is_err(),
                "a fresh challenge does not help: the proof is bound to the old one",
            )
            .observed(shown(&r2))
            .by("VTC"),
            Check::new(
                r3.is_err(),
                "another join DID does not help: the proof is bound to bob's",
            )
            .observed(shown(&r3))
            .by("VTC"),
        ],
    );
    s.p("The attestations themselves are *standing* endorsements: they carry no challenge, and bob may present them again under a fresh one. What cannot be reused is $\\pi_0$, which only the holder of $usk_B$ can produce.");
    let blocked = r1.is_err() && r2.is_err() && r3.is_err();
    Ok((
        s,
        verdict(
            if blocked { "blocked" } else { "accepted" },
            "Rejected all three: the challenge is single use, and $\\pi_0$ is bound to it and to the join DID.",
        ),
    ))
}

fn steal(run: &mut Run, w: &mut World) -> Out {
    let hvk = w.vtc.hvk().clone();
    let mut frank = ApplicantEngine::new(&w.vtc, "did:example:frank", &mut w.rng)?;
    let frank_id = *frank.id();
    let s_f = w.vtc.open().tag_point(&frank_id)?;
    run.val(Val::g1("lab.frank.id", "id_F", &frank_id).who(&["frank", "vtc"]));
    run.val(Val::fr("lab.frank.s", "s_F", &s_f).who(&["public"]));
    let received = frank.receive(&w.vtc, w.a_carol.clone());
    // frank proves with bob's two attestations, by hand.
    let usk = UserSecretKey::from_scalar(*frank.usk_scalar());
    let c = w.vtc.challenge(&mut w.rng);
    let app0 = app0(w, &frank_id, "did:example:frank", &c)?;
    let apps = [
        w.a_carol.meta.context_bytes()?,
        w.a_alice.meta.context_bytes()?,
    ];
    let app_refs: Vec<&[u8]> = apps.iter().map(Vec::as_slice).collect();
    let atts = [w.a_carol.attestation.clone(), w.a_alice.attestation.clone()];
    let prove = trace::span(
        "frank",
        "PCS::prove_in_context",
        "Prove with bob's attestations",
        || {
            w.vtc.open().prove_in_context(
                &hvk,
                &hidden_vetting_predicate(2),
                &frank_id,
                &usk,
                &atts,
                &app_refs,
                &app0,
                &mut w.rng,
            )
        },
    );
    // Or bob's whole proof, with frank's identifier on it.
    let mut sub = w.sub2.clone();
    sub.id = frank_id;
    sub.join_did = "did:example:frank".into();
    sub.challenge = w.vtc.challenge(&mut w.rng);
    let at_vtc = vtc_submit(&mut w.vtc, &sub);

    let mut s = new_stage(
        "lab-steal",
        "Use another applicant's attestations",
        "frank → VTC, with bob's attestations",
        "Each attestation answers one question: is there a credentialed key whose tag at \
         $s_B = H_0(id_B)$ is $T_j$? Presented for frank, the statement asks about $s_F$ instead.",
    );
    s.fig(
        Fig::new(
            &["frank", "vtc"],
            "bob's attestations, presented for frank.",
        )
        .act(
            "frank",
            r"\V{lab.frank.s}{s_F} := H_0(\V{lab.frank.id}{id_F}) \ne \V{bob.s}{s_B}",
            &["lab.frank.s"],
        )
        .check(
            "frank",
            r"\VerifyAtt(\hvk, id_F, att_1) = 1",
            received.is_ok(),
            "the tag clause asks $T_1 = H_2(s_F)^{usk}$, and $\\ctx_1$ is rebuilt with $id_F$",
        )
        .check(
            "frank",
            r"\mathsf{Prove}(f_2, id_F, (att_1, att_2))",
            prove.is_ok(),
            "frank's prover refuses",
        )
        .send(
            "frank",
            "vtc",
            r"\text{bob's } \pi \text{ with } id_F",
            &[],
            None,
        )
        .check(
            "vtc",
            r"\CheckAtts(\hvk, id_F, \dots) = 1",
            at_vtc.is_ok(),
            "the VTC refuses",
        ),
    );
    s.checks(
        "What the code returned",
        vec![
            Check::new(
                received.is_err(),
                "frank's engine rejects the attestation on receipt",
            )
            .observed(shown(&received))
            .by("frank's engine"),
            Check::new(prove.is_err(), "frank's prover refuses")
                .observed(shown(&prove))
                .by("frank's engine"),
            Check::new(
                at_vtc.is_err(),
                "the VTC refuses bob's proof under frank's identifier",
            )
            .observed(shown(&at_vtc))
            .by("VTC"),
        ],
    );
    let blocked = received.is_err() && prove.is_err() && at_vtc.is_err();
    Ok((
        s,
        verdict(
            if blocked { "blocked" } else { "accepted" },
            "Rejected: an attestation is bound to the identifier it was made for.",
        ),
    ))
}

/// A Fiat–Shamir proof for a statement whose defect `φ(w) − Y` lies in a subgroup of order 3:
/// guess `c mod 3` (the forge of `tests/pcs_review_regressions.rs`). Returns the attempts.
fn forge(
    rel: &PairingRelation<pcs_vetting_prototype::scheme::E>,
    witness: &[Fr],
    ctx: &[u8],
    rng: &mut StdRng,
) -> R<(FSProof<Fr>, u64)> {
    let defect = rel.recompute_commitment(&Fr::from(1u64), witness)?;
    for attempts in 1..=1000u64 {
        let guess = Fr::from(attempts % 3);
        let (mut a, state) = commit(rel, rng)?;
        for (a_i, d_i) in a.g1.iter_mut().zip(&defect.g1) {
            *a_i += *d_i * guess;
        }
        let c = fiat_shamir::challenge(rel, ctx, &a)?;
        if defect.g1.iter().all(|d| *d * c == *d * guess) {
            return Ok((
                FSProof {
                    challenge: c,
                    responses: respond(state, witness, &c)?,
                },
                attempts,
            ));
        }
    }
    Err("the defect is not of order 3".into())
}

fn cofactor(run: &mut Run, w: &mut World) -> Out {
    let hvk = w.vtc.hvk().clone();
    let bob_id = *w.bob.id();
    let s_b = w.vtc.open().tag_point(&bob_id)?;
    // P_3 = (0, 2) on y² = x³ + 4.
    let p3a = G1Affine::new_unchecked(Fq::zero(), Fq::from(2u64));
    let on_curve = p3a.is_on_curve();
    let in_subgroup = p3a.is_in_correct_subgroup_assuming_on_curve();
    let p3: G1 = p3a.into_group();
    let order3 = !p3.is_zero() && (p3 + p3 + p3).is_zero();
    let h = <ark_bls12_381::g1::Config as CurveConfig>::COFACTOR;
    // 2^64 ≡ 1 (mod 3), so h mod 3 is the sum of its limbs mod 3.
    let h_mod3 = h.iter().map(|l| l % 3).sum::<u64>() % 3;
    let h_hex = format!(
        "0x{}",
        h.iter()
            .rev()
            .map(|l| format!("{l:016x}"))
            .collect::<String>()
    );

    let alice_usk = *w.vetters[0].usk_scalar();
    let tag = w
        .vtc
        .open()
        .tag()
        .eval(&alice_usk, &s_b)
        .ok_or("tag undefined")?;
    let forged_tag = tag + p3;
    run.val(
        Val::g1("lab.P3", "P_3", &p3).note("$(0, 2)$: on the curve, of order 3, outside $\\G_1$."),
    );
    run.val(Val::g1("lab.Tf", r"T_2 + P_3", &forged_tag).note("alice's tag for bob, shifted by $P_3$. Encodes fine; it is just not in the prime-order subgroup."));

    let cred = w.vetters[0]
        .credential(PERIOD)
        .ok_or("alice has no credential")?;
    let phi = w.a_alice.attestation.phi;
    let pp = w.vtc.open().base_parameters();
    let m_hid = <Base as SigmaFriendlyCredentialBase<_>>::hidden_message(&alice_usk, &cred.aux);
    let m = <Base as CredentialBase>::encode_message(pp, &m_hid, &phi)?;
    let (shown_cred, omega) =
        <Base as CredentialBase>::rerand(pp, &hvk, &m, &cred.cred, &mut w.rng)?;
    let rel = w
        .vtc
        .open()
        .attestation_relation(&hvk, &shown_cred, &phi, &forged_tag, &s_b)?;
    let witness = Open::attestation_witness(&m_hid, &omega);
    let app = w.a_alice.meta.context_bytes()?;
    let ctx = w.vtc.open().attestation_context_with_app(
        &hvk,
        &bob_id,
        &phi,
        &forged_tag,
        &shown_cred,
        Some(app.as_slice()),
    )?;
    let (proof, attempts) = trace::span(
        "alice",
        "forge",
        "commit, hash, keep the commitment iff c ≡ guess (mod 3)",
        || forge(&rel, &witness, &ctx, &mut w.rng),
    )?;
    let sigma_ok = fiat_shamir::verify(&rel, &ctx, &proof);
    let forged = Attestation {
        tag: forged_tag,
        shown: shown_cred,
        phi,
        proof,
    };
    let verify_att = trace::span(
        "bob",
        "PCS::check_attestation_in_context",
        "VerifyAtt of the forged attestation",
        || {
            w.vtc
                .open()
                .check_attestation_in_context(&hvk, &bob_id, &forged, &app)
        },
    );
    // Spliced into bob's k = 2 proof in place of carol's: alice twice.
    let mut sub = w.sub2.clone();
    let j = index_of(&sub, &w.a_carol.attestation.tag)?;
    sub.proof.attestations[j] = forged;
    sub.statements[j] = (w.a_alice.meta.clone(), w.a_alice.token.clone());
    sub.challenge = w.vtc.challenge(&mut w.rng);
    let at_vtc = vtc_submit(&mut w.vtc, &sub);

    let mut s = new_stage(
        "lab-cofactor",
        "Shift a tag by a point of order 3",
        "alice (cheating) → bob → VTC",
        "The cofactor of $\\G_1$ in BLS12-381 is divisible by 3, so the curve has points of \
         order 3 outside the prime-order subgroup. Adding one to a tag gives a *different* \
         point, and the Schnorr clause of the tag still verifies whenever $c \\equiv 0$ \
         modulo 3 in the right sense: a few attempts.",
    );
    s.derive(
        "The point",
        "",
        vec![
            line_ok(
                r"\V{lab.P3}{P_3} = (0, 2) \in E(\mathbb{F}_q): \ 2^2 = 0^3 + 4",
                &["lab.P3"],
                on_curve,
                "on the curve",
            ),
            line_ok(
                r"3 \cdot P_3 = \mathcal{O}, \quad P_3 \ne \mathcal{O}",
                &[],
                order3,
                "of order 3",
            ),
            line_ok(
                r"P_3 \notin \G_1",
                &[],
                !in_subgroup,
                "outside the prime-order subgroup",
            ),
            line_ok(
                &format!(r"h = \texttt{{{h_hex}}}, \quad h \bmod 3 = {h_mod3}"),
                &[],
                h_mod3 == 0,
                "the cofactor $h$ of $\\G_1$ (arkworks' constant) is divisible by 3",
            ),
        ],
    );
    s.fig(
        Fig::new(&["alice", "bob", "vtc"], "One vetter, two tags.")
            .act("alice", r"T := H_2(s_B)^{\usk_A}, \quad \V{lab.Tf}{T'} := T + \V{lab.P3}{P_3}", &["alice.T", "lab.Tf"])
            .act(
                "alice",
                &format!(
                    r"\pi' \gets \text{{commit, hash, retry until }} c' \equiv \text{{guess}} \pmod 3 \quad (\text{{{attempts} attempt{plural}}})",
                    plural = if attempts == 1 { "" } else { "s" }
                ),
                &[],
            )
            .check("alice", r"\VerifyFS(\ctx', \pi') = 1", sigma_ok, "the $\\Sigma$-check alone accepts the forged tag")
            .check("alice", r"T' \ne T", forged_tag != tag, "as group elements: a distinctness test alone would count two vetters")
            .send("alice", "bob", r"att' = (T', \cred^{*\prime}, \varphi_v, \pi')", &["lab.Tf"], None)
            .check("bob", r"\VerifyAtt(att') = 1", verify_att.is_ok(), "refused: $T'$ is not in the prime-order subgroup")
            .send("bob", "vtc", r"\pi \text{ with } (att_2, att') \text{ spliced in}", &[], None)
            .check("vtc", r"\pi \text{ decodes into } \G_1", at_vtc.is_ok(), "refused before any equation is checked"),
    );
    s.checks(
        "What the code returned",
        vec![
            Check::new(sigma_ok, &format!("the forged proof passes `fiat_shamir::verify` on its own, after {attempts} attempt{}", if attempts == 1 { "" } else { "s" })).by("walkthrough"),
            Check::new(verify_att.is_err(), "`VerifyAtt` refuses: every point is subgroup-checked first").observed(shown(&verify_att)).by("bob's engine"),
            Check::new(at_vtc.is_err(), "the VTC refuses the proof").observed(shown(&at_vtc)).by("VTC"),
        ],
    );
    s.p("Pairing equations cannot catch this: $e(P_3, \\cdot) = 1$ for a point of order 3, since $3 \\nmid p$. The defence is a membership test on every received $\\G_1$ and $\\G_2$ element; the crate re-validates every object it is handed, however it was built. Run again for fresh randomness: the number of attempts changes.");
    let blocked = verify_att.is_err() && at_vtc.is_err();
    Ok((
        s,
        verdict(
            if blocked { "blocked" } else { "accepted" },
            "Rejected: $T + P_3$ is not an element of $\\G_1$.",
        ),
    ))
}

fn twin_key(run: &mut Run, w: &mut World) -> Out {
    let _ = run;
    let again = w.vetters[0].enroll(&mut w.vtc, &mut w.rng);
    let mut twin = VetterEngine::new("alice", &w.vtc, &mut w.rng)?;
    let twin_enrol = twin.enroll(&mut w.vtc, &mut w.rng);
    let mut stranger = VetterEngine::new("mallory", &w.vtc, &mut w.rng)?;
    let stranger_enrol = stranger.enroll(&mut w.vtc, &mut w.rng);

    let mut s = new_stage(
        "lab-twin-key",
        "Enrol a second key",
        "alice → VTC",
        "Distinct tags mean distinct *keys*. That they also mean distinct *members* rests on \
         the VTC: it binds one identifier to each member at the first enrolment.",
    );
    s.fig(
        Fig::new(&["alice", "mallory", "vtc"], "Three enrolment attempts.")
            .send(
                "alice",
                "vtc",
                r"\text{root request again, same key } \usk_A",
                &["alice.id"],
                None,
            )
            .check(
                "vtc",
                r"\text{no credential yet under } \texttt{vetter/2026-09}",
                again.is_ok(),
                "one credential per member per period",
            )
            .send(
                "alice",
                "vtc",
                r"\text{root request with a second key } \usk'_A",
                &[],
                None,
            )
            .check(
                "vtc",
                r"id'_A = \text{the identifier bound to alice}",
                twin_enrol.is_ok(),
                "one identifier per member, for life",
            )
            .send(
                "mallory",
                "vtc",
                r"\text{root request, without a vetter grant}",
                &[],
                None,
            )
            .check(
                "vtc",
                r"\text{mallory holds a vetter grant}",
                stranger_enrol.is_ok(),
                "credentials only behind the grant",
            ),
    );
    s.checks(
        "What the code returned",
        vec![
            Check::new(
                again.is_err(),
                "a second credential for alice in the same period is refused",
            )
            .observed(shown(&again))
            .by("VTC"),
            Check::new(twin_enrol.is_err(), "a second key for alice is refused")
                .observed(shown(&twin_enrol))
                .by("VTC"),
            Check::new(
                stranger_enrol.is_err(),
                "a member without the grant gets nothing",
            )
            .observed(shown(&stranger_enrol))
            .by("VTC"),
        ],
    );
    s.p("Each attempt reaches the VTC with a valid root request: the request proves that $C$, $id$ and $T_0$ are under one key the requester knows, not that the key should be admitted. Admission is the VTC's out-of-band check, and the security model takes root credentials as an initial condition.");
    let blocked = again.is_err() && twin_enrol.is_err() && stranger_enrol.is_err();
    Ok((
        s,
        verdict(
            if blocked { "blocked" } else { "accepted" },
            "Refused: one key per member, one credential per period, only behind the grant.",
        ),
    ))
}

fn capacity(run: &mut Run, w: &mut World) -> Out {
    let _ = run;
    let label = w.vtc.current_token_label().to_string();
    let alice = &mut w.vetters[0];
    let mut rows = vec![vec![
        "after bob's vetting".to_string(),
        "—".into(),
        alice.tokens_free().to_string(),
        alice.tokens_held().to_string(),
    ]];
    let mut push = |what: &str, outcome: String, v: &VetterEngine| {
        rows.push(vec![
            what.to_string(),
            outcome,
            v.tokens_free().to_string(),
            v.tokens_held().to_string(),
        ]);
    };
    let r1 = alice.accept(None, 2);
    push("accept a request", shown(&r1), alice);
    let r2 = alice.accept(None, 2);
    push("accept another", shown(&r2), alice);
    let r3 = alice.accept(None, 2);
    push("accept a third", shown(&r3), alice);
    if let Ok(r) = &r2 {
        alice.decline(r);
    }
    push("decline the second (at capacity)", "released".into(), alice);
    let r4 = alice.accept(None, 2);
    push("accept again", shown(&r4), alice);
    let extra = alice.drip(&mut w.vtc, 1, &label, 3, &mut w.rng);
    push("ask for an extra drip in tick 1", shown(&extra), alice);
    let next = alice.drip(&mut w.vtc, 2, &label, 3, &mut w.rng);
    push("the drip of tick 2", shown(&next), alice);

    let mut s = new_stage(
        "lab-capacity",
        "Run out of tokens",
        "alice ⇄ VTC",
        "Accepting a vetting request reserves a token; attesting spends it. When no token is \
         free, the engine declines with `atCapacity`, and the VTC serves exactly one drip per \
         member and tick, whatever the member asks.",
    );
    s.table("alice's wallet", &["step", "result", "free", "held"], rows);
    s.checks(
        "What the code returned",
        vec![
            Check::new(
                r3.is_err(),
                "with every token reserved, the next request is declined",
            )
            .observed(shown(&r3))
            .by("alice's engine"),
            Check::new(r4.is_ok(), "declining a request releases its token")
                .observed(shown(&r4))
                .by("alice's engine"),
            Check::new(extra.is_err(), "an extra drip in the same tick is refused")
                .observed(shown(&extra))
                .by("VTC"),
            Check::new(next.is_ok(), "the next tick is served as usual")
                .observed(shown(&next))
                .by("VTC"),
        ],
    );
    s.p("Nothing the VTC observes depends on how many tokens a vetter used: the drip is unconditional and identical for everyone, and a spend reveals only its label. A personal limit below the drip lives in the vetter's engine and is never sent anywhere.");
    let ok = r3.is_err() && r4.is_ok() && extra.is_err() && next.is_ok();
    Ok((
        s,
        verdict(
            if ok { "blocked" } else { "accepted" },
            "Capped: reservations bound capacity, one drip per tick.",
        ),
    ))
}

fn rotation(run: &mut Run, w: &mut World) -> Out {
    let hvk = w.vtc.hvk().clone();
    let bob_id = *w.bob.id();
    let old_phi = w.vtc.live_vetter_phis()?[0];
    w.vtc.rotate("2026-10")?;
    for v in &mut w.vetters {
        v.enroll(&mut w.vtc, &mut w.rng)?;
    }
    let new_phi = w.vtc.live_vetter_phis()?[0];
    run.val(
        Val::fr("lab.phi10", r"\varphi_{v'}", &new_phi)
            .who(&["public"])
            .note("$\\EncPred(0, \\texttt{vetter/2026-10})$."),
    );
    // alice refreshes: same statement, the current period, a fresh token.
    let refreshed = w.vetters[0].refresh(&w.vtc, &bob_id, &mut w.rng)?;
    let same_tag = refreshed.attestation.tag == w.a_alice.attestation.tag;
    let alice_new = refreshed.clone();
    w.bob.replace(&w.vtc, refreshed)?;
    let c = w.vtc.challenge(&mut w.rng);
    let mixed = w.bob.submit(&w.vtc, &c, &mut w.rng)?;
    let phis: Vec<Fr> = mixed.proof.attestations.iter().map(|a| a.phi).collect();
    let mixes = phis.contains(&old_phi) && phis.contains(&new_phi);
    let mixed_ok = vtc_submit(&mut w.vtc, &mixed);
    // Emergency: 2026-09 leaves the AllowList now.
    w.vtc.drop_period(PERIOD)?;
    let usk = UserSecretKey::from_scalar(*w.bob.usk_scalar());
    let c = w.vtc.challenge(&mut w.rng);
    let app0 = app0(w, &bob_id, &w.bob.join_did, &c)?;
    let pair = [w.a_carol.clone(), alice_new.clone()];
    let apps: Vec<Vec<u8>> = pair
        .iter()
        .map(|h| h.meta.context_bytes())
        .collect::<Result<_, _>>()?;
    let app_refs: Vec<&[u8]> = apps.iter().map(Vec::as_slice).collect();
    let atts: Vec<_> = pair.iter().map(|h| h.attestation.clone()).collect();
    let (proof, _) = w.vtc.open().prove_in_context(
        &hvk,
        &hidden_vetting_predicate(2),
        &bob_id,
        &usk,
        &atts,
        &app_refs,
        &app0,
        &mut w.rng,
    )?;
    let stale = Submission {
        id: bob_id,
        join_did: w.bob.join_did.clone(),
        challenge: c,
        statements: pair
            .iter()
            .map(|h| (h.meta.clone(), h.token.clone()))
            .collect(),
        proof,
    };
    let stale_res = vtc_submit(&mut w.vtc, &stale);
    // carol refreshes too; bob proves again with both under 2026-10.
    let carol_new = w.vetters[1].refresh(&w.vtc, &bob_id, &mut w.rng)?;
    w.bob.replace(&w.vtc, carol_new)?;
    let c = w.vtc.challenge(&mut w.rng);
    let fresh = w.bob.submit(&w.vtc, &c, &mut w.rng)?;
    let fresh_ok = vtc_submit(&mut w.vtc, &fresh);

    let mut s = new_stage(
        "lab-rotation",
        "Rotate the period, then drop the old one",
        "VTC, alice, carol, bob",
        "The scheme has no revocation; currency comes from the class label. At a rotation \
         every live vetter is re-issued a credential on the same key, so tags do not change, \
         and the VTC accepts the current and the previous label.",
    );
    s.fig(
        Fig::new(
            &["alice", "bob", "vtc"],
            "Rotation, refresh and an emergency drop.",
        )
        .act(
            "vtc",
            r"\text{rotate: live classes } \{\varphi_{v'}, \varphi_v\}",
            &["lab.phi10", "phi.v"],
        )
        .send(
            "vtc",
            "alice",
            r"\text{root credential under } \texttt{vetter/2026-10}, \text{ same } \usk_A",
            &[],
            None,
        )
        .send(
            "alice",
            "bob",
            r"\text{refreshed } att_2 \text{ under } \varphi_{v'}",
            &["alice.T"],
            None,
        )
        .check(
            "bob",
            r"T_2^{\mathrm{new}} = T_2",
            same_tag,
            "a refresh keeps the tag: it cannot count as a second vetter",
        )
        .send(
            "bob",
            "vtc",
            r"\pi \text{ with } \varphi_1 = \varphi_v,\ \varphi_2 = \varphi_{v'}",
            &[],
            None,
        )
        .check(
            "vtc",
            r"P(\varphi_v, \varphi_{v'}) = 1",
            mixed_ok.is_ok(),
            "one proof may mix two live periods",
        )
        .act(
            "vtc",
            r"\text{emergency: drop } \texttt{2026-09} \text{ from the AllowList}",
            &[],
        )
        .send(
            "bob",
            "vtc",
            r"\pi \text{ still carrying carol's } \varphi_v",
            &[],
            None,
        )
        .check(
            "vtc",
            r"P(\varphi_v, \varphi_{v'}) = 1",
            stale_res.is_ok(),
            "the whole proof fails",
        )
        .send(
            "bob",
            "vtc",
            r"\pi \text{ after carol refreshes too}",
            &[],
            None,
        )
        .check(
            "vtc",
            r"P(\varphi_{v'}, \varphi_{v'}) = 1",
            fresh_ok.is_ok(),
            "admitted under the current period",
        ),
    );
    s.checks(
        "What the code returned",
        vec![
            Check::new(mixes, "bob's proof mixes the two periods").by("anyone"),
            Check::new(
                mixed_ok.is_ok(),
                "the mixed proof is accepted while both periods are live",
            )
            .observed(shown(&mixed_ok).replace("Ok", "Ok(decision)"))
            .by("VTC"),
            Check::new(
                stale_res.is_err(),
                "after the drop, any proof carrying the old class fails as a whole",
            )
            .observed(shown(&stale_res))
            .by("VTC"),
            Check::new(
                fresh_ok.is_ok(),
                "refreshed attestations, same tags, are accepted",
            )
            .observed(shown(&fresh_ok).replace("Ok", "Ok(decision)"))
            .by("VTC"),
        ],
    );
    s.p("Removing a vetter means not re-issuing at the next rotation. Rotating the helper key instead would not work: the applicant's identifier depends on the public parameters, so attestations under two keys would not even concern the same identifier.");
    let ok = same_tag && mixes && mixed_ok.is_ok() && stale_res.is_err() && fresh_ok.is_ok();
    Ok((
        s,
        verdict(
            if ok { "blocked" } else { "accepted" },
            "Old class refused after the drop; refreshed attestations keep their tags.",
        ),
    ))
}

fn self_vetting(run: &mut Run, w: &mut World) -> Out {
    let mut puppet = ApplicantEngine::new(&w.vtc, "did:example:alice-2", &mut w.rng)?;
    let puppet_id = *puppet.id();
    let s_p = w.vtc.open().tag_point(&puppet_id)?;
    let a_self = vet(
        &w.vtc,
        &mut w.vetters[0],
        &puppet,
        VettingMethod::InPerson,
        &mut w.rng,
    )?;
    let a_carol = vet(
        &w.vtc,
        &mut w.vetters[1],
        &puppet,
        VettingMethod::Video,
        &mut w.rng,
    )?;
    let t_self = a_self.attestation.tag;
    puppet.receive(&w.vtc, a_self)?;
    puppet.receive(&w.vtc, a_carol)?;
    let c = w.vtc.challenge(&mut w.rng);
    let sub = puppet.submit(&w.vtc, &c, &mut w.rng)?;
    let t0 = sub.proof.t0;
    let d = vtc_submit(&mut w.vtc, &sub);
    let alice_t0 = w
        .vtc
        .open()
        .tag()
        .eval(w.vetters[0].usk_scalar(), &s_p)
        .ok_or("tag undefined")?;
    run.val(Val::g1("lab.p.id", "id_P", &puppet_id).who(&["alice", "vtc"]));
    run.val(Val::g1("lab.p.T0", "T_0", &t0).note("Under the puppet's fresh application key."));
    run.val(
        Val::g1("lab.p.Ta", r"T_A", &t_self)
            .note("alice's tag for her own puppet, under her vetter key."),
    );
    let admitted = d.as_ref().is_ok_and(|d| d.evaluation.satisfied());

    let mut s = new_stage(
        "lab-self-vetting",
        "Vouch for your own second persona",
        "alice, as vetter and as applicant",
        "Self-exclusion, $T_0 \\notin \\{T_j\\}$, excludes the *application key*. The \
         applicant's key is fresh for every application, so it never equals a vetter's key, \
         and nothing ties the new application to alice.",
    );
    s.fig(
        Fig::new(
            &["alice", "alice-2", "vtc"],
            "alice vets a fresh application of her own.",
        )
        .act(
            "alice-2",
            r"\usk_P \sample \Z_p^{*}, \quad \V{lab.p.id}{id_P} := \gone^{\usk_P}",
            &["lab.p.id"],
        )
        .send(
            "alice",
            "alice-2",
            r"att = (\V{lab.p.Ta}{T_A} = H_2(s_P)^{\usk_A}, \dots) \quad \text{(in person)}",
            &["lab.p.Ta"],
            None,
        )
        .say(
            "alice-2",
            "also gets carol's attestation (video), for the second vetter",
        )
        .send(
            "alice-2",
            "vtc",
            r"\pi \text{ with } \V{lab.p.T0}{T_0} = H_2(s_P)^{\usk_P}",
            &["lab.p.T0"],
            None,
        )
        .check(
            "vtc",
            r"T_0 \notin \{T_A, T_C\}",
            t0 != t_self,
            "passes: $T_0$ is under $usk_P$, not $usk_A$",
        )
        .check(
            "vtc",
            r"\text{admit}",
            admitted,
            "the policy is met: two distinct vetters, one in person",
        ),
    );
    s.checks(
        "What the code returned",
        vec![
            Check::new(t0 != t_self, "the self-exclusion tag differs from alice's tag").tex(r"\V{lab.p.T0}{T_0} \ne \V{lab.p.Ta}{T_A}").by("anyone"),
            Check::new(alice_t0 == t_self, "had alice applied with her vetter key, $T_0$ would equal her tag, and the proof would fail").tex(r"H_2(s_P)^{\usk_A} = T_A").by("walkthrough, with alice's key"),
            Check::new(admitted, "the VTC admits alice's second persona").observed(match &d { Ok(d) => format!("Ok: distinct vetters = {}, needs = {:?}", d.evaluation.distinct_vetters(), d.evaluation.needs.iter().map(|n| n.to_wire()).collect::<Vec<_>>()), Err(e) => format!("Err({e})") }).by("VTC"),
        ],
    );
    s.callout(
        "warn",
        "This is a limit of the design, not a bug: the cryptography proves $k$ distinct \
         credentialed keys, and one of them may belong to the applicant's other persona. What \
         limits it is $k \\ge 2$ distinct vetters (alice still needed carol), the token cap, \
         and the human check by the other vetters. The OpenVTC analysis lists it among the \
         limits of hidden mode.",
    );
    Ok((
        s,
        verdict(
            if admitted { "limit" } else { "blocked" },
            if admitted {
                "Accepted: the cryptography does not prevent this."
            } else {
                "Refused in this run."
            },
        ),
    ))
}
