# pcs-vetting-prototype

A throwaway prototype of hidden-vetter admission for OpenVTC. It is built on the Predicate
Credential System (PCS).

The applicant, Bob, proves to a VTC that `k` distinct, currently eligible vetters vetted him. The
VTC learns nothing about which vetters they were.

The design is OpenVTC's `vetting-hidden-vetters-pcs.md`, including the corrections in its §13.
This prototype is step 1 of that document's order of work.

**Not production code.** Everything runs in memory. There is no transport, no DIDs and no
persistence.

## Run

```sh
cargo test -p pcs-vetting-prototype --release
```

To watch it instead, step through the narrated walkthrough. It prints every group element
that goes over the wire, recomputes the equations live, and shows the submission in its wire
form. It is written for an audience of cryptographers:

```sh
cargo run -p pcs-vetting-prototype --release --example walkthrough
```

Enter goes to the next stage, `b` goes back, a number jumps to that stage, and `q` quits.
`--auto` prints every stage at once.

To present it, run the same walkthrough as a local web page:

```sh
cargo run -p pcs-vetting-prototype --release --example walkthrough-web
```

It serves <http://127.0.0.1:8787/> and opens it in the browser. The page has the terminal
walkthrough's 15 stages, numbered from 0. Step 0 is an overview, where nothing runs: the
instantiation, a map of every message of the run, and what each step does. Steps 1 to 14 are
the terminal's stages 2 to 15, and each has the same parts:

- A bar that stays on screen and says where you are: the step and its phase, which action is
  running, and which engine call it is in.
- The step's actions, numbered, each by one party: what it computes, what it checks, and what
  it sends to whom. An action first shows the engine calls it made, one by one, and then its
  result.
- The content of every message, as JSON:
  - the join submission in its wire form;
  - the VTC's answer in the shape of the join ceremony's `Verdict` (vta-sdk), with its `needs`;
  - every other message as the in-memory object it is in this prototype, written out by the
    crate's `serde` layer.
- The outcome of the step.
- A panel of where things stand: who holds what, and how far each application is from the
  policy, including what it is still missing.

With the default seed (7) every value is the one the terminal walkthrough prints, and *New
randomness* recomputes everything under a random seed. In the formulas, colour gives each
symbol's group (𝔾₁, 𝔾₂, 𝔾_T, ℤ_p or bytes), and selecting a symbol, a value or a coloured
string in a message opens its full encoding, who holds it and where else it appears. Secrets
are hatched; they are shown only because the walkthrough reads them through the engines' demo
hooks.

The whole run is computed when the page loads. The actions are played one after another so
that an audience can follow. The pace can be *auto*, *slow*, *one action per key* or *instant*;
the times shown are the ones measured in the run, recorded by the `trace` hook, and `--release`
matters for them. Every equation is recomputed and both sides of each pairing equation are
shown. The *attack lab* runs experiments on request, against the state of step 9 (bob just
admitted) for the same seed:

- editing a signed statement (the Fiat–Shamir challenge diverges);
- counting one vetter twice;
- replaying or transplanting a proof;
- using another applicant's attestations;
- shifting a tag by a point of order 3, where the forged proof passes `fiat_shamir::verify` and
  only the subgroup check stops it;
- a twin key;
- the token budget;
- rotation and an emergency drop of a period;
- a vetter vouching for a second persona of her own. This one is accepted: the applicant's key
  is fresh, so `T_0 ∉ {T_j}` does not exclude it.

Keys: → plays the next action, or shows the rest of the step, or goes to the next stage; ← goes
back; `R` plays a stage again; `P` is presenter mode (larger type, the state below each stage);
`?` lists the rest. Flags: `--port N`, `--seed N`, `--no-open`, and `--assets demo/web`, which
serves the page from disk so that it can be edited without a rebuild.

The page is plain HTML, CSS and JavaScript with no build step. It needs no network: KaTeX
0.17.0 and its fonts are vendored unmodified under `web/vendor/katex` (MIT; provenance and
SHA-256 sums in `SOURCE.txt`), and its three faces (KaTeX_Main, KaTeX_SansSerif,
KaTeX_Typewriter) are also the page's text faces. The server uses the standard library only,
so the workspace lockfile does not change. It listens on 127.0.0.1 and refuses any `Host` but
its own (DNS rebinding). Every POST must carry `X-PCS-Demo: 1` and a JSON content type, and
any `Origin` must be the page's own. Pages are served under a Content-Security-Policy that
allows scripts, styles and fonts from the server only, and data reaches the DOM as text or
through KaTeX, never as HTML.

It is a workspace member of this repository (`publish = false`) and depends on the
`predicate-credential-system` crate one directory up.

**Not run in CI.** It pulls in `vta-sdk`'s whole dependency tree (trust-tasks-rs,
dtg-credentials, reqwest/rustls, ...), so it is an optional harness for developers working on the
OpenVTC integration, run locally as above, rather than a gate on every PR.

## Layout

| Module | Role in the design |
|---|---|
| `scheme` | The instantiation (Σ-PS with Tag_DDH over BLS12-381), plus the labels: a fixed deployment label, epochs in the class label `vetter/<period>`, and token labels (§13 C1) |
| `meta` | The application contexts: `StatementMeta` for each attestation (`ctx_j`), and `ProofContext` for the proof (`ctx_0`) (§4.1, §4.2) |
| `token` | Attestation tokens: PS blind signatures on secret serials, with proofs of opening, spent sets per label, and the vetter's wallet (newest first, with reservations) (§5.1, §5.2) |
| `vtc` | The VTC as PCS *helper*: root issuance behind the grant and the member→id binding, rotation, drip, event mode, submission to VTI `StatementFacts`, and withdrawal |
| `vetter` | The vetter's PCS engine, which in production lives in the vetter's VTA: a stable `usk`, enrolment, drip, accept/decline, attest, refresh and withdraw |
| `applicant` | The applicant's PCS engine: a fresh `usk` for each application, verification of attestations on receipt, and the proof |
| `trace` | Demo hook for the web walkthrough: when a recorder is installed, the engines report each protocol call (who, which algorithm, how long, any error). Otherwise every wrapper is a plain call, and no wrapper draws randomness |

The web walkthrough is `examples/walkthrough-web/`: `scenario.rs` (the stages as flows of
actions, calling the engines in the terminal walkthrough's order), `lab.rs` (the experiments),
`model.rs` (the JSON the page renders: values, flows, the ledger of who holds what),
`server.rs` and `assets.rs`. The page itself is `web/`.

## What the tests establish

`tests/end_to_end.rs` has one test per claim of the design. Counting is done by `vta-sdk 0.48`'s
own `vetting::requirements::evaluate`, with no changes.

- **Admission from two hidden vetters.** The facts the policy sees contain no member id and no
  vetter PCS id.
- **`requestMore`, then admission on resubmission.** A token presented again with the same
  `(id, tag)` counts once, and is not flagged as an anomaly.
- **One vetter counts once across submissions.** The VTC gives the reason `same-vetter`.
- **A double-spent token does not count.** The VTC records an anomaly without being able to name
  anyone.
- **Nothing moves between attestations.** A swapped token fails as `token-mismatch`. Swapped
  metadata breaks the proof.
- **Challenges.** Each challenge works once. It is bound to the proof, and so is the join DID.
- **Closed token labels.** Tokens under a closed label fail as `no-token`.
- **Rotation.** One proof can mix attestations from two periods. A refresh keeps the tag.
- **Dropped periods.** If any attestation's period has been dropped, the whole proof fails with
  `PolicyRejected`.
- **One member, one identifier.** Enrolling twice is refused, and so is a second key pair (a twin)
  for the same member. A member without a grant, or a removed member, gets no credential.
- **Withdrawal by tag.** It stops the statement counting, and one vetter cannot forge another
  vetter's withdrawal.
- **Drip and reservations.** The drip is served once per tick. Reservations bound capacity, a
  decline releases its token, and a personal limit is enforced locally.
- **Proofs of opening.** Each is bound to its tick and its member.
- **Event mode.** It needs a group of at least the floor size and an approver from outside the
  group. Event tokens die when the event closes.

**Mutation check.** I disabled each of five VTC defences in turn: the double-spend check, the
member→id binding, the token signature check, single-use challenges and the event group floor.
Each time, the test that covers that defence fails.

## Not covered

- Trust Task messages and transport.
- DIDs. The `id ↔ joinDid` binding is a digest standing in for a Data Integrity proof.
- Where the VTA keeps keys.
- Persistence.
- Concurrency. The signing locks exist, but the tests are single-threaded.
- JCS canonicalisation of the metadata.
- **Re-counting after admission.** A later submission can overwrite a counted statement with
  `no-token`. This needs a rule; see the design doc, §14.
