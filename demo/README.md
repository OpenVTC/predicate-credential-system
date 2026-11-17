# pcs-vetting-prototype

A throwaway prototype of hidden-vetter admission for OpenVTC. It is built on `pcreds`, the
protocol `Π_PCreds` of the Predicate Credential System (PCS) in the crate one directory up, with
its application contexts.

The applicant, Bob, proves to a VTC that `k` distinct, currently eligible vetters vetted him. The
VTC learns nothing about which vetters they were.

The design is OpenVTC's `vetting-hidden-vetters-pcs.md`, including the corrections in its §13
where `pcreds` allows them (see [Changes for `pcreds`](#changes-for-pcreds)). This prototype is
step 1 of that document's order of work.

**Not production code.** Everything runs in memory. There is no transport, no DIDs and no
persistence.

## Run

```sh
cargo test -p pcs-vetting-prototype --release
```

It is a workspace member of this repository (`publish = false`) and depends on the
`predicate-credential-system` crate one directory up.

**Not run in CI.** It pulls in `vta-sdk`'s whole dependency tree (trust-tasks-rs,
dtg-credentials, reqwest/rustls, ...), so it is an optional harness for developers working on the
OpenVTC integration, run locally as above, rather than a gate on every PR.

## Layout

| Module | Role in the design |
|---|---|
| `scheme` | The instantiation (`Σ-PS` with `Tag_DDH` over BLS12-381), plus the labels: a fixed deployment label, one helper key per vetter period, and token labels |
| `meta` | The application contexts: `StatementMeta` for each attestation (`ctx_j`), and `ProofContext` for the request (`ctx_0`) (§4.1, §4.2) |
| `token` | Attestation tokens: `Σ-PS` blind signatures on secret serials under one key per label, with proofs of opening, spent sets per label, and the vetter's wallet (newest first, with reservations) (§5.1, §5.2) |
| `vtc` | The VTC as PCS *helper*: root admissions behind the grant check, one credential per member and period, rotation, drip, event mode, evaluation of a submission into VTI `StatementFacts`, and withdrawal |
| `vetter` | The vetter's PCS engine, which in production lives in the vetter's VTA: a key and a credential per period, enrolment, drip, accept/decline, attest, refresh and withdraw |
| `applicant` | The applicant's PCS engine: a fresh `usk` for each application, the attestation requests, verification of attestations on receipt, and the request |

## Changes for `pcreds`

This prototype was first written against the earlier `pcs` API of this crate, whose predicates
carried class labels. `pcreds` has none, and every identifier and tag is a function of the
helper key: `id = Tag(usk, x_0)` with `x_0 = H_id(⟨hvk⟩)`, and `t_{P→Q} = Tag(usk_P, x_Q)` with
`x_Q = H_req(⟨pp, hvk, id_Q, j_Q⟩)`. Three parts of the design change with it.

- **Periods are helper keys.** The vetter class label `vetter/<period>` of §13 C1 becomes one
  helper key per period, the epoch rotation of `(hvk, hsk)` that §4.3 described before C1. The
  VTC keeps the current and the previous period live, as before.
  - *An application lives in one period.* The applicant registers under the current period's
    key, and the VTC evaluates the request under that key alone. One request cannot mix periods,
    which was C1's aim. Tags under different keys are unlinkable, so the VTC could not tell one
    vetter's attestations of two periods apart, and a request that mixed them would let one
    vetter count twice.
  - *Rotation.* An application in flight completes under its period while that period is live,
    since vetters keep their credential of the previous period. A vetter enrolled under the new
    period only cannot vet it. Once the period is dropped, the request fails as a whole, the
    applicant registers again under the new period, and each vetter refreshes its statement as in
    §4.3: the same metadata, a fresh token, no new session. The refreshed attestation has a new
    tag.
  - *Removal keeps its strength.* A removed vetter gets no credential under the next period, and
    cannot attest at all once the period of its last credential is dropped.
  - *Vetter keys.* A vetter draws a fresh key for each period, the per-period keys of §18.2. C2's
    stable `usk` and `id` no longer hold, and the VTC binds one identifier per member and period
    instead of one per member for life. Nothing needs more, as no request spans two periods.
- **Tokens use one key per label.** The `Σ-PS` of `pcreds` signs one scalar, the serial, so the
  label is in the key, as with the per-month token keys of §5.1, and not in a second message as
  C1 had it. Closing a label deletes its key. A spend still reveals the serial with a
  re-randomised signature, recorded in the label's spent set.
- **Attestations and the submission are `pcreds` messages.** The applicant sends each vetter
  `(id_Q, π_id)` under a fresh session `ssid` and the vetter's contact name, and the vetter
  answers with an attestation bound to the statement metadata, an application context. The
  submission is a `pcreds` credential request under the session `ssid = challenge`, bound to the
  metadata of every statement in order and to the proof context. The VTC evaluates it, which
  gives `N''`, the distinct tags of the valid attestations, and never answers it with a
  credential. Its helpers have a policy that no request meets, so every credential under a
  period's key is a root admission (C4). A statement whose attestation does not verify is
  `unverified` and does not count, where in the `pcs` version one invalid attestation failed the
  whole proof. A withdrawal is a proof of knowledge of the key behind the tag at the applicant's
  recipient point, under a withdrawal context.

## What the tests establish

`tests/end_to_end.rs` has one test per claim of the design. Counting is done by `vta-sdk 0.56.1`'s
own `vetting::requirements::evaluate`, with no changes.

- **Admission from two hidden vetters.** The facts the policy sees contain no member id and no
  vetter PCS id.
- **`requestMore`, then admission on resubmission.** A token presented again with the same
  `(id, tag)` counts once, and is not flagged as an anomaly.
- **One vetter counts once across submissions.** The VTC gives the reason `same-vetter`.
- **A double-spent token does not count.** The VTC records an anomaly without being able to name
  anyone.
- **Nothing moves between attestations.** A swapped token fails as `token-mismatch`. Swapped
  metadata breaks the request's `π_iss`.
- **Challenges.** Each challenge works once. It is the request's `ssid`, and the join DID is bound
  in its proof context.
- **Closed token labels.** Tokens under a closed label fail as `no-token`.
- **An application lives in one period.** It completes across a rotation while its period is
  live, a vetter of the new period only cannot vet it, it fails as a whole once its period is
  dropped, and refreshes carry it to the new period with new tags. An attestation of the old
  application forced into the new request is `unverified` and does not count.
- **Dropped periods.** A request under a dropped period fails with `PeriodNotLive`, and the
  current period cannot be dropped.
- **One credential per member and period.** Enrolling twice is refused, and so is a twin key in
  the same period. A member without a grant gets no credential. A removed vetter keeps its
  credential of a live period until the period leaves the window, gets none under the next, and
  cannot attest once the period is dropped.
- **Withdrawal by tag.** It names the statement's own tag, stops the statement counting, and one
  vetter cannot forge another vetter's withdrawal.
- **Drip and reservations.** The drip is served once per tick. Reservations bound capacity, a
  decline releases its token, and a personal limit is enforced locally.
- **Proofs of opening.** Each is bound to its tick and its member.
- **Event mode.** It needs a group of at least the floor size and an approver from outside the
  group. Event tokens die when the event closes.

**Mutation check (2026-11-16).** Each of eight VTC defences was disabled in turn: the double-spend
check, one credential per member and period, the token signature check, single-use challenges,
the event group floor, `N''` deciding which statements verified, dropping a period, and the
withdrawal proof check. Each time, the test that covers that defence failed.

## Not covered

- Trust Task messages and transport. A refresh finds the statement by its session's `ssid`,
  which stands in for the channel the request arrives on.
- DIDs. The `id ↔ joinDid` binding is a digest standing in for a Data Integrity proof.
- Where the VTA keeps keys. The vetter engine keeps its key of each period in memory, for
  withdrawals.
- Persistence.
- Concurrency. The signing locks exist, but the tests are single-threaded.
- JCS canonicalisation of the metadata.
- **Re-counting after admission.** A later submission can overwrite a counted statement with
  `no-token`. This needs a rule, see the design doc, §14.
- **One applicant across periods.** A registration under a new period is a new application, and
  the VTC keeps no record across it.
