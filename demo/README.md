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

It is a workspace member of this repository (`publish = false`) and depends on the
`predicate-credential-system` crate one directory up.

## Layout

| Module | Role in the design |
|---|---|
| `scheme` | The instantiation (Σ-PS with Tag_DDH over BLS12-381), plus the labels: a fixed deployment label, epochs in the class label `vetter/<period>`, and token labels (§13 C1) |
| `meta` | The application contexts: `StatementMeta` for each attestation (`ctx_j`), and `ProofContext` for the proof (`ctx_0`) (§4.1, §4.2) |
| `token` | Attestation tokens: PS blind signatures on secret serials, with proofs of opening, spent sets per label, and the vetter's wallet (newest first, with reservations) (§5.1, §5.2) |
| `vtc` | The VTC as PCS *helper*: root issuance behind the grant and the member→id binding, rotation, drip, event mode, submission to VTI `StatementFacts`, and withdrawal |
| `vetter` | The vetter's PCS engine, which in production lives in the vetter's VTA: a stable `usk`, enrolment, drip, accept/decline, attest, refresh and withdraw |
| `applicant` | The applicant's PCS engine: a fresh `usk` for each application, verification of attestations on receipt, and the proof |

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
