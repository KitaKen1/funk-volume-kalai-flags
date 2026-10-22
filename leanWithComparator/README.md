# FC #6926: exact final-target verification

This harness verifies `Funk.FormalConjectures.kalaiFullFlags` against the pinned
Formal Conjectures PR statement. The public workflow runs in
`KitaKen1/funk-volume-kalai-flags` and requires the repository to be public.
The same checks first passed in a private sandbox trial.

The [public run 39763236395](https://github.com/KitaKen1/funk-volume-kalai-flags/actions/runs/39763236395)
passed on `b46f8c30d2be8a8ad388a82098019358503c22b6`. Its
[saved evidence](receipts/public-run-39763236395/README.md), including the
[actual axiom report](receipts/public-run-39763236395/axioms.log) and
[nanoda result](receipts/public-run-39763236395/nanoda.log), is retained here.

## Inputs

- PR statement: `KitaKen1/formal-conjectures@decbde8be8be440b1b10c3f4e516d39896bb4b2c`,
  `FormalConjectures/Arxiv/2306.09268/KalaiFullFlags.lean`.
- Proof: `KitaKen1/funk-volume-kalai-flags@5b92194f6b5ed49f380a6412b120ad256d850740`,
  `lean/FinalTheorems.lean`.
- Lean: `v4.34.1`. The complete Mathlib dependency graph is locked to the original
  proof manifest. No cross-version olean/export comparison is performed.
- Permitted axioms: `propext`, `Classical.choice`, `Quot.sound` only.

`reference/proof-source-lock.json` records SHA-256 hashes of all 439 files
under `lean/` and `FClikelean/`. All mathematical proof sources, vendor files and
Lean configuration are byte-identical to the pinned proof commit. Three existing
publication receipt JSON files were updated by public commit `0c71197074dd57cea6d8669218ae42fa43e7eddc`;
the lock records both their original and published hashes under
`publication_metadata`. The checks require the exact published hashes, rather
than excluding these files from verification. `reference/KalaiFullFlags.pr.lean` is the exact PR
snapshot, identified both by Git blob ID and SHA-256. `make_challenge.py` retains
its namespace body byte-for-byte, changing the module/import/public-section
wrapper for the proof's pinned environment. In particular, all definitions,
structure fields, `answer(True)`, the theorem type, attributes, and the intentional
statement placeholder remain unchanged inside that body.

Full Mathlib and the proof's narrower imports choose different, definitionally
equal PartialOrder dictionaries for sets: the complete-partial-order path versus
the chain-complete-partial-order path. `RawPRFC` retains the full-Mathlib instance
selection without changes. `ChallengeFC` disables only the redundant
`CompletePartialOrder.toPartialOrder` instance during elaboration so its dictionary
path matches the fixed proof. `ModelAuditFC` independently reads the raw PR's
compiled interface without importing its placeholder, and checks all eleven
geometric declarations and the final theorem type by definitional equality.
The comparator then retains its original strict comparison, with no definition
holes or expression rewriting. The proof source is unchanged.

## Verification

`ChallengeFC` and `SolutionFC` are compiled and exported separately; they must
never be imported together. The Challenge imports Mathlib and pinned FC utilities,
not the proof modules. `SolutionFC` imports the original `FinalTheorems`.

The driver uses the pinned upstream `Comparator.compareAt` and
`Comparator.checkAxioms` implementation. The final theorem is a theorem target;
all eleven geometric model declarations are explicit roots, and no definitions
are holes. The final theorem type and the reachable definition graph must match.
`AuditFC` also checks the explicit `True ↔ ...` type, including the finite flag
condition and numerical bound, and prints the target's axioms.

The exporter starts from the **FC final theorem**, including the final flag
equivalence and cardinality transport. Nanoda independently checks its entire
exported dependency closure. Its exit status, success message, checked declaration
count, and printed final target must all be present. Each run produces a fresh
result directory and only records success after every stage has completed.

Small compiled control fixtures exercise the same driver and checker: a correct
proof is accepted; `sorry`, a custom axiom, a changed definition body, a changed
theorem type, and a missing target are rejected by the comparator at the expected
stages. An export with a well-formed but ill-typed proof replacement still passes
structural comparison and is rejected by nanoda. These control fixtures are
separate from the actual pinned proof and are explicitly named in the results.

## Run on a fresh Linux checkout

Install the pinned Lean toolchain through elan and Rust `1.90.0` through rustup,
then run:

```sh
cd leanWithComparator
python3 scripts/make_challenge.py --check
lake exe cache get
python3 scripts/setup_tools.py
python3 scripts/verify.py
```

The tools' source revisions are in `pins.json`. The legacy comparator and
exporter are built from unmodified source with the explicit Lean `4.34.1`
toolchain override, as in the original local verification. The driver is a
separate package with an explicit path dependency on the pinned exporter, so the
legacy comparator package's floating exporter dependency is not used.

See `.github/workflows/fc-final-verification.yml` for the disposable hosted Linux
runner setup. The initial trial built the proof from source. Subsequent trials
may reuse proof build products keyed by the pinned proof lock, dependencies,
toolchain and Challenge source; each result records whether this cache was hit.
The workflow may download trusted Mathlib artifacts for the fixed dependency revisions.
This is not a source-only cold build of Mathlib. The core comparison and nanoda
stages are fresh executions. Tool commits, new platform-specific binary hashes,
input hashes, commands, exit codes, durations and evidence hashes are recorded in
`evidence/result.json`, with logs and the checked statement beside it. The large
exports can be reproduced; CI uploads the small logs and JSON/text evidence.

## Scope

This is a comparator-core plus nanoda validation of known, immutable proof
sources in a disposable runner. It does not run the legacy landrun pipeline and
does not claim an adversarial-code build sandbox or an independent human
mathematical review. The old comparator repository is archived; a future upgrade
to Lean 4.35+ can use the integrated `lake comparator` instead, after porting and
rechecking the proof. No such migration is silently applied here.

The original pinned proof link remains valid. Adding this harness does not
change the proof or automatically post a reply to the Formal Conjectures PR.

## Where to see the axiom evidence

Open the successful Actions run and download its `fc6926-evidence` artifact.
`evidence/axioms.log` contains Lean's `#print axioms Funk.FormalConjectures.kalaiFullFlags`
output. `evidence/result.json` records that output as `reported_axioms`.
`evidence/nanoda-config.json` limits independent checking to the same three
axioms, sets `unpermitted_axiom_hard_error` to true and
`unsafe_permit_all_axioms` to false. `evidence/nanoda.log` records the number of
declarations checked without errors. The workflow console also prints the
reported axioms and declaration count at the end of its verification step.
