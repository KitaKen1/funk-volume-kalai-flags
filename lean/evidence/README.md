# Verification records

| Record | Check |
|---|---|
| [package-audit.json](package-audit.json) | Source hashes, generation, two exact goal types, two exact FC target types and 16 axiom reports |
| [package-build.log](package-build.log) | Complete modular proof build |
| [fc-statement-build.log](fc-statement-build.log) | Both FC statements compile with their intentional `by sorry` |
| [fc-statement-check.json](fc-statement-check.json) | Two FC targets, official attributes and statement placeholders separate from the proofs |
| [fc-exact-targets.json](fc-exact-targets.json), [log](fc-exact-targets.log) | Both proved FC targets and 15 geometric declarations match the actual compiled FC interfaces |
| [package-axioms.log](package-axioms.log) | Declaration types and axioms |
| [standalone-build.log](standalone-build.log) | Complete Lean 4.35.0-rc4 file, local compilation |
| [lean4web-live.json](lean4web-live.json) | Public Lean4Web: zero errors, four core/FC proof reports without `sorryAx` |
| [lean4web-live-diagnostics.json](lean4web-live-diagnostics.json) | Public-server diagnostics |
| [distribution-check.json](distribution-check.json) | Package scope and source correspondence |
| [github-publication.json](github-publication.json) | Published content commit and matching public Lean4Web source |
| [proof-sources.json](proof-sources.json) | Proof/configuration source hashes |
| [standalone-4.34.1-build.log](standalone-4.34.1-build.log) | Original single-file edition |

All audited proof declarations use only `propext`, `Classical.choice` and `Quot.sound`.

The FC problem statements are not included in the audited proof dependencies.

Earlier checks of the original modular sources are recorded in
[original-verification.json](original-verification.json): nanoda checked
67,170 reachable declarations; a cache-free 4,123-job rebuild and subsequent
independent check covered 67,081 declarations in another workspace on the same Mac.
These checks cover the original modular proofs. The added FC final theorems,
the answer elaborator adaptation and the two newer web API edits were checked
by ordinary Lean. Final third-party semantic review remains pending.

From the package root, repeat the local audit with
`python3 lean/scripts/build_audit.py`. To repeat the public-server check, use
`node lean/scripts/check_lean4web_live.mjs` (Node.js 22+); it sends the complete
source to the public server.
The current public check used Mathlib `9e6b3aac99b624d10c84653ab9c5357283b9b3b8`;
the local web project remains pinned to `021ce68bf125a049beee22b3fc7664d78728e21d`.
To reproduce that public check, set
`FUNK_LEAN4WEB_MATHLIB_REV=9e6b3aac99b624d10c84653ab9c5357283b9b3b8`
when running the checker.
