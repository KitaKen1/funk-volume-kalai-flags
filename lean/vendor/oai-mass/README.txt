Pinned OAI mass-source dependency closure

Repository: https://github.com/openai/math
Commit: adc7f1241b42e322a6451854ab7e4b4c146bf78a
Source prefix: lean/OAI/
License: Apache-2.0; original LICENSE included.
228 original Lean modules, 995005 bytes, no compatibility source edits.

manifest.json records exact URLs, SHA256 hashes, and internal imports.
Funk/LensMassLower.lean applies the generic homogeneous flux and regular
mass estimates to the actual local tilted-lens source. The original body's
Mahler theorem is not substituted for a Funk lower-bound theorem.

Run python3 scripts/verify_upstream_sources.py and python3 scripts/verify.py.
Local build and used-declaration axiom checks do not constitute independent
kernel replay or semantic validation of the full candidate manuscript.
