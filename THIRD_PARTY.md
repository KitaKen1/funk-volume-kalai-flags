# Third-party sources

## OpenAI's OAI mathematical library

- Source: **OpenAI**, [openai/math](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI), revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
- Used for: the homogeneous-flux, Stokes and holomorphic mass estimates in `OAI.Analysis.Mahler`.
- Included: 228 unchanged modules in `lean/vendor/oai-mass/OAI/`.
- License: Apache-2.0; [original license](lean/vendor/oai-mass/LICENSE).
- Source hashes and URLs: [manifest](lean/vendor/oai-mass/manifest.json).

The web edition includes this source. Its two Mathlib API adaptations are
recorded in [source-map.json](lean4web/source-map.json).

## Formal Conjectures utilities

- Source: **The Formal Conjectures Authors**, [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/tree/d838afa7a62f66dc034c96fb011c10b9bde3f44c), revision `d838afa7a62f66dc034c96fb011c10b9bde3f44c`.
- Included: four unchanged modules providing `answer` and the FC attributes in `lean/vendor/formal-conjectures/`.
- License: Apache-2.0; [original license](lean/vendor/formal-conjectures/LICENSE) and [source manifest](lean/vendor/formal-conjectures/manifest.json).

The single-file editions embed the official `answer` syntax and elaborator.
They fix its original default mode (`AnswerSetting.alwaysTrue`) because Lean
cannot read an option initializer in the same file that defines it. FC metadata
attributes are omitted there; geometric definitions and target types are retained.
The vendored utility sources are unchanged.

Mathlib and its dependencies are fetched at the revisions in the Lake manifests.

The directory layout follows [bapat-lal-q-permanent-lean](https://github.com/KitaKen1/bapat-lal-q-permanent-lean).
The root [LICENSE](LICENSE) is retained from the existing repository.
