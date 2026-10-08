# Lean4Web proof

[FunkKalaiLean4Web.lean](FunkKalaiLean4Web.lean) contains the complete proof
with Mathlib imports only. Lean **4.35.0-rc4**; dependencies are pinned in
[lake-manifest.json](lake-manifest.json).

Open [Lean4Web](https://live.lean-lang.org/), select **Latest Mathlib with Lean
v4.35.0-rc4**, and paste the complete file.

The public server verified it on **8 October 2026**: zero errors and no
`sorryAx` in either FC target theorem. The same FC definitions and target
statements appear at the end, with proofs and `#print axioms`.
[Verification record](../lean/evidence/lean4web-live.json).

Build locally from this directory:

```bash
lake exe cache get
lake build
```

Regenerate from the package root:

```bash
python3 lean/scripts/make_lean4web.py
python3 lean/scripts/make_lean4web.py --check
```

The [source map](source-map.json) records two Mathlib API compatibility edits
and the default-mode adaptation of the official FC `answer` elaborator.
The original Lean 4.34.1 edition is in [pinned-4.34.1/](pinned-4.34.1/).
