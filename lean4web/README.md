# Lean4Web proof

[FunkKalaiLean4Web.lean](FunkKalaiLean4Web.lean) contains the complete proof
with Mathlib imports only. Lean **4.35.0-rc4**; dependencies are pinned in
[lake-manifest.json](lake-manifest.json).

Open [Lean4Web](https://live.lean-lang.org/), select **Latest Mathlib with Lean
v4.35.0-rc4**, and paste the complete file.

The public server verified it on **8 October 2026**: zero errors, 39 warnings,
and both main proof declarations without `sorryAx`.
The FC problem statements are distributed separately.
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

The [source map](source-map.json) records two Mathlib API compatibility edits.
The original Lean 4.34.1 edition is in [pinned-4.34.1/](pinned-4.34.1/).
