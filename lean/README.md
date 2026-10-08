# Modular Lean proof

Lean **4.34.1**, with dependencies pinned in `lake-manifest.json`.

```bash
lake exe cache get
python3 scripts/build_audit.py
```

The audit builds the complete proof library. To check the FC-style statements
in the sibling `FClikelean/` directory, run
`lake --wfail build KalaiFullFlags SymmetricFunkVolume`.

- [FinalTheorems.lean](FinalTheorems.lean): the exact FC targets, proved, followed
  by `#print axioms`.
- [MainTheorems.lean](Funk/MainTheorems.lean): core proofs.
- [Targets.lean](Funk/Targets.lean): geometric definitions and theorem specifications.
- [PublicationStatements.lean](Funk/PublicationStatements.lean): explicit formulas.

The final definitions and statements are generated from the FC files:

```bash
python3 scripts/make_final_theorems.py --check
lake env lean -j1 -Ewarning evidence/CheckFCTargets.lean
```
