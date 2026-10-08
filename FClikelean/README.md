# FC-style statements

- [KalaiFullFlags.lean](KalaiFullFlags.lean): Kalai's full flag conjecture.
- [SymmetricFunkVolume.lean](SymmetricFunkVolume.lean): the numerical Funk-volume
  lower bound, without equality cases.

Each file has explicit geometric definitions, references and the official FC
annotations, with a `by sorry` proof slot. The complete proofs are in
[MainTheorems.lean](../lean/Funk/MainTheorems.lean)
and [Lean4Web](../lean4web/FunkKalaiLean4Web.lean).

Check the statements:

```bash
cd ../lean
lake --wfail build KalaiFullFlags SymmetricFunkVolume
```
