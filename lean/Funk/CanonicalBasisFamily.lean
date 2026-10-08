import Funk.CanonicalPacking

/-! A finite, permutation-free family of signed nonsingular row selections.
This is a classical real-valued specification, not an executable floating-point
rank test. Simplicity and probability covering remain proof obligations. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

abbrev SignedRowChoice (n m : ℕ) := (Fin n → Fin m) × (Fin n → Bool)

def canonicalBasisIndices {n m : ℕ} (rows : Fin m → Space n) : Finset (SignedRowChoice n m) := by
  classical
  exact Finset.univ.filter (fun k => StrictMono k.1 ∧
    Matrix.det (fun i => rows (k.1 i) : Matrix (Fin n) (Fin n) ℝ) ≠ 0)

theorem mem_canonicalBasisIndices {n m : ℕ} (rows : Fin m → Space n)
    (k : SignedRowChoice n m) :
    k ∈ canonicalBasisIndices rows ↔ StrictMono k.1 ∧
      Matrix.det (fun i => rows (k.1 i) : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  classical
  simp [canonicalBasisIndices]

/-- For square nonsingular row families, increasing selection leaves exactly
one row order; every sign vector is retained. -/
theorem mem_canonicalBasisIndices_square {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) (k : SignedRowChoice n n) :
    k ∈ canonicalBasisIndices B ↔ k.1 = id := by
  constructor
  · intro hk
    have hs := ((mem_canonicalBasisIndices (fun i => B i) k).mp hk).1
    exact (increasing_selection_eq_of_range_subset strictMono_id hs
      (by intro x _; exact mem_range_self x)).symm
  · intro hk
    apply (mem_canonicalBasisIndices (fun i => B i) k).mpr
    refine ⟨?_, ?_⟩
    · rw [hk]
      exact strictMono_id
    · have he : (fun i => B (k.1 i) : Matrix (Fin n) (Fin n) ℝ) = B := by
        funext i
        rw [hk]
        rfl
      exact he.symm ▸ hB

/-- The user no longer has to supply basis determinants, ordering or duplicate
index proofs. The finite family enforces them, retaining the two geometric gaps. -/
theorem funkVolume_strip_target_of_canonical_cover {n m : ℕ}
    (rows : Fin m → Space n) (hK : IsSymmetricConvexBody (stripBody rows))
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hsimple : ∀ᵐ X ∂volume.restrict (stripBody rows), ∀ k ∈ canonicalBasisIndices rows,
      X ∈ basisFeasibleRegion τ rows k.1 k.2 → NoExtraActive τ rows k.1 k.2 X)
    (hcover : 1 ≤ ∑ k ∈ canonicalBasisIndices rows, lensBoundaryRows n τ
      (basisBoundaryEvent τ k.2 (fun i => rows (k.1 i)) (basisFeasibleRegion τ rows k.1 k.2))) :
    funkVolume (stripBody rows) τ < ⊤ ∧
      ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) ≤
        funkVolume (stripBody rows) τ := by
  apply funkVolume_strip_target_of_simple_cover rows hK hτ0 hτ1
    (canonicalBasisIndices rows) Prod.fst Prod.snd
  · intro k hk
    exact ((mem_canonicalBasisIndices rows k).mp hk).2
  · intro k hk
    exact ((mem_canonicalBasisIndices rows k).mp hk).1
  · intro k _ l _ h
    exact h
  · exact hsimple
  · exact hcover

end
end Funk
