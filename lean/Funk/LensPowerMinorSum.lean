import Funk.RectangularDeterminant
import Funk.LensMassDensity
import Funk.UnsignedBoundaryCover

/-! Exact Cauchy--Binet sum for the actual lens Jacobian, over the same unsigned
basis indices used by the boundary probability consumer. -/

open Set Matrix Complex MeasureTheory
open scoped BigOperators ENNReal

namespace Funk
noncomputable section

/-- The selected weighted real minor, with the diagonal weights retained. -/
theorem lensWeightedGram_selected_factor {n m : ℕ} (rows : Fin m → Space n)
    (c : Fin m → ℝ) (s : Fin n → Fin m) :
    (((Matrix.of rows).transpose * diagonal c).submatrix id s).det *
      ((Matrix.of rows).submatrix s id).det =
      (∏ i, c (s i)) * (Matrix.of fun i => rows (s i)).det ^ 2 := by
  classical
  have hA : ((Matrix.of rows).transpose * diagonal c).submatrix id s =
      (Matrix.of fun i => rows (s i)).transpose * diagonal (fun i => c (s i)) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.transpose_apply,
      Matrix.of_apply, id_eq]
  rw [hA, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  change _ * (Matrix.of fun i => rows (s i)).det = _
  ring

/-- All increasing selections occur once; no factorial is hidden in this sum. -/
theorem lensWeightedGram_det_eq_increasing_sum {n m : ℕ} (rows : Fin m → Space n)
    (c : Fin m → ℝ) :
    (lensWeightedGram rows c).det = ∑ s ∈ Finset.univ.filter StrictMono,
      (∏ i, c (s i)) * (Matrix.of fun i => rows (s i)).det ^ 2 := by
  classical
  unfold lensWeightedGram
  rw [rectangular_det_eq_increasing_minors]
  exact Finset.sum_congr rfl (fun s _ => lensWeightedGram_selected_factor rows c s)

/-- Singular selections vanish, leaving precisely the existing unsigned basis set. -/
theorem lensWeightedGram_det_eq_unsigned_sum {n m : ℕ} (rows : Fin m → Space n)
    (c : Fin m → ℝ) :
    (lensWeightedGram rows c).det = ∑ s ∈ unsignedBasisIndices rows,
      (∏ i, c (s i)) * (Matrix.of fun i => rows (s i)).det ^ 2 := by
  classical
  rw [lensWeightedGram_det_eq_increasing_sum]
  symm
  apply Finset.sum_subset
  · intro s hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((mem_unsignedBasisIndices rows s).mp hs).1⟩
  · intro s hs hn
    have hm := (Finset.mem_filter.mp hs).2
    have hd : (Matrix.of fun i => rows (s i)).det = 0 := by
      by_contra hd
      exact hn ((mem_unsignedBasisIndices rows s).mpr ⟨hm, hd⟩)
    rw [hd, zero_pow (by decide : 2 ≠ 0), mul_zero]

/-- Exact norm-square minor sum of the genuine complex derivative Gram matrix. -/
theorem lensPowerJacobian_gram_det_eq_unsigned_normSq_sum {n m : ℕ} (τ : ℝ)
    (rows : Fin m → Space n) (k : ℕ) (z : LensComplexSpace n) :
    (((lensPowerJacobian τ rows k z)ᴴ * lensPowerJacobian τ rows k z).det).re =
      ∑ s ∈ unsignedBasisIndices rows,
        normSq (Matrix.of fun i l => lensPowerJacobian τ rows k z (s i) l).det := by
  classical
  rw [lensPowerJacobian_gram_det, Complex.ofReal_re, lensWeightedGram_det_eq_unsigned_sum]
  exact Finset.sum_congr rfl (fun s _ => (lensPowerJacobian_minor_normSq τ rows k z s).symm)

/-- The upstream mass density uses n! times this exact unsigned minor sum. -/
theorem lensPower_massDensity_eq_factorial_unsigned_sum {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ)
    {z : LensComplexSpace n} (hz : z ∈ lensComplexDomain τ rows) :
    OAI.Mahler.massDensity (fun j => lensPowerComponent τ rows k j) z =
      ∑ s ∈ unsignedBasisIndices rows, (n.factorial : ℝ) *
        (∏ i, lensPowerWeight τ rows k z (s i)) *
          (Matrix.of fun i => rows (s i)).det ^ 2 := by
  classical
  rw [lensPower_massDensity_eq_factorial_gram hτ0 hτ1 rows k hz,
    lensWeightedGram_det_eq_unsigned_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => (mul_assoc _ _ _).symm)

/-- Every real minor-density summand is nonnegative. -/
theorem lensPower_minorDensity_nonneg {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n)
    (k : ℕ) (z : LensComplexSpace n) (s : Fin n → Fin m) :
    0 ≤ (n.factorial : ℝ) * (∏ i, lensPowerWeight τ rows k z (s i)) *
      (Matrix.of fun i => rows (s i)).det ^ 2 := by
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (Finset.prod_nonneg fun i _ => lensPowerWeight_nonneg τ rows k z (s i))) (sq_nonneg _)

/-- Passing to extended nonnegative reals preserves this finite density sum. -/
theorem lensPower_massDensity_ofReal_eq_unsigned_sum {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ)
    {z : LensComplexSpace n} (hz : z ∈ lensComplexDomain τ rows) :
    ENNReal.ofReal (OAI.Mahler.massDensity (fun j => lensPowerComponent τ rows k j) z) =
      ∑ s ∈ unsignedBasisIndices rows, ENNReal.ofReal ((n.factorial : ℝ) *
        (∏ i, lensPowerWeight τ rows k z (s i)) *
          (Matrix.of fun i => rows (s i)).det ^ 2) := by
  classical
  rw [lensPower_massDensity_eq_factorial_unsigned_sum hτ0 hτ1 rows k hz]
  exact ENNReal.ofReal_sum_of_nonneg fun s _ => lensPower_minorDensity_nonneg τ rows k z s

end
end Funk
