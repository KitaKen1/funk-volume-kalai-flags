import Funk.LensPowerDerivative
import Mathlib.Algebra.Order.Star.Real

/-! The actual derivative Gram matrix is a real weighted row Gram matrix.
Every selected minor has its exact real determinant-squared and weight product. -/

open Matrix Complex
open scoped BigOperators

namespace Funk
noncomputable section

/-- The real Gram matrix with an arbitrary nonnegative row weight. -/
def lensWeightedGram {n m : ℕ} (rows : Fin m → Space n) (c : Fin m → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := (Matrix.of rows).transpose * diagonal c * Matrix.of rows

theorem lensWeightedGram_apply {n m : ℕ} (rows : Fin m → Space n) (c : Fin m → ℝ)
    (i l : Fin n) : lensWeightedGram rows c i l = ∑ j, rows j i * c j * rows j l := by
  unfold lensWeightedGram
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.of_apply]

theorem lensWeightedGram_posSemidef {n m : ℕ} (rows : Fin m → Space n)
    {c : Fin m → ℝ} (hc : ∀ j, 0 ≤ c j) : (lensWeightedGram rows c).PosSemidef := by
  simpa only [lensWeightedGram, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.posSemidef_diagonal_iff.mpr hc).conjTranspose_mul_mul_same (Matrix.of rows)

theorem lensWeightedGram_det_nonneg {n m : ℕ} (rows : Fin m → Space n)
    {c : Fin m → ℝ} (hc : ∀ j, 0 ≤ c j) : 0 ≤ (lensWeightedGram rows c).det :=
  (lensWeightedGram_posSemidef rows hc).det_nonneg

/-- No abstract Jacobian is supplied: this matrix comes from the actual fderiv. -/
theorem lensPowerJacobian_gram {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n)
    (k : ℕ) (z : LensComplexSpace n) :
    (lensPowerJacobian τ rows k z)ᴴ * lensPowerJacobian τ rows k z =
      (lensWeightedGram rows (lensPowerWeight τ rows k z)).map (algebraMap ℝ ℂ) := by
  ext i l
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, lensPowerJacobian,
    Matrix.map_apply, lensWeightedGram_apply, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro j _
  change star (lensPowerRowFactor τ rows k z j * (rows j i : ℂ)) *
      (lensPowerRowFactor τ rows k z j * (rows j l : ℂ)) =
    (rows j i : ℂ) * (normSq (lensPowerRowFactor τ rows k z j) : ℂ) * (rows j l : ℂ)
  rw [normSq_eq_conj_mul_self]
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

theorem lensPowerJacobian_gram_det {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n)
    (k : ℕ) (z : LensComplexSpace n) :
    ((lensPowerJacobian τ rows k z)ᴴ * lensPowerJacobian τ rows k z).det =
      ((lensWeightedGram rows (lensPowerWeight τ rows k z)).det : ℂ) := by
  rw [lensPowerJacobian_gram]
  exact (RingHom.map_det (algebraMap ℝ ℂ)
    (lensWeightedGram rows (lensPowerWeight τ rows k z))).symm

theorem lensPowerJacobian_gram_det_re_nonneg {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n)
    (k : ℕ) (z : LensComplexSpace n) :
    0 ≤ (((lensPowerJacobian τ rows k z)ᴴ * lensPowerJacobian τ rows k z).det).re := by
  rw [lensPowerJacobian_gram_det, Complex.ofReal_re]
  exact lensWeightedGram_det_nonneg rows (lensPowerWeight_nonneg τ rows k z)

/-- Exact factorization for any row selection, including singular selections. -/
theorem lensPowerJacobian_minor_det {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n)
    (k : ℕ) (z : LensComplexSpace n) (s : Fin n → Fin m) :
    (Matrix.of fun i l => lensPowerJacobian τ rows k z (s i) l).det =
      (∏ i, lensPowerRowFactor τ rows k z (s i)) *
      ((Matrix.of fun i => rows (s i)).det : ℂ) := by
  have h := Matrix.det_mul_column (fun i => lensPowerRowFactor τ rows k z (s i))
    (Matrix.of fun i l => (rows (s i) l : ℂ))
  exact h.trans (congrArg (fun a => (∏ i, lensPowerRowFactor τ rows k z (s i)) * a)
    (RingHom.map_det (algebraMap ℝ ℂ) (Matrix.of fun i => rows (s i))).symm)

/-- The real determinant is squared, rather than its absolute value or first power. -/
theorem lensPowerJacobian_minor_normSq {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n)
    (k : ℕ) (z : LensComplexSpace n) (s : Fin n → Fin m) :
    normSq (Matrix.of fun i l => lensPowerJacobian τ rows k z (s i) l).det =
      (∏ i, lensPowerWeight τ rows k z (s i)) *
      (Matrix.of fun i => rows (s i)).det ^ 2 := by
  rw [lensPowerJacobian_minor_det, normSq_mul, map_prod, normSq_ofReal]
  simp only [lensPowerWeight, pow_two]

theorem lensPowerJacobian_minor_zero_of_singular {n m : ℕ} (τ : ℝ)
    (rows : Fin m → Space n) (k : ℕ) (z : LensComplexSpace n) (s : Fin n → Fin m)
    (hs : (Matrix.of fun i => rows (s i)).det = 0) :
    (Matrix.of fun i l => lensPowerJacobian τ rows k z (s i) l).det = 0 := by
  rw [lensPowerJacobian_minor_det, hs, Complex.ofReal_zero, mul_zero]

end
end Funk
