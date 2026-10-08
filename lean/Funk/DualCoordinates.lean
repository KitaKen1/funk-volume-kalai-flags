import Funk.BasisDensityTransport
import Funk.FlagSimplex
import Mathlib.Analysis.Calculus.FDeriv.Add

/-! The affine dual coordinates u = 1 - Q x, with an explicit inverse,
constant Jacobian and exact set-integral change of variables. All measures
are the original product Lebesgue measure, without a surrogate normalization. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

def dualCoordinates {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) :
    Space n →ᵃ[ℝ] Space n :=
  AffineMap.const ℝ (Space n) (1 : Space n) - (basisMap Q).toLinearMap.toAffineMap

theorem dualCoordinates_apply {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (x : Space n) :
    dualCoordinates Q x = 1 - basisMap Q x := rfl

theorem dualCoordinates_component {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (x : Space n) (i : Fin n) : dualCoordinates Q x i = 1 - dotProduct (Q i) x := rfl

theorem continuous_dualCoordinates {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (dualCoordinates Q) :=
  continuous_const.sub (basisMap Q).continuous

theorem basisMap_neg {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) :
    basisMap (-Q) = -(basisMap Q) := by
  ext x i
  change dotProduct (-(Q i)) x = -dotProduct (Q i) x
  exact neg_dotProduct _ _

theorem hasFDerivAt_dualCoordinates {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (x : Space n) :
    HasFDerivAt (dualCoordinates Q) (basisMap (-Q)) x := by
  rw [basisMap_neg]
  exact (basisMap Q).hasFDerivAt.const_sub (1 : Space n)

theorem abs_det_dualCoordinates_derivative {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) :
    |(basisMap (-Q)).det| = |Q.det| := by
  rw [basisMap_det, Matrix.det_neg, abs_mul, abs_pow]
  simp

theorem basisMap_inverse_left {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.det ≠ 0) (x : Space n) : basisMap Q⁻¹ (basisMap Q x) = x := by
  change Q⁻¹.mulVec (Q.mulVec x) = x
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.mpr hQ),
    Matrix.one_mulVec]

theorem basisMap_inverse_right {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.det ≠ 0) (x : Space n) : basisMap Q (basisMap Q⁻¹ x) = x := by
  change Q.mulVec (Q⁻¹.mulVec x) = x
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hQ),
    Matrix.one_mulVec]

def dualCoordinatesInverse {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (u : Space n) : Space n :=
  basisMap Q⁻¹ (1 - u)

theorem dualCoordinates_left_inverse {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.det ≠ 0) (x : Space n) : dualCoordinatesInverse Q (dualCoordinates Q x) = x := by
  simp only [dualCoordinatesInverse, dualCoordinates_apply, sub_sub_cancel]
  exact basisMap_inverse_left hQ x

theorem dualCoordinates_right_inverse {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.det ≠ 0) (u : Space n) : dualCoordinates Q (dualCoordinatesInverse Q u) = u := by
  rw [dualCoordinates_apply, dualCoordinatesInverse, basisMap_inverse_right hQ]
  simp

theorem dualCoordinates_injective {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.det ≠ 0) : Function.Injective (dualCoordinates Q) :=
  Function.HasLeftInverse.injective ⟨dualCoordinatesInverse Q, dualCoordinates_left_inverse hQ⟩

theorem dualCoordinates_surjective {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.det ≠ 0) : Function.Surjective (dualCoordinates Q) :=
  Function.HasRightInverse.surjective ⟨dualCoordinatesInverse Q, dualCoordinates_right_inverse hQ⟩

theorem measurableSet_dualCoordinates_image {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.det ≠ 0) {s : Set (Space n)} (hs : MeasurableSet s) :
    MeasurableSet (dualCoordinates Q '' s) :=
  measurable_image_of_fderivWithin hs
    (fun x _ => (hasFDerivAt_dualCoordinates Q x).hasFDerivWithinAt)
    (dualCoordinates_injective hQ).injOn

/-- The actual affine Jacobian, for every measurable region and every nonnegative kernel. -/
theorem lintegral_dualCoordinates_image {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.det ≠ 0) {s : Set (Space n)} (hs : MeasurableSet s) (g : Space n → ℝ≥0∞) :
    ∫⁻ u in dualCoordinates Q '' s, g u =
      ∫⁻ x in s, ENNReal.ofReal |Q.det| * g (dualCoordinates Q x) := by
  simpa only [abs_det_dualCoordinates_derivative] using
    lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure (Space n)) hs
      (fun x _ => (hasFDerivAt_dualCoordinates Q x).hasFDerivWithinAt)
      (dualCoordinates_injective hQ).injOn g

def dualProductKernel {n : ℕ} (u : Space n) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / ((n.factorial : ℝ) * ∏ i, u i))

theorem measurable_dualProductKernel (n : ℕ) : Measurable (@dualProductKernel n) := by
  unfold dualProductKernel
  fun_prop

theorem determinant_mul_dualProductKernel {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (x : Space n) :
    ENNReal.ofReal |Q.det| * dualProductKernel (dualCoordinates Q x) =
      ENNReal.ofReal (|Q.det| / ((∏ i, (1 - dotProduct (Q i) x)) * (n.factorial : ℝ))) := by
  unfold dualProductKernel
  simp only [dualCoordinates_component]
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  ring

/-- Exact denominator transport. Positivity is checked separately on the geometric domains. -/
theorem lintegral_denominator_eq_dualCoordinates {n : ℕ}
    {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.det ≠ 0)
    {s : Set (Space n)} (hs : MeasurableSet s) :
    (∫⁻ x in s, ENNReal.ofReal (|Q.det| /
      ((∏ i, (1 - dotProduct (Q i) x)) * (n.factorial : ℝ)))) =
      ∫⁻ u in dualCoordinates Q '' s, dualProductKernel u := by
  rw [lintegral_dualCoordinates_image hQ hs]
  apply setLIntegral_congr_fun hs
  intro x _
  exact (determinant_mul_dualProductKernel Q x).symm

end
end Funk
