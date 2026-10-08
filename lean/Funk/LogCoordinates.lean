import Funk.DualCoordinates
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-! Coordinatewise exponentiation removes the reciprocal-product kernel.
The change of variables is for the actual product Lebesgue measure. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

def expCoordinates {n : ℕ} (z : Space n) : Space n := fun i => Real.exp (z i)
def logCoordinates {n : ℕ} (u : Space n) : Space n := fun i => Real.log (u i)

theorem expCoordinates_pos {n : ℕ} (z : Space n) (i : Fin n) :
    0 < expCoordinates z i := Real.exp_pos _

theorem logCoordinates_expCoordinates {n : ℕ} (z : Space n) :
    logCoordinates (expCoordinates z) = z := by
  ext i
  exact Real.log_exp _

theorem expCoordinates_logCoordinates {n : ℕ} {u : Space n}
    (hu : ∀ i, 0 < u i) : expCoordinates (logCoordinates u) = u := by
  ext i
  exact Real.exp_log (hu i)

theorem expCoordinates_injective (n : ℕ) : Function.Injective (@expCoordinates n) :=
  Function.HasLeftInverse.injective ⟨logCoordinates, logCoordinates_expCoordinates⟩

theorem continuous_expCoordinates (n : ℕ) : Continuous (@expCoordinates n) := by
  unfold expCoordinates
  fun_prop

theorem measurable_logCoordinates (n : ℕ) : Measurable (@logCoordinates n) := by
  unfold logCoordinates
  fun_prop

theorem hasFDerivAt_expCoordinates {n : ℕ} (z : Space n) :
    HasFDerivAt expCoordinates (basisMap (Matrix.diagonal (expCoordinates z))) z := by
  apply hasFDerivAt_pi''
  intro i
  have he : (ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ).comp
      (basisMap (Matrix.diagonal (expCoordinates z))) =
      Real.exp (z i) • (ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ) := by
    ext x
    change (Matrix.diagonal (expCoordinates z)).mulVec x i = Real.exp (z i) * x i
    rw [Matrix.mulVec_diagonal]
    rfl
  rw [he]
  exact (hasFDerivAt_apply (𝕜 := ℝ) i z).exp

theorem det_expCoordinates_derivative {n : ℕ} (z : Space n) :
    (basisMap (Matrix.diagonal (expCoordinates z))).det = ∏ i, expCoordinates z i := by
  rw [basisMap_det, Matrix.det_diagonal]

theorem expCoordinates_jacobian_pos {n : ℕ} (z : Space n) :
    0 < ∏ i, expCoordinates z i :=
  Finset.prod_pos (fun i _ => expCoordinates_pos z i)

theorem expCoordinates_jacobian_mul_kernel {n : ℕ} (z : Space n) :
    ENNReal.ofReal |(basisMap (Matrix.diagonal (expCoordinates z))).det| *
      dualProductKernel (expCoordinates z) = ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  rw [det_expCoordinates_derivative, abs_of_pos (expCoordinates_jacobian_pos z)]
  unfold dualProductKernel
  rw [← ENNReal.ofReal_mul (expCoordinates_jacobian_pos z).le]
  congr 1
  have hp := ne_of_gt (expCoordinates_jacobian_pos z)
  field_simp

theorem measurableSet_expCoordinates_image {n : ℕ} {s : Set (Space n)}
    (hs : MeasurableSet s) : MeasurableSet (expCoordinates '' s) :=
  measurable_image_of_fderivWithin hs
    (fun z _ => (hasFDerivAt_expCoordinates z).hasFDerivWithinAt)
    (expCoordinates_injective n).injOn

/-- Exact flattening of the actual reciprocal-product integral. -/
theorem lintegral_expCoordinates_kernel {n : ℕ} {s : Set (Space n)}
    (hs : MeasurableSet s) :
    (∫⁻ u in expCoordinates '' s, dualProductKernel u) =
      ENNReal.ofReal (1 / (n.factorial : ℝ)) * volume s := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure (Space n)) hs
    (fun z _ => (hasFDerivAt_expCoordinates z).hasFDerivWithinAt)
    (expCoordinates_injective n).injOn]
  simp_rw [expCoordinates_jacobian_mul_kernel]
  simp

/-- Positivity, rather than an unverified surjectivity assumption, supplies the inverse. -/
theorem expCoordinates_image_preimage {n : ℕ} {s : Set (Space n)}
    (hs : ∀ u ∈ s, ∀ i, 0 < u i) : expCoordinates '' (expCoordinates ⁻¹' s) = s := by
  apply Set.Subset.antisymm (Set.image_preimage_subset _ _)
  intro u hu
  refine ⟨logCoordinates u, ?_, expCoordinates_logCoordinates (hs u hu)⟩
  change expCoordinates (logCoordinates u) ∈ s
  rwa [expCoordinates_logCoordinates (hs u hu)]

theorem preimage_expCoordinates_eq_log_image {n : ℕ} {s : Set (Space n)}
    (hs : ∀ u ∈ s, ∀ i, 0 < u i) : expCoordinates ⁻¹' s = logCoordinates '' s := by
  ext z
  constructor
  · intro hz
    exact ⟨expCoordinates z, hz, logCoordinates_expCoordinates z⟩
  · rintro ⟨u, hu, rfl⟩
    change expCoordinates (logCoordinates u) ∈ s
    rwa [expCoordinates_logCoordinates (hs u hu)]

end
end Funk
