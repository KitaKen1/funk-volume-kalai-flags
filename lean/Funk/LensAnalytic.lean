import Funk.LensSeries
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-! Holomorphicity and the reported ODE for the actual infinite lens series.
The proof uses the Weierstrass theorem and mathlib's complex arctangent series.
It does not establish injectivity or identify the image boundary. -/

open Set Filter
open scoped Topology

namespace Funk

noncomputable section

theorem lensSeries_differentiableOn (b : ℝ) :
    DifferentiableOn ℂ (lensSeries b) {z : ℂ | ‖z‖ < 1} := by
  exact Complex.differentiableOn_tsum_of_summable_norm summable_lens_majorant
    (fun j z _ => (hasDerivAt_lensTerm b j z).differentiableAt.differentiableWithinAt)
    (isOpen_lt continuous_norm continuous_const)
    (fun j _ hz => norm_lensTerm_le b j hz.le)

theorem hasSum_deriv_lensTerm (b : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun j => deriv (lensTerm b j) z) (deriv (lensSeries b) z) := by
  exact Complex.hasSum_deriv_of_summable_norm summable_lens_majorant
    (fun j w _ => (hasDerivAt_lensTerm b j w).differentiableAt.differentiableWithinAt)
    (isOpen_lt continuous_norm continuous_const)
    (fun j _ hw => norm_lensTerm_le b j hw.le) hz

theorem lensSeries_ode (b : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    z * deriv (lensSeries b) z - (b : ℂ) * Complex.I * lensSeries b z =
      Complex.arctan z := by
  have h := ((hasSum_deriv_lensTerm b hz).mul_left z).sub
    ((summable_lensTerm b hz.le).hasSum.mul_left ((b : ℂ) * Complex.I))
  have heq : (fun j => z * deriv (lensTerm b j) z - (b : ℂ) * Complex.I * lensTerm b j z) =
      (fun j : ℕ => (-1 : ℂ) ^ j * z ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℂ)) := by
    funext j
    rw [(hasDerivAt_lensTerm b j z).deriv]
    exact lensTerm_ode b j z
  rw [heq] at h
  exact h.unique (Complex.hasSum_arctan hz)

theorem tiltedLens_differentiableOn (τ : ℝ) :
    DifferentiableOn ℂ (tiltedLens τ) {z : ℂ | ‖z‖ < 1} :=
  (lensSeries_differentiableOn _).const_mul _

/-- The ODE holds for the actual infinite series at every point of the open disk. -/
theorem tiltedLens_ode (τ : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    z * deriv (tiltedLens τ) z - (lensRate τ : ℂ) * Complex.I * tiltedLens τ z =
      (lensFactor τ : ℂ) * Complex.arctan z := by
  have hd : HasDerivAt (tiltedLens τ)
      ((lensFactor τ : ℂ) * deriv (lensSeries (lensRate τ)) z) z :=
    ((lensSeries_differentiableOn (lensRate τ)).differentiableAt
      ((isOpen_lt continuous_norm continuous_const).mem_nhds hz)).hasDerivAt.const_mul _
  rw [hd.deriv, tiltedLens]
  calc
    _ = (lensFactor τ : ℂ) * (z * deriv (lensSeries (lensRate τ)) z -
        (lensRate τ : ℂ) * Complex.I * lensSeries (lensRate τ) z) := by ring
    _ = _ := by rw [lensSeries_ode _ hz]

theorem tiltedLens_isCompact_image (τ : ℝ) :
    IsCompact ((tiltedLens τ) '' {z : ℂ | ‖z‖ ≤ 1}) := by
  have hs : IsCompact {z : ℂ | ‖z‖ ≤ 1} := by
    simpa only [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : ℂ) (1 : ℝ)
  exact hs.image_of_continuousOn (tiltedLens_continuousOn τ)

theorem tiltedLens_image_bounded (τ : ℝ) :
    Bornology.IsBounded ((tiltedLens τ) '' {z : ℂ | ‖z‖ ≤ 1}) :=
  (tiltedLens_isCompact_image τ).isBounded

end
end Funk
