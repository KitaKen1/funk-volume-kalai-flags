import Funk.LensConcavity
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! Actual height coordinates and strict second curvature of the right arc.
The angle is analytic; this file does not assert analyticity of the boundary
profile or nullity of a multivariable collision set. -/

open Set Filter
open scoped Topology

namespace Funk
noncomputable section

theorem lensHeightAngle_analyticAt {τ y : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hy : 0 < 1 - τ * y) : AnalyticAt ℝ (lensHeightAngle τ) y := by
  unfold lensHeightAngle
  apply AnalyticAt.div_const
  apply AnalyticAt.neg
  apply AnalyticAt.log
  · exact (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).div_const
  · exact div_pos hy (lensScale_pos hτ0 hτ1)

theorem lensHeightAngle_analyticOnNhd {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    AnalyticOnNhd ℝ (lensHeightAngle τ) (Ioo (-1) 1) :=
  fun _ hy => lensHeightAngle_analyticAt hτ0 hτ1
    (lensHeight_margin_pos_of_le_one hτ0 hτ1 hy.2.le)

/-- The formula is kept factored so that every sign has a geometric source. -/
def lensProfileCurvature (τ y : ℝ) : ℝ :=
  (τ / (lensRate τ * lensScale τ)) *
    (Real.exp (lensRate τ * lensHeightAngle τ y) *
      (-lensFactor τ / (2 * Real.cos (lensHeightAngle τ y)))) *
    (τ / (lensRate τ * (1 - τ * y)))

theorem hasDerivAt_lensProfile_deriv {τ y : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hy : y ∈ Ioo (-1) 1) :
    HasDerivAt (deriv (lensProfile τ)) (lensProfileCurvature τ y) y := by
  have hm := lensHeight_margin_pos_of_le_one hτ0 hτ1 hy.2.le
  have hθ := lensHeightAngle_mem_Ioo hτ0 hτ1 hy
  have hc := Real.cos_pos_of_mem_Ioo (by simpa [neg_div] using hθ)
  have hd := ((hasDerivAt_lensWeightedChordField τ hc).comp y
    (hasDerivAt_lensHeightAngle hτ0 hτ1 hm)).const_mul
      (τ / (lensRate τ * lensScale τ))
  have he : deriv (lensProfile τ) =ᶠ[𝓝 y]
      (fun u => τ / (lensRate τ * lensScale τ) *
        (Real.exp (lensRate τ * lensHeightAngle τ u) *
          lensChordField τ (lensHeightAngle τ u))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with u hu
    exact (hasDerivAt_lensProfile hτ0 hτ1 hu).deriv
  convert hd.congr_of_eventuallyEq he using 1
  simp only [lensProfileCurvature, mul_assoc]

theorem lensProfileCurvature_neg {τ y : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hy : y ∈ Ioo (-1) 1) : lensProfileCurvature τ y < 0 := by
  have hb := lensRate_pos hτ0 hτ1
  have hc := lensScale_pos hτ0 hτ1
  have hθ := lensHeightAngle_mem_Ioo hτ0 hτ1 hy
  have hcos := Real.cos_pos_of_mem_Ioo (by simpa [neg_div] using hθ)
  unfold lensProfileCurvature
  apply mul_neg_of_neg_of_pos
  · apply mul_neg_of_pos_of_neg (div_pos hτ0 (mul_pos hb hc))
    apply mul_neg_of_pos_of_neg (Real.exp_pos _)
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (lensFactor_pos hτ0 hτ1))
      (mul_pos (by norm_num) hcos)
  · exact div_pos hτ0 (mul_pos hb
      (lensHeight_margin_pos_of_le_one hτ0 hτ1 hy.2.le))

theorem lensProfile_second_deriv_neg {τ y : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hy : y ∈ Ioo (-1) 1) : deriv (deriv (lensProfile τ)) y < 0 := by
  rw [(hasDerivAt_lensProfile_deriv hτ0 hτ1 hy).deriv]
  exact lensProfileCurvature_neg hτ0 hτ1 hy

end
end Funk
