import Funk.LensHeightInverse
import Funk.LensArcSeparation
import Mathlib.Analysis.Convex.Deriv

/-! The actual right boundary arc, parametrized by its height, is strictly
concave after subtracting the endpoint chord.  Its derivative is a positive
constant times the already verified decreasing weighted angular derivative. -/

open Set

namespace Funk
noncomputable section

def lensProfile (τ y : ℝ) : ℝ :=
  lensChordCoordinate τ (lensRadialTrace τ 1 (lensHeightAngle τ y))

theorem lensProfile_tiltedHeight {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (θ : ℝ) :
    lensProfile τ (tiltedHeight τ θ) = lensChordCoordinate τ (lensRadialTrace τ 1 θ) := by
  rw [lensProfile, lensHeightAngle_tiltedHeight hτ0 hτ1]

theorem lensProfile_continuousOn {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ContinuousOn (lensProfile τ) (Icc (-1) 1) :=
  ((lensChordCoordinate_continuous τ).comp (lensBoundary_continuous τ)).comp_continuousOn
    (lensHeightAngle_continuousOn hτ0 hτ1)

theorem lensProfile_endpoints {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    lensProfile τ (-1) = 0 ∧ lensProfile τ 1 = 0 := by
  simpa only [lensProfile, lensHeightAngle_left hτ0 hτ1,
    lensHeightAngle_right hτ0 hτ1] using lensChordCoordinate_endpoints hτ0 hτ1

theorem lensProfile_pos {τ y : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hy : y ∈ Ioo (-1) 1) : 0 < lensProfile τ y :=
  lensChordCoordinate_pos hτ0 hτ1 (lensHeightAngle_mem_Ioo hτ0 hτ1 hy)

theorem lensProfile_nonneg {τ y : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hy : y ∈ Icc (-1) 1) : 0 ≤ lensProfile τ y :=
  lensChordCoordinate_nonneg hτ0 hτ1 (lensHeightAngle_mem_Icc hτ0 hτ1 hy)

theorem hasDerivAt_lensProfile {τ y : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hy : y ∈ Ioo (-1) 1) :
    HasDerivAt (lensProfile τ)
      (τ / (lensRate τ * lensScale τ) *
        (Real.exp (lensRate τ * lensHeightAngle τ y) *
          lensChordField τ (lensHeightAngle τ y))) y := by
  have hθ := lensHeightAngle_mem_Ioo hτ0 hτ1 hy
  have hm := lensHeight_margin_pos_of_le_one hτ0 hτ1 hy.2.le
  have hd := (hasDerivAt_lensChord τ
    (Real.cos_pos_of_mem_Ioo (by simpa [neg_div] using hθ))).comp y
      (hasDerivAt_lensHeightAngle hτ0 hτ1 hm)
  convert hd using 1
  · rfl
  · rw [exp_lensHeightAngle hτ0 hτ1 hm]
    have hb := (lensRate_pos hτ0 hτ1).ne'
    have hc := (lensScale_pos hτ0 hτ1).ne'
    field_simp

theorem lensProfile_deriv_strictAntiOn {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    StrictAntiOn (deriv (lensProfile τ)) (Ioo (-1) 1) := by
  intro x hx y hy hxy
  rw [(hasDerivAt_lensProfile hτ0 hτ1 hx).deriv,
    (hasDerivAt_lensProfile hτ0 hτ1 hy).deriv]
  apply mul_lt_mul_of_pos_left
    (lensWeightedChordField_strictAntiOn hτ0 hτ1
      (lensHeightAngle_mem_Ioo hτ0 hτ1 hx) (lensHeightAngle_mem_Ioo hτ0 hτ1 hy)
      (lensHeightAngle_strictMonoOn hτ0 hτ1 hx.2.le hy.2.le hxy))
  exact div_pos hτ0 (mul_pos (lensRate_pos hτ0 hτ1) (lensScale_pos hτ0 hτ1))

/-- Strict concavity includes the two singular angular endpoints by continuity. -/
theorem lensProfile_strictConcaveOn {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    StrictConcaveOn ℝ (Icc (-1) 1) (lensProfile τ) := by
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Icc _ _)
    (lensProfile_continuousOn hτ0 hτ1)
  simpa only [interior_Icc] using lensProfile_deriv_strictAntiOn hτ0 hτ1

theorem lensProfile_concaveOn {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ConcaveOn ℝ (Icc (-1) 1) (lensProfile τ) :=
  (lensProfile_strictConcaveOn hτ0 hτ1).concaveOn

end
end Funk
