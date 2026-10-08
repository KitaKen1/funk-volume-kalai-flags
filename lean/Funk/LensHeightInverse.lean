import Funk.LensBoundaryHeight
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! An explicit inverse for the known height of the actual right lens arc.
The logarithm is only differentiated where its argument is strictly positive. -/

open Set

namespace Funk
noncomputable section

def lensHeightAngle (τ y : ℝ) : ℝ :=
  -Real.log ((1 - τ * y) / lensScale τ) / lensRate τ

theorem lensHeight_margin_pos_of_le_one {τ y : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hy : y ≤ 1) : 0 < 1 - τ * y := by
  have := mul_le_mul_of_nonneg_left hy hτ0.le
  nlinarith

theorem lensHeightAngle_tiltedHeight {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (θ : ℝ) :
    lensHeightAngle τ (tiltedHeight τ θ) = θ := by
  have hb := (lensRate_pos hτ0 hτ1).ne'
  have hc := (lensScale_pos hτ0 hτ1).ne'
  have he : (1 - τ * tiltedHeight τ θ) / lensScale τ =
      Real.exp (-lensRate τ * θ) := by
    dsimp [tiltedHeight, lensHeight]
    field_simp
    ring
  rw [lensHeightAngle, he, Real.log_exp]
  field_simp

theorem tiltedHeight_lensHeightAngle {τ y : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hy : 0 < 1 - τ * y) : tiltedHeight τ (lensHeightAngle τ y) = y := by
  have hb := (lensRate_pos hτ0 hτ1).ne'
  have hc := (lensScale_pos hτ0 hτ1).ne'
  have hp : 0 < (1 - τ * y) / lensScale τ := div_pos hy (lensScale_pos hτ0 hτ1)
  have he : -lensRate τ * lensHeightAngle τ y =
      Real.log ((1 - τ * y) / lensScale τ) := by
    dsimp [lensHeightAngle]
    field_simp
  dsimp [tiltedHeight, lensHeight]
  rw [he, Real.exp_log hp]
  field_simp
  ring

theorem lensHeightAngle_left {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    lensHeightAngle τ (-1) = -Real.pi / 2 := by
  rw [← tiltedHeight_left hτ0 hτ1, lensHeightAngle_tiltedHeight hτ0 hτ1]

theorem lensHeightAngle_right {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    lensHeightAngle τ 1 = Real.pi / 2 := by
  rw [← tiltedHeight_right hτ0 hτ1, lensHeightAngle_tiltedHeight hτ0 hτ1]

theorem lensHeightAngle_strictMonoOn {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    StrictMonoOn (lensHeightAngle τ) (Iic 1) := by
  intro x hx y hy hxy
  apply (tiltedHeight_strictMono hτ0 hτ1).lt_iff_lt.mp
  simpa only [tiltedHeight_lensHeightAngle hτ0 hτ1
    (lensHeight_margin_pos_of_le_one hτ0 hτ1 hx),
    tiltedHeight_lensHeightAngle hτ0 hτ1
    (lensHeight_margin_pos_of_le_one hτ0 hτ1 hy)] using hxy

theorem lensHeightAngle_mem_Icc {τ y : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hy : y ∈ Icc (-1) 1) : lensHeightAngle τ y ∈ Icc (-Real.pi / 2) (Real.pi / 2) := by
  have hm := (lensHeightAngle_strictMonoOn hτ0 hτ1).monotoneOn
  constructor
  · rw [← lensHeightAngle_left hτ0 hτ1]
    exact hm (by norm_num) hy.2 hy.1
  · rw [← lensHeightAngle_right hτ0 hτ1]
    exact hm hy.2 (by simp) hy.2

theorem lensHeightAngle_mem_Ioo {τ y : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hy : y ∈ Ioo (-1) 1) : lensHeightAngle τ y ∈ Ioo (-Real.pi / 2) (Real.pi / 2) := by
  have hm := lensHeightAngle_strictMonoOn hτ0 hτ1
  constructor
  · rw [← lensHeightAngle_left hτ0 hτ1]
    exact hm (by norm_num) hy.2.le hy.1
  · rw [← lensHeightAngle_right hτ0 hτ1]
    exact hm hy.2.le (by simp) hy.2

theorem lensHeightAngle_continuousAt {τ y : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hy : 0 < 1 - τ * y) : ContinuousAt (lensHeightAngle τ) y := by
  have hc := lensScale_pos hτ0 hτ1
  unfold lensHeightAngle
  exact (((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).div_const _).log
    (div_pos hy hc).ne').neg.div_const _

theorem lensHeightAngle_continuousOn {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ContinuousOn (lensHeightAngle τ) (Icc (-1) 1) := by
  intro y hy
  exact (lensHeightAngle_continuousAt hτ0 hτ1
    (lensHeight_margin_pos_of_le_one hτ0 hτ1 hy.2)).continuousWithinAt

theorem hasDerivAt_lensHeightAngle {τ y : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hy : 0 < 1 - τ * y) :
    HasDerivAt (lensHeightAngle τ) (τ / (lensRate τ * (1 - τ * y))) y := by
  have hc := (lensScale_pos hτ0 hτ1).ne'
  have hd := (((hasDerivAt_const y (1 : ℝ)).sub
    ((hasDerivAt_id y).const_mul τ)).div_const (lensScale τ)).log
      (div_pos hy (lensScale_pos hτ0 hτ1)).ne'
  convert hd.neg.div_const (lensRate τ) using 1
  · rfl
  · dsimp
    field_simp
    ring

theorem exp_lensHeightAngle {τ y : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hy : 0 < 1 - τ * y) :
    Real.exp (lensRate τ * lensHeightAngle τ y) = lensScale τ / (1 - τ * y) := by
  have hb := (lensRate_pos hτ0 hτ1).ne'
  have he : lensRate τ * lensHeightAngle τ y =
      -Real.log ((1 - τ * y) / lensScale τ) := by
    dsimp [lensHeightAngle]
    field_simp
  rw [he, Real.exp_neg, Real.exp_log (div_pos hy (lensScale_pos hτ0 hτ1)), inv_div]

end
end Funk
