import Funk.LensPowerLeading
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Convexity and Schwarz contraction for the actual tilted lens.
The analytic radial ratio is regularized at zero by a divided slope. -/

open Set Metric Filter Complex
open scoped Topology

namespace Funk
noncomputable section

theorem lensInterior_real_smul_mem {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {w : ℂ} (hw : w ∈ interior (lensGraphBody τ)) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : (s : ℂ) * w ∈ interior (lensGraphBody τ) := by
  have h := (lensGraphBody_convex hτ0 hτ1).interior
    (lensGraphBody_zero_mem_interior hτ0 hτ1) hw
    (show 0 ≤ 1-s by linarith) hs0 (by ring : (1-s)+s=1)
  simpa only [smul_zero, zero_add, Complex.real_smul] using h

theorem tiltedLensInverse_radial_contraction {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {u : ℂ} (hu : u ∈ ball 0 1) :
    ‖tiltedLensInverse τ ((s : ℂ) * tiltedLens τ u)‖ ≤ ‖u‖ := by
  let h : ℂ → ℂ := fun z => tiltedLensInverse τ ((s : ℂ) * tiltedLens τ z)
  have hm : ∀ z ∈ ball (0 : ℂ) 1,
      (s : ℂ) * tiltedLens τ z ∈ interior (lensGraphBody τ) := fun z hz =>
    lensInterior_real_smul_mem hτ0 hτ1 (tiltedLens_mapsTo_ball_interior hτ0 hτ1 hz) hs0 hs1
  have hd : DifferentiableOn ℂ h (ball 0 1) := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    exact ((tiltedLensInverse_analyticOnNhd hτ0 hτ1 _ (hm z hz)).differentiableAt).comp z
      (((tiltedLens_diffContOnCl τ).differentiableOn.differentiableAt
        (isOpen_ball.mem_nhds hz)).const_mul (s : ℂ))
  have hmaps : MapsTo h (ball 0 1) (closedBall 0 1) := fun z hz =>
    ball_subset_closedBall (tiltedLensInverse_mem_ball hτ0 hτ1 (hm z hz))
  exact Complex.norm_le_norm_of_mapsTo_ball hd hmaps
    (by simp [h, tiltedLens_zero, tiltedLensInverse_zero hτ0 hτ1])
    (mem_ball_zero_iff.mp hu)

/-- The derivative of the squared complex norm along a real parameter. -/
theorem lens_hasDerivAt_normSq {f : ℝ → ℂ} {f' : ℂ} {t : ℝ}
    (hf : HasDerivAt f f' t) :
    HasDerivAt (fun x => Complex.normSq (f x))
      (2 * ((f t).re * f'.re + (f t).im * f'.im)) t := by
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hf
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hf
  convert (hr.pow 2).add (hi.pow 2) using 1
  · ext x
    simp [Complex.normSq_apply, pow_two]
  · simp only [Complex.reCLM_apply, Complex.imCLM_apply]
    norm_num
    ring

/-- The radial analytic ratio F(u)/(u F'(u)), with its value at zero filled in. -/
def lensRadialRatio (τ : ℝ) (u : ℂ) : ℂ :=
  dslope (tiltedLens τ) 0 u / deriv (tiltedLens τ) u

theorem lensRadialRatio_zero {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    lensRadialRatio τ 0 = 1 := by
  simp only [lensRadialRatio, dslope_same]
  exact div_self (tiltedLens_deriv_ne_zero hτ0 hτ1 (by norm_num))

theorem tiltedLens_eq_mul_dslope (τ : ℝ) (u : ℂ) :
    tiltedLens τ u = u * dslope (tiltedLens τ) 0 u := by
  simpa only [sub_zero, smul_eq_mul, tiltedLens_zero] using
    (sub_smul_dslope (tiltedLens τ) (0 : ℂ) u).symm

theorem lensRadialRatio_analyticOnNhd {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    AnalyticOnNhd ℂ (lensRadialRatio τ) (ball 0 1) := by
  have hF := (tiltedLens_diffContOnCl τ).differentiableOn.analyticOnNhd isOpen_ball
  intro u hu
  have hs : AnalyticAt ℂ (dslope (tiltedLens τ) 0) u := by
    by_cases hu0 : u = 0
    · subst u
      obtain ⟨p, hp⟩ := hF 0 (by simp)
      exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
    · have hd : AnalyticAt ℂ (fun z : ℂ => (tiltedLens τ z - tiltedLens τ 0) / (z-0)) u :=
        ((hF u hu).sub analyticAt_const).div
          (analyticAt_id.sub analyticAt_const) (by simpa using hu0)
      apply hd.congr
      filter_upwards [eventually_ne_nhds hu0] with z hz
      simp [dslope_of_ne _ hz, slope_def_module, div_eq_inv_mul]
  exact hs.div (hF.deriv u hu) (tiltedLens_deriv_ne_zero hτ0 hτ1 (mem_ball_zero_iff.mp hu))

end
end Funk
