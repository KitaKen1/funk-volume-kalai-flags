import Funk.LensJetBoundary
import Funk.LensDiskImage
import Funk.HalfPlane
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-! The regularized derivative has positive real part in the open disk.
Consequently the actual lens map has no critical points and admits an analytic
local inverse at every interior point. -/

open Set Metric Filter
open scoped Topology

namespace Funk
noncomputable section

theorem tiltedLensJet_re_nonneg_circle {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {z : ℂ} (hz : ‖z‖ = 1) : 0 ≤ (tiltedLensJet τ z).re := by
  have hz' : z ∈ circleMap 0 1 '' Ioc (-Real.pi / 2) (3 * Real.pi / 2) := by
    rw [circleMap_image_lens_period]
    exact hz
  obtain ⟨θ, hθ, rfl⟩ := hz'
  by_cases h : θ ≤ Real.pi / 2
  · exact tiltedLensJet_boundary_re_nonneg hτ0 hτ1 ⟨hθ.1.le, h⟩
  · have he : circleMap 0 1 θ = -circleMap 0 1 (θ - Real.pi) := by
      have hh : circleMap 0 1 ((θ - Real.pi) + Real.pi) =
          -circleMap 0 1 (θ - Real.pi) := by
        apply Complex.ext <;> simp [circleMap_zero_re, circleMap_zero_im]
      simpa only [sub_add_cancel] using hh
    rw [he, tiltedLensJet_neg]
    exact tiltedLensJet_boundary_re_nonneg hτ0 hτ1 ⟨by linarith, by linarith [hθ.2]⟩

theorem tiltedLensJet_diffContOnCl (τ : ℝ) :
    DiffContOnCl ℂ (tiltedLensJet τ) (ball 0 1) := by
  apply DiffContOnCl.mk_ball
  · simpa only [ball, dist_zero_right] using tiltedLensJet_differentiableOn τ
  · simpa only [closedBall, dist_zero_right] using tiltedLensJet_continuousOn τ

theorem tiltedLensJet_re_nonneg {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : 0 ≤ (tiltedLensJet τ z).re := by
  apply holomorphic_mem_closed_convex_of_frontier
    (K := {w : ℂ | 0 ≤ w.re}) (isBounded_ball (x := (0 : ℂ)) (r := 1))
    (tiltedLensJet_diffContOnCl τ)
    ((convex_Ici (0 : ℝ)).linear_preimage Complex.reCLM.toLinearMap)
    (isClosed_le continuous_const Complex.continuous_re)
  · intro w hw
    exact tiltedLensJet_re_nonneg_circle hτ0 hτ1 (by
      simpa [frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hw)
  · simpa [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hz

theorem tiltedLensJet_zero_re_pos {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    0 < (tiltedLensJet τ 0).re := by
  have hk := lensFactor_pos hτ0 hτ1
  have hd : 0 < Complex.normSq (1 - (lensRate τ : ℂ) * Complex.I) :=
    Complex.normSq_pos.mpr (by simpa using lens_denominator_ne_zero (lensRate τ) 0)
  have hr : 0 < (1 / (1 - (lensRate τ : ℂ) * Complex.I) : ℂ).re := by
    rw [one_div, Complex.inv_re]
    simpa using div_pos (by norm_num : (0 : ℝ) < 1) hd
  simpa only [tiltedLensJet, lensJet_zero, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] using mul_pos hk hr

theorem tiltedLensJet_re_pos {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {z : ℂ} (hz : ‖z‖ < 1) : 0 < (tiltedLensJet τ z).re := by
  exact re_pos_of_nonneg_on_connected isOpen_ball (convex_ball (0 : ℂ) 1).isPreconnected
    ((tiltedLensJet_diffContOnCl τ).differentiableOn.analyticOnNhd isOpen_ball)
    (fun w hw => tiltedLensJet_re_nonneg hτ0 hτ1 (mem_ball_zero_iff.mp hw).le)
    (mem_ball_self (by norm_num)) (tiltedLensJet_zero_re_pos hτ0 hτ1)
    z (mem_ball_zero_iff.mpr hz)

theorem tiltedLens_deriv_ne_zero {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {z : ℂ} (hz : ‖z‖ < 1) : deriv (tiltedLens τ) z ≠ 0 := by
  intro h
  have hp := tiltedLensJet_re_pos hτ0 hτ1 hz
  rw [tiltedLensJet_eq_deriv τ hz, h, mul_zero, Complex.zero_re] at hp
  exact lt_irrefl _ hp

theorem tiltedLens_exists_analytic_localInverse {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (tiltedLens τ z) ∧
      (∀ᶠ u in 𝓝 z, g (tiltedLens τ u) = u) ∧
      (∀ᶠ w in 𝓝 (tiltedLens τ z), tiltedLens τ (g w) = w) ∧
      HasDerivAt g (deriv (tiltedLens τ) z)⁻¹ (tiltedLens τ z) := by
  have ha : AnalyticAt ℂ (tiltedLens τ) z :=
    (tiltedLens_diffContOnCl τ).differentiableOn.analyticOnNhd isOpen_ball z
      (mem_ball_zero_iff.mpr hz)
  have hn := tiltedLens_deriv_ne_zero hτ0 hτ1 hz
  refine ⟨ha.hasStrictDerivAt.localInverse _ _ _ hn, ha.analyticAt_localInverse hn,
    ha.hasStrictDerivAt.eventually_left_inverse hn,
    ha.hasStrictDerivAt.eventually_right_inverse hn,
    (ha.hasStrictDerivAt.to_localInverse hn).hasDerivAt⟩

end
end Funk
