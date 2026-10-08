import Funk.LensJet
import Funk.LensRealPart

/-! Boundary values of the regularized derivative. Its real part can be read
off from the already proved height ODE, without evaluating a contour integral. -/

open Set Filter
open scoped Topology

namespace Funk
noncomputable section

theorem tiltedLensJet_radial_tendsto (τ θ : ℝ) :
    Tendsto (fun r => tiltedLensJet τ (circleMap 0 r θ)) (𝓝[<] (1 : ℝ))
      (𝓝 (tiltedLensJet τ (circleMap 0 1 θ))) := by
  have hp : Continuous (fun r : ℝ => circleMap 0 r θ) := by
    simp only [circleMap_zero]
    fun_prop
  have hc : ContinuousOn (fun r => tiltedLensJet τ (circleMap 0 r θ))
      (Icc (1 / 2 : ℝ) 1) := by
    apply (tiltedLensJet_continuousOn τ).comp hp.continuousOn
    intro r hr
    change ‖circleMap 0 r θ‖ ≤ 1
    rw [norm_circleMap_zero, abs_of_nonneg (by linarith [hr.1])]
    exact hr.2
  exact (hc 1 (by norm_num)).mono_left lens_inward_filter_le

theorem tiltedLensJet_boundary (τ : ℝ) {θ : ℝ} (hθ : 0 < Real.cos θ) :
    tiltedLensJet τ (circleMap 0 1 θ) =
      -(2 * Real.cos θ : ℂ) * Complex.I * lensAngularField τ 1 θ := by
  have hp : Continuous (fun r : ℝ => circleMap 0 r θ) := by
    simp only [circleMap_zero]
    fun_prop
  have hz := hp.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[<] (1 : ℝ) ≤ 𝓝 1)
  have hj := tiltedLensJet_radial_tendsto τ θ
  have hf := lensRadialTrace_tendsto τ θ
  have hr : 0 < (circleMap 0 1 θ).re := by simpa [circleMap_zero_re] using hθ
  have ha := (continuousAt_arctan_right hr).tendsto.comp hz
  have hl := hz.mul hj
  have hh := ((tendsto_const_nhds (x := (1 : ℂ))).add (hz.pow 2)).mul
    (((tendsto_const_nhds (x := (lensRate τ : ℂ) * Complex.I)).mul hf).add
      ((tendsto_const_nhds (x := (lensFactor τ : ℂ))).mul ha))
  have he : ∀ᶠ r in 𝓝[<] (1 : ℝ),
      circleMap 0 r θ * tiltedLensJet τ (circleMap 0 r θ) =
        (1 + circleMap 0 r θ ^ 2) *
          ((lensRate τ : ℂ) * Complex.I * lensRadialTrace τ r θ +
            (lensFactor τ : ℂ) * Complex.arctan (circleMap 0 r θ)) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
        nhdsWithin_le_nhds] with r hr1 hr0
    have hn : ‖circleMap 0 r θ‖ < 1 := by
      rw [norm_circleMap_zero, abs_of_pos hr0]
      exact hr1
    rw [tiltedLensJet_eq_deriv τ hn]
    have ho := tiltedLens_ode τ hn
    dsimp [lensRadialTrace]
    linear_combination (1 + circleMap 0 r θ ^ 2) * ho
  have he' : (fun r => circleMap 0 r θ * tiltedLensJet τ (circleMap 0 r θ)) =ᶠ[𝓝[<] (1 : ℝ)]
      (fun r => (1 + circleMap 0 r θ ^ 2) *
        ((lensRate τ : ℂ) * Complex.I * lensRadialTrace τ r θ +
          (lensFactor τ : ℂ) * Complex.arctan (circleMap 0 r θ))) := he
  have heq := tendsto_nhds_unique hl (hh.congr' he'.symm)
  have hn : ‖circleMap 0 1 θ‖ = 1 := by simp
  have hne : circleMap 0 1 θ ≠ 0 := by intro h; simp [h] at hn
  apply mul_left_cancel₀ hne
  rw [heq, one_add_sq_unit hn, circleMap_zero_re]
  dsimp [lensAngularField]
  push_cast
  ring_nf
  simp [Complex.I_sq]

theorem tiltedLensJet_boundary_re (τ : ℝ) {θ : ℝ} (hθ : 0 < Real.cos θ) :
    (tiltedLensJet τ (circleMap 0 1 θ)).re =
      2 * Real.cos θ * (-lensRate τ * (lensRadialTrace τ 1 θ).im + lensRate τ / τ) := by
  rw [tiltedLensJet_boundary τ hθ]
  have hr : 0 < (circleMap 0 1 θ).re := by simpa [circleMap_zero_re] using hθ
  have hn : ‖circleMap 0 1 θ‖ = 1 := by simp
  simp [lensAngularField, Complex.mul_re, Complex.mul_im, arctan_re_unit_right hn hr,
    Complex.cos_ofReal_re]
  rw [show lensFactor τ * (Real.pi / 4) = lensRate τ / τ by
    simpa only [mul_div_assoc] using lensFactor_mul_pi τ]
  ring_nf; simp

theorem tiltedLensJet_boundary_re_continuous (τ : ℝ) :
    Continuous (fun θ => (tiltedLensJet τ (circleMap 0 1 θ)).re) := by
  apply Complex.continuous_re.comp
  apply continuousOn_univ.mp
  apply (tiltedLensJet_continuousOn τ).comp (continuous_circleMap 0 1).continuousOn
  intro θ _
  change ‖circleMap 0 1 θ‖ ≤ 1
  simp

theorem tiltedLensJet_boundary_re_eq {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    EqOn (fun θ => (tiltedLensJet τ (circleMap 0 1 θ)).re)
      (fun θ => 2 * Real.cos θ *
        (lensRate τ * lensScale τ * Real.exp (-lensRate τ * θ) / τ))
      (Icc (-Real.pi / 2) (Real.pi / 2)) := by
  have he : EqOn (fun θ => (tiltedLensJet τ (circleMap 0 1 θ)).re)
      (fun θ => 2 * Real.cos θ *
        (lensRate τ * lensScale τ * Real.exp (-lensRate τ * θ) / τ))
      (Ioo (-Real.pi / 2) (Real.pi / 2)) := by
    intro θ hθ
    dsimp only
    have hh := lensBoundary_im_eq_tiltedHeight hτ0 hτ1 ⟨hθ.1.le, hθ.2.le⟩
    dsimp only at hh
    rw [tiltedLensJet_boundary_re τ
      (Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hθ)), hh]
    dsimp [tiltedHeight, lensHeight]
    ring
  have hc : Continuous (fun θ : ℝ => 2 * Real.cos θ *
      (lensRate τ * lensScale τ * Real.exp (-lensRate τ * θ) / τ)) := by fun_prop
  have h := he.closure (tiltedLensJet_boundary_re_continuous τ) hc
  rwa [closure_Ioo (by linarith [Real.pi_pos] : -Real.pi / 2 ≠ Real.pi / 2)] at h

theorem tiltedLensJet_boundary_re_nonneg {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {θ : ℝ} (hθ : θ ∈ Icc (-Real.pi / 2) (Real.pi / 2)) :
    0 ≤ (tiltedLensJet τ (circleMap 0 1 θ)).re := by
  have he := tiltedLensJet_boundary_re_eq hτ0 hτ1 hθ
  dsimp only at he
  rw [he]
  have hc := Real.cos_nonneg_of_mem_Icc (by simpa only [neg_div] using hθ)
  have hb := lensRate_pos hτ0 hτ1
  have hs := lensScale_pos hτ0 hτ1
  positivity

theorem tiltedLensJet_boundary_re_pos {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {θ : ℝ} (hθ : θ ∈ Ioo (-Real.pi / 2) (Real.pi / 2)) :
    0 < (tiltedLensJet τ (circleMap 0 1 θ)).re := by
  have he := tiltedLensJet_boundary_re_eq hτ0 hτ1 ⟨hθ.1.le, hθ.2.le⟩
  dsimp only at he
  rw [he]
  have hc := Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hθ)
  have hb := lensRate_pos hτ0 hτ1
  have hs := lensScale_pos hτ0 hτ1
  positivity

end
end Funk
