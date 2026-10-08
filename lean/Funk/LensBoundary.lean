import Funk.LensAnalytic
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-! Boundary analysis of the actual lens series.  Boundary derivatives are obtained
by a locally uniform radial limit; complex differentiability of the globally
defined tsum at the unit circle is neither assumed nor asserted. -/

open Set Filter
open scoped Topology

namespace Funk
noncomputable section

def arctanCayley (z : ℂ) : ℂ := (1 + z * Complex.I) / (1 - z * Complex.I)

theorem arctanCayley_den_ne_zero {z : ℂ} (hz : 0 < z.re) :
    1 - z * Complex.I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp at hi
  linarith

theorem arctanCayley_re (z : ℂ) :
    (arctanCayley z).re = (1 - ‖z‖ ^ 2) / Complex.normSq (1 - z * Complex.I) := by
  simp only [arctanCayley, Complex.div_re, Complex.add_re, Complex.one_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.add_im,
    Complex.one_im, Complex.mul_im, Complex.sub_im, mul_zero, mul_one, zero_add,
    add_zero, zero_sub, sub_neg_eq_add, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem arctanCayley_im (z : ℂ) :
    (arctanCayley z).im = 2 * z.re / Complex.normSq (1 - z * Complex.I) := by
  simp only [arctanCayley, Complex.div_im, Complex.add_re, Complex.one_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.add_im,
    Complex.one_im, Complex.mul_im, Complex.sub_im, mul_zero, mul_one, zero_add,
    add_zero, zero_sub, sub_neg_eq_add]
  ring

theorem arctanCayley_im_pos {z : ℂ} (hz : 0 < z.re) : 0 < (arctanCayley z).im := by
  rw [arctanCayley_im]
  exact div_pos (by linarith) (Complex.normSq_pos.mpr (arctanCayley_den_ne_zero hz))

theorem arctanCayley_mem_slitPlane {z : ℂ} (hz : 0 < z.re) :
    arctanCayley z ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt (arctanCayley_im_pos hz)))

theorem continuousAt_arctan_right {z : ℂ} (hz : 0 < z.re) :
    ContinuousAt Complex.arctan z := by
  have hc : ContinuousAt arctanCayley z := by
    unfold arctanCayley
    exact (continuousAt_const.add (continuousAt_id.mul continuousAt_const)).div
      (continuousAt_const.sub (continuousAt_id.mul continuousAt_const))
      (arctanCayley_den_ne_zero hz)
  exact continuousAt_const.mul (hc.clog (arctanCayley_mem_slitPlane hz))

/-- The constant forcing term on the open right semicircle.  The two points
`±I` are deliberately excluded by the strict real-part hypothesis. -/
theorem arctan_re_unit_right {z : ℂ} (hn : ‖z‖ = 1) (hr : 0 < z.re) :
    (Complex.arctan z).re = Real.pi / 4 := by
  have harg : (arctanCayley z).arg = Real.pi / 2 := by
    apply Complex.arg_eq_pi_div_two_iff.mpr
    exact ⟨by rw [arctanCayley_re, hn]; norm_num, arctanCayley_im_pos hr⟩
  change (-Complex.I / 2 * Complex.log (arctanCayley z)).re = _
  simp [Complex.mul_re, Complex.log_im, harg]
  ring

/-- The trace on a circle of radius `r`; `r = 1` is the actual boundary trace. -/
def lensRadialTrace (τ r θ : ℝ) : ℂ := tiltedLens τ (circleMap 0 r θ)

def lensAngularField (τ r θ : ℝ) : ℂ :=
  -(lensRate τ : ℂ) * lensRadialTrace τ r θ +
    Complex.I * (lensFactor τ : ℂ) * Complex.arctan (circleMap 0 r θ)

theorem hasDerivAt_lensRadialTrace (τ : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (θ : ℝ) : HasDerivAt (lensRadialTrace τ r) (lensAngularField τ r θ) θ := by
  have hn : ‖circleMap 0 r θ‖ < 1 := by simpa [abs_of_pos hr0] using hr1
  have hd := ((tiltedLens_differentiableOn τ).differentiableAt
    ((isOpen_lt continuous_norm continuous_const).mem_nhds hn)).hasDerivAt
  have hc := hd.comp θ (hasDerivAt_circleMap 0 r θ)
  have heq : deriv (tiltedLens τ) (circleMap 0 r θ) * (circleMap 0 r θ * Complex.I) =
      lensAngularField τ r θ := by
    have ho := congrArg (fun w : ℂ => w * Complex.I) (tiltedLens_ode τ hn)
    unfold lensAngularField lensRadialTrace
    linear_combination (norm := (ring_nf; simp [Complex.I_sq])) ho
  rw [heq] at hc
  exact hc

theorem continuous_lens_circle :
    Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
  simp only [circleMap_zero]
  fun_prop

theorem lensRadialTrace_continuousOn (τ : ℝ) (S : Set ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => lensRadialTrace τ p.1 p.2)
      (Icc (1 / 2 : ℝ) 1 ×ˢ S) := by
  apply (tiltedLens_continuousOn τ).comp continuous_lens_circle.continuousOn
  rintro ⟨r, θ⟩ ⟨hr, _⟩
  change ‖circleMap 0 r θ‖ ≤ 1
  rw [norm_circleMap_zero, abs_of_nonneg (by linarith [hr.1])]
  exact hr.2

theorem lensAngularField_continuousOn (τ : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => lensAngularField τ p.1 p.2)
      (Icc (1 / 2 : ℝ) 1 ×ˢ {θ : ℝ | 0 < Real.cos θ}) := by
  have ha : ContinuousOn (fun p : ℝ × ℝ => Complex.arctan (circleMap 0 p.1 p.2))
      (Icc (1 / 2 : ℝ) 1 ×ˢ {θ : ℝ | 0 < Real.cos θ}) := by
    intro p hp
    have hr : 0 < (circleMap 0 p.1 p.2).re := by
      rw [circleMap_zero_re]
      exact mul_pos (by linarith [hp.1.1]) hp.2
    exact ((continuousAt_arctan_right hr).comp
      (f := fun p : ℝ × ℝ => circleMap 0 p.1 p.2) continuous_lens_circle.continuousAt).continuousWithinAt
  exact (continuousOn_const.mul (lensRadialTrace_continuousOn τ _)).add
    (continuousOn_const.mul ha)

theorem lens_inward_filter_le :
    𝓝[<] (1 : ℝ) ≤ 𝓝[Icc (1 / 2 : ℝ) 1] 1 := by
  apply le_inf nhdsWithin_le_nhds
  apply le_principal_iff.mpr
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1)).filter_mono
      nhdsWithin_le_nhds] with r hr hr0
  exact ⟨hr0.le, hr.le⟩

theorem lensAngularField_tendstoLocallyUniformly (τ : ℝ) :
    TendstoLocallyUniformlyOn (lensAngularField τ) (lensAngularField τ 1)
      (𝓝[<] (1 : ℝ)) {θ : ℝ | 0 < Real.cos θ} := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact
    (isOpen_lt continuous_const Real.continuous_cos)]
  intro K hK hcompact
  have hc : ContinuousOn (fun p : ℝ × ℝ => lensAngularField τ p.1 p.2)
      (Icc (1 / 2 : ℝ) 1 ×ˢ K) :=
    (lensAngularField_continuousOn τ).mono (prod_mono Subset.rfl hK)
  have hu := ((isCompact_Icc.prod hcompact).uniformContinuousOn_of_continuous hc).tendstoUniformlyOn (F := lensAngularField τ) (by norm_num : (1 : ℝ) ∈ Icc (1 / 2 : ℝ) 1)
  exact fun u hu' => (hu u hu').filter_mono lens_inward_filter_le

theorem lensRadialTrace_tendsto (τ θ : ℝ) :
    Tendsto (fun r => lensRadialTrace τ r θ) (𝓝[<] (1 : ℝ))
      (𝓝 (lensRadialTrace τ 1 θ)) := by
  have hp : Continuous (fun r : ℝ => circleMap 0 r θ) := by
    simp only [circleMap_zero]
    fun_prop
  have hc : ContinuousOn (fun r => lensRadialTrace τ r θ) (Icc (1 / 2 : ℝ) 1) := by
    apply (tiltedLens_continuousOn τ).comp hp.continuousOn
    intro r hr
    change ‖circleMap 0 r θ‖ ≤ 1
    rw [norm_circleMap_zero, abs_of_nonneg (by linarith [hr.1])]
    exact hr.2
  exact (hc 1 (by norm_num)).mono_left lens_inward_filter_le

/-- An angular derivative of the boundary trace, obtained from interior circles. -/
theorem hasDerivAt_lensBoundary (τ : ℝ) {θ : ℝ} (hθ : 0 < Real.cos θ) :
    HasDerivAt (lensRadialTrace τ 1) (lensAngularField τ 1 θ) θ := by
  apply hasDerivAt_of_tendstoLocallyUniformlyOn
    (isOpen_lt continuous_const Real.continuous_cos)
    (lensAngularField_tendstoLocallyUniformly τ) ?_
    (fun x _ => lensRadialTrace_tendsto τ x) hθ
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
      nhdsWithin_le_nhds] with r hr hr0
  intro x _
  exact hasDerivAt_lensRadialTrace τ hr0 hr x

/-- The imaginary part of the actual boundary trace satisfies the scalar ODE.
This statement alone does not yet identify its integration constant. -/
theorem hasDerivAt_lensBoundary_im (τ : ℝ) {θ : ℝ} (hθ : 0 < Real.cos θ) :
    HasDerivAt (fun x => (lensRadialTrace τ 1 x).im)
      (-lensRate τ * (lensRadialTrace τ 1 θ).im + lensFactor τ * Real.pi / 4) θ := by
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_lensBoundary τ hθ)
  have hr : 0 < (circleMap 0 1 θ).re := by simpa [circleMap_zero_re] using hθ
  have hn : ‖circleMap 0 1 θ‖ = 1 := by simp
  simpa [lensAngularField, Complex.mul_im, arctan_re_unit_right hn hr, mul_div_assoc,
    Function.comp_def, Complex.imCLM_apply]
    using h

end
end Funk
