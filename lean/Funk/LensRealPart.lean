import Funk.LensBoundaryHeight

/-! Angular derivatives needed for separating the two lens arcs.  The real
part is handled by an ODE, without evaluating its boundary integral. -/

open Set

namespace Funk
noncomputable section

theorem arctanCayley_num_ne_zero {z : ℂ} (hz : 0 < z.re) :
    1 + z * Complex.I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp at hi
  linarith

theorem one_add_sq_factor (z : ℂ) :
    1 + z ^ 2 = (1 - z * Complex.I) * (1 + z * Complex.I) := by
  ring_nf
  simp [Complex.I_sq]

theorem one_add_sq_ne_zero_right {z : ℂ} (hz : 0 < z.re) : 1 + z ^ 2 ≠ 0 := by
  rw [one_add_sq_factor]
  exact mul_ne_zero (arctanCayley_den_ne_zero hz) (arctanCayley_num_ne_zero hz)

theorem hasDerivAt_arctanCayley {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt arctanCayley (2 * Complex.I / (1 - z * Complex.I) ^ 2) z := by
  have h := ((hasDerivAt_const z (1 : ℂ)).add
    ((hasDerivAt_id z).mul_const Complex.I)).div
    ((hasDerivAt_const z (1 : ℂ)).sub ((hasDerivAt_id z).mul_const Complex.I))
    (arctanCayley_den_ne_zero hz)
  convert h using 1
  · rfl
  · dsimp
    ring

theorem hasDerivAt_arctan_right {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt Complex.arctan (1 / (1 + z ^ 2)) z := by
  have h := ((Complex.hasDerivAt_log (arctanCayley_mem_slitPlane hz)).comp z
    (hasDerivAt_arctanCayley hz)).const_mul (-Complex.I / 2)
  convert h using 1
  · rfl
  · dsimp [arctanCayley]
    rw [one_add_sq_factor]
    field_simp [arctanCayley_den_ne_zero hz, arctanCayley_num_ne_zero hz]
    ring_nf
    simp [Complex.I_sq]

theorem one_add_sq_unit {z : ℂ} (hz : ‖z‖ = 1) :
    1 + z ^ 2 = (2 * z.re : ℂ) * z := by
  have hn : z.re ^ 2 + z.im ^ 2 = 1 := by
    calc
      z.re ^ 2 + z.im ^ 2 = Complex.normSq z := by rw [Complex.normSq_apply]; ring
      _ = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
      _ = 1 := by rw [hz]; norm_num
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, pow_two] <;> nlinarith

theorem hasDerivAt_arctan_circle {θ : ℝ} (hθ : 0 < Real.cos θ) :
    HasDerivAt (fun x => Complex.arctan (circleMap 0 1 x))
      (Complex.I / ((2 * Real.cos θ : ℝ) : ℂ)) θ := by
  have hr : 0 < (circleMap 0 1 θ).re := by simpa [circleMap_zero_re] using hθ
  have hn : ‖circleMap 0 1 θ‖ = 1 := by simp
  have hz : circleMap 0 1 θ ≠ 0 := by intro h; simp [h] at hn
  have hc : (Real.cos θ : ℂ) ≠ 0 := by exact_mod_cast hθ.ne'
  convert (hasDerivAt_arctan_right hr).comp θ (hasDerivAt_circleMap 0 1 θ) using 1
  · rfl
  · rw [one_add_sq_unit hn, circleMap_zero_re]
    push_cast
    field_simp

theorem hasDerivAt_arctan_circle_im {θ : ℝ} (hθ : 0 < Real.cos θ) :
    HasDerivAt (fun x => (Complex.arctan (circleMap 0 1 x)).im)
      (1 / (2 * Real.cos θ)) θ := by
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_arctan_circle hθ)
  change HasDerivAt (fun x => (Complex.arctan (circleMap 0 1 x)).im)
    (Complex.I / ((2 * Real.cos θ : ℝ) : ℂ)).im θ at h
  simpa only [Complex.div_ofReal_im, Complex.I_im] using h

theorem hasDerivAt_lensBoundary_re (τ : ℝ) {θ : ℝ} (hθ : 0 < Real.cos θ) :
    HasDerivAt (fun x => (lensRadialTrace τ 1 x).re)
      (-lensRate τ * (lensRadialTrace τ 1 θ).re -
        lensFactor τ * (Complex.arctan (circleMap 0 1 θ)).im) θ := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_lensBoundary τ hθ)
  simpa [lensAngularField, Complex.mul_re, Function.comp_def, Complex.reCLM_apply,
    sub_eq_add_neg] using h

theorem lensFactor_pos {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) : 0 < lensFactor τ := by
  have hb := lensRate_pos hτ0 hτ1
  unfold lensFactor
  positivity

end
end Funk
