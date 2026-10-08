import Funk.LensBoundary

/-! Identify the imaginary part of the actual lens boundary with the known
height formula.  An integrating factor and the opposite endpoint values fix
the integration constant; no boundary value of the arctangent at `±I` is used. -/

open Set

namespace Funk
noncomputable section

/-- Uniqueness for a scalar linear ODE with the sum of the endpoint values
prescribed.  Differentiability is only required in the open interval. -/
theorem linear_ode_eq_of_endpoint_sum {f g : ℝ → ℝ} {a b k : ℝ} {q : ℝ → ℝ}
    (hab : a < b) (hf : Continuous f) (hg : Continuous g)
    (hdf : ∀ x ∈ Ioo a b, HasDerivAt f (-k * f x + q x) x)
    (hdg : ∀ x ∈ Ioo a b, HasDerivAt g (-k * g x + q x) x)
    (hend : f a + f b = g a + g b) : EqOn f g (Icc a b) := by
  let C : ℝ → ℝ := fun x => Real.exp (k * x) * (f x - g x)
  have hc : Continuous C := by
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul (hf.sub hg)
  have hd : ∀ x ∈ Ioo a b, HasDerivAt C 0 x := by
    intro x hx
    convert (((hasDerivAt_id x).const_mul k).exp).mul ((hdf x hx).sub (hdg x hx)) using 1
    · rfl
    · dsimp
      ring
  have hm : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have heq : EqOn C (fun _ => C ((a + b) / 2)) (Ioo a b) := by
    intro x hx
    exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hd y hy).deriv) hx hm
  have hclosed := heq.closure hc continuous_const
  rw [closure_Ioo hab.ne] at hclosed
  have habC : C a = C b :=
    (hclosed (left_mem_Icc.mpr hab.le)).trans (hclosed (right_mem_Icc.mpr hab.le)).symm
  have hbzero : f b - g b = 0 := by
    have hmul : (Real.exp (k * a) + Real.exp (k * b)) * (f b - g b) = 0 := by
      dsimp [C] at habC
      linear_combination Real.exp (k * a) * hend - habC
    exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt (by positivity))
  intro x hx
  have hxC : C x = C b := (hclosed hx).trans (hclosed (right_mem_Icc.mpr hab.le)).symm
  dsimp [C] at hxC
  rw [hbzero, mul_zero] at hxC
  exact sub_eq_zero.mp ((mul_eq_zero.mp hxC).resolve_left (Real.exp_ne_zero _))

theorem lensBoundary_continuous (τ : ℝ) : Continuous (lensRadialTrace τ 1) := by
  apply continuousOn_univ.mp
  apply (tiltedLens_continuousOn τ).comp (continuous_circleMap 0 1).continuousOn
  intro θ _
  change ‖circleMap 0 1 θ‖ ≤ 1
  simp

theorem lensBoundary_opposite_endpoints (τ : ℝ) :
    lensRadialTrace τ 1 (-Real.pi / 2) = -lensRadialTrace τ 1 (Real.pi / 2) := by
  have hl : circleMap 0 1 (-Real.pi / 2) = -Complex.I := by
    apply Complex.ext <;> simp [circleMap_zero_re, circleMap_zero_im, neg_div]
  have hr : circleMap 0 1 (Real.pi / 2) = Complex.I := by
    apply Complex.ext <;> simp [circleMap_zero_re, circleMap_zero_im]
  simp only [lensRadialTrace, hl, hr, tiltedLens_neg]

theorem lensFactor_mul_pi (τ : ℝ) : lensFactor τ * Real.pi / 4 = lensRate τ / τ := by
  unfold lensFactor
  field_simp

/-- Endpoint values and the interior angular ODE uniquely determine the height. -/
theorem lensBoundary_im_eq_tiltedHeight {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    EqOn (fun θ => (lensRadialTrace τ 1 θ).im) (tiltedHeight τ)
      (Icc (-Real.pi / 2) (Real.pi / 2)) := by
  apply linear_ode_eq_of_endpoint_sum (f := fun θ => (lensRadialTrace τ 1 θ).im)
    (g := tiltedHeight τ) (k := lensRate τ) (q := fun _ => lensRate τ / τ)
    (by linarith [Real.pi_pos])
    (Complex.continuous_im.comp (lensBoundary_continuous τ))
    (by unfold tiltedHeight lensHeight; fun_prop)
  · intro θ hθ
    have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (by simpa [neg_div] using hθ)
    simpa only [lensFactor_mul_pi] using hasDerivAt_lensBoundary_im τ hcos
  · intro θ _
    convert hasDerivAt_lensHeight τ (lensRate τ) (lensScale τ) θ using 1
    · rfl
    · dsimp [tiltedHeight, lensHeight]
      field_simp
      ring
  · rw [tiltedHeight_left hτ0 hτ1, tiltedHeight_right hτ0 hτ1,
      lensBoundary_opposite_endpoints]
    simp

theorem lensBoundary_im_left {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    (tiltedLens τ (-Complex.I)).im = -1 := by
  have h := lensBoundary_im_eq_tiltedHeight hτ0 hτ1
    (left_mem_Icc.mpr (by linarith [Real.pi_pos]))
  have hl : circleMap 0 1 (-Real.pi / 2) = -Complex.I := by
    apply Complex.ext <;> simp [circleMap_zero_re, circleMap_zero_im, neg_div]
  simpa [lensRadialTrace, hl, tiltedHeight_left hτ0 hτ1] using h

theorem lensBoundary_im_right {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    (tiltedLens τ Complex.I).im = 1 := by
  have h := lensBoundary_im_eq_tiltedHeight hτ0 hτ1
    (right_mem_Icc.mpr (by linarith [Real.pi_pos]))
  have hr : circleMap 0 1 (Real.pi / 2) = Complex.I := by
    apply Complex.ext <;> simp [circleMap_zero_re, circleMap_zero_im]
  simpa [lensRadialTrace, hr, tiltedHeight_right hτ0 hτ1] using h

theorem lensBoundary_im_strictMonoOn {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    StrictMonoOn (fun θ => (lensRadialTrace τ 1 θ).im)
      (Icc (-Real.pi / 2) (Real.pi / 2)) := by
  intro x hx y hy hxy
  rw [lensBoundary_im_eq_tiltedHeight hτ0 hτ1 hx,
    lensBoundary_im_eq_tiltedHeight hτ0 hτ1 hy]
  exact tiltedHeight_strictMono hτ0 hτ1 hxy

theorem lensBoundary_injOn_right {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    InjOn (lensRadialTrace τ 1) (Icc (-Real.pi / 2) (Real.pi / 2)) := by
  intro x hx y hy hxy
  exact (lensBoundary_im_strictMonoOn hτ0 hτ1).injOn hx hy (congrArg Complex.im hxy)

end
end Funk
