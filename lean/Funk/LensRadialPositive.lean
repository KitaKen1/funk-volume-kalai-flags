import Funk.LensRadialContraction

/-! Strict radial positivity follows from Schwarz contraction and the analytic
half-plane criterion. No coordinate reflection symmetry or Sard theorem is used. -/

open Set Metric Filter Complex
open scoped Topology

namespace Funk
noncomputable section

/-- The actual derivative of squared inverse radius in the radial direction. -/
def lensInverseRadiusSlope (τ : ℝ) (w : ℂ) : ℝ :=
  2 * ((tiltedLensInverse τ w).re *
      ((deriv (tiltedLens τ) (tiltedLensInverse τ w))⁻¹ * w).re +
    (tiltedLensInverse τ w).im *
      ((deriv (tiltedLens τ) (tiltedLensInverse τ w))⁻¹ * w).im)

theorem lensInverseRadius_hasDerivAt {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {w : ℂ} (hw : w ∈ interior (lensGraphBody τ)) :
    HasDerivAt (fun t : ℝ => normSq (tiltedLensInverse τ ((t : ℂ) * w)))
      (lensInverseRadiusSlope τ w) 1 := by
  have hl : HasDerivAt (fun t : ℂ => t*w) w (1 : ℂ) := by
    simpa using (hasDerivAt_id (1 : ℂ)).mul_const w
  have hi : HasDerivAt (tiltedLensInverse τ)
      (deriv (tiltedLens τ) (tiltedLensInverse τ w))⁻¹ ((fun t : ℂ => t*w) 1) := by
    simpa using hasDerivAt_tiltedLensInverse hτ0 hτ1 hw
  simpa only [lensInverseRadiusSlope, Function.comp_apply, ofReal_one, one_mul] using
    lens_hasDerivAt_normSq ((hi.comp (1 : ℂ) hl).comp_ofReal)

theorem lensInverseRadiusSlope_at_image {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {u : ℂ} (hu : u ∈ ball 0 1) :
    lensInverseRadiusSlope τ (tiltedLens τ u) = 2 * normSq u * (lensRadialRatio τ u).re := by
  unfold lensInverseRadiusSlope
  rw [tiltedLensInverse_left hτ0 hτ1 hu, tiltedLens_eq_mul_dslope]
  have he : starRingEnd ℂ u * ((deriv (tiltedLens τ) u)⁻¹ *
      (u * dslope (tiltedLens τ) 0 u)) =
      (normSq u : ℂ) * lensRadialRatio τ u := by
    rw [normSq_eq_conj_mul_self, lensRadialRatio, div_eq_mul_inv]
    ring
  have hr : u.re * ((deriv (tiltedLens τ) u)⁻¹ * (u * dslope (tiltedLens τ) 0 u)).re +
      u.im * ((deriv (tiltedLens τ) u)⁻¹ * (u * dslope (tiltedLens τ) 0 u)).im =
      normSq u * (lensRadialRatio τ u).re := by
    calc
      _ = (starRingEnd ℂ u * ((deriv (tiltedLens τ) u)⁻¹ *
          (u * dslope (tiltedLens τ) 0 u))).re := by
        conv_rhs => rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
        ring
      _ = _ := by rw [he, Complex.re_ofReal_mul]
  rw [hr]
  ring

theorem lensInverseRadiusSlope_nonneg_at_image {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {u : ℂ} (hu : u ∈ ball 0 1) :
    0 ≤ lensInverseRadiusSlope τ (tiltedLens τ u) := by
  let f : ℝ → ℝ := fun t => normSq (tiltedLensInverse τ ((t : ℂ) * tiltedLens τ u))
  have hm : IsMaxOn f (Icc (0 : ℝ) 1) 1 := by
    intro s hs
    have hn := tiltedLensInverse_radial_contraction hτ0 hτ1 hs.1 hs.2 hu
    dsimp [f]
    simp only [one_mul, tiltedLensInverse_left hτ0 hτ1 hu,
      normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) hn 2
  have ht : (-1 : ℝ) ∈ posTangentConeAt (Icc (0 : ℝ) 1) 1 := by
    convert sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc (0 : ℝ) 1).segment_subset
        (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
        (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1)) using 1
    norm_num
  have hd := lensInverseRadius_hasDerivAt hτ0 hτ1
    (tiltedLens_mapsTo_ball_interior hτ0 hτ1 hu)
  have h := hm.isLocalMaxOn.hasFDerivWithinAt_nonpos hd.hasFDerivAt.hasFDerivWithinAt ht
  simpa using h

theorem lensRadialRatio_re_nonneg {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {u : ℂ} (hu : u ∈ ball 0 1) : 0 ≤ (lensRadialRatio τ u).re := by
  by_cases hu0 : u = 0
  · simp [hu0, lensRadialRatio_zero hτ0 hτ1]
  · have h := lensInverseRadiusSlope_nonneg_at_image hτ0 hτ1 hu
    rw [lensInverseRadiusSlope_at_image hτ0 hτ1 hu] at h
    exact (mul_nonneg_iff_of_pos_left (mul_pos (by norm_num) (normSq_pos.mpr hu0))).mp h

theorem lensRadialRatio_re_pos {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {u : ℂ} (hu : u ∈ ball 0 1) : 0 < (lensRadialRatio τ u).re := by
  exact re_pos_of_nonneg_on_connected isOpen_ball (convex_ball (0 : ℂ) 1).isPreconnected
    (lensRadialRatio_analyticOnNhd hτ0 hτ1)
    (fun _ hz => lensRadialRatio_re_nonneg hτ0 hτ1 hz)
    (by simp : (0 : ℂ) ∈ ball 0 1) (by simp [lensRadialRatio_zero hτ0 hτ1]) u hu

theorem lensInverseRadiusSlope_pos {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {w : ℂ} (hw : w ∈ interior (lensGraphBody τ)) (hw0 : w ≠ 0) :
    0 < lensInverseRadiusSlope τ w := by
  have hu := tiltedLensInverse_mem_ball hτ0 hτ1 hw
  have hu0 := (tiltedLensInverse_eq_zero_iff hτ0 hτ1 hw).not.mpr hw0
  have h := lensInverseRadiusSlope_at_image hτ0 hτ1 hu
  rw [tiltedLensInverse_right hτ0 hτ1 hw] at h
  rw [h]
  exact mul_pos (mul_pos (by norm_num) (normSq_pos.mpr hu0))
    (lensRadialRatio_re_pos hτ0 hτ1 hu)

theorem lensInverseRadiusSlope_zero (τ : ℝ) : lensInverseRadiusSlope τ 0 = 0 := by
  simp [lensInverseRadiusSlope]

theorem lensInverseRadiusSlope_nonneg {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {w : ℂ} (hw : w ∈ interior (lensGraphBody τ)) :
    0 ≤ lensInverseRadiusSlope τ w := by
  by_cases hw0 : w = 0
  · simp [hw0, lensInverseRadiusSlope_zero]
  · exact (lensInverseRadiusSlope_pos hτ0 hτ1 hw hw0).le

end
end Funk
