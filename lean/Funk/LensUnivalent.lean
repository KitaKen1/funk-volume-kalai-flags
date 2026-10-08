import Funk.LensJetPositive
import Funk.ArctanStrip
import Funk.LensFibers

/-! Univalence of the actual lens series. Arctangent coordinates turn the
positive regularized derivative into a positive-real derivative on a convex
strip, where the real mean-value theorem proves injectivity. -/

open Set Metric

namespace Funk
noncomputable section

theorem hasDerivAt_lens_tan (τ : ℝ) {z : ℂ} (hz : z ∈ arctanStrip) :
    HasDerivAt (fun w => tiltedLens τ (Complex.tan w)) (tiltedLensJet τ (Complex.tan z)) z := by
  have hn := norm_tan_lt_one_of_mem_strip hz
  have hf := ((tiltedLens_diffContOnCl τ).differentiableOn.differentiableAt
    (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hn))).hasDerivAt
  convert hf.comp z (hasDerivAt_tan_strip hz) using 1
  · rfl
  · rw [tiltedLensJet_eq_deriv τ hn]
    ring

theorem tiltedLens_tan_injOn {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    InjOn (fun z => tiltedLens τ (Complex.tan z)) arctanStrip := by
  apply injOn_of_deriv_re_pos arctanStrip_isOpen arctanStrip_convex
    (fun z hz => (hasDerivAt_lens_tan τ hz).differentiableAt.differentiableWithinAt)
  intro z hz
  rw [(hasDerivAt_lens_tan τ hz).deriv]
  exact tiltedLensJet_re_pos hτ0 hτ1 (norm_tan_lt_one_of_mem_strip hz)

theorem tiltedLens_injOn_ball {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    InjOn (tiltedLens τ) (ball 0 1) := by
  intro z hz w hw he
  have hnz := mem_ball_zero_iff.mp hz
  have hnw := mem_ball_zero_iff.mp hw
  have ha := tiltedLens_tan_injOn hτ0 hτ1 (arctan_mem_strip hnz) (arctan_mem_strip hnw)
    (by simpa only [tan_arctan_disk hnz, tan_arctan_disk hnw] using he)
  have ht := congrArg Complex.tan ha
  simpa only [tan_arctan_disk hnz, tan_arctan_disk hnw] using ht

theorem tiltedLens_injOn_closedBall {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    InjOn (tiltedLens τ) (closedBall 0 1) := by
  intro z hz w hw he
  by_cases hzi : z ∈ ball (0 : ℂ) 1
  · have hwi := tiltedLens_preimage_interior_mem_ball hτ0 hτ1 hw
      (he ▸ tiltedLens_mapsTo_ball_interior hτ0 hτ1 hzi)
    exact tiltedLens_injOn_ball hτ0 hτ1 hzi hwi he
  · by_cases hwi : w ∈ ball (0 : ℂ) 1
    · exact False.elim (hzi (tiltedLens_preimage_interior_mem_ball hτ0 hτ1 hz
        (he.symm ▸ tiltedLens_mapsTo_ball_interior hτ0 hτ1 hwi)))
    · exact tiltedLens_injOn_unitCircle hτ0 hτ1
        (le_antisymm (mem_closedBall_zero_iff.mp hz) (not_lt.mp (by simpa using hzi)))
        (le_antisymm (mem_closedBall_zero_iff.mp hw) (not_lt.mp (by simpa using hwi))) he

theorem tiltedLens_bijOn_ball {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    BijOn (tiltedLens τ) (ball 0 1) (interior (lensGraphBody τ)) :=
  ⟨tiltedLens_mapsTo_ball_interior hτ0 hτ1, tiltedLens_injOn_ball hτ0 hτ1,
    (tiltedLens_image_ball hτ0 hτ1).superset⟩

theorem tiltedLens_bijOn_closedBall {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    BijOn (tiltedLens τ) (closedBall 0 1) (lensGraphBody τ) :=
  ⟨tiltedLens_mapsTo_closedBall hτ0 hτ1, tiltedLens_injOn_closedBall hτ0 hτ1,
    (tiltedLens_image_closedBall hτ0 hτ1).superset⟩

theorem lensFiber_eq_singleton {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {z : ℂ} (hz : z ∈ closedBall 0 1) : lensFiber τ (tiltedLens τ z) = {z} := by
  ext w
  constructor
  · rintro ⟨hw, he⟩
    exact tiltedLens_injOn_closedBall hτ0 hτ1 hw hz he
  · rintro rfl
    exact ⟨hz, rfl⟩

theorem lensFiber_card_one {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {w : ℂ} (hw : w ∈ lensGraphBody τ) : Nat.card (lensFiber τ w) = 1 := by
  obtain ⟨z, hz, rfl⟩ := (tiltedLens_image_closedBall hτ0 hτ1).superset hw
  rw [lensFiber_eq_singleton hτ0 hτ1 hz]
  simp

end
end Funk
