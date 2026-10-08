import Funk.LensFrontier
import Funk.ConvexMaximum
import Mathlib.Analysis.Complex.OpenMapping

/-! The actual holomorphic map sends the open disk onto the interior of the
explicit convex body, and the closed disk onto the body.  No uniqueness of
preimages is asserted: injectivity remains a separate proof obligation. -/

open Set Metric

namespace Funk
noncomputable section

theorem tiltedLens_diffContOnCl (τ : ℝ) :
    DiffContOnCl ℂ (tiltedLens τ) (ball 0 1) := by
  apply DiffContOnCl.mk_ball
  · simpa only [ball, dist_zero_right] using tiltedLens_differentiableOn τ
  · simpa only [closedBall, dist_zero_right] using tiltedLens_continuousOn τ

theorem tiltedLens_mapsTo_closedBall {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    MapsTo (tiltedLens τ) (closedBall 0 1) (lensGraphBody τ) := by
  intro z hz
  apply holomorphic_mem_closed_convex_of_frontier (isBounded_ball (x := (0 : ℂ)) (r := 1))
    (tiltedLens_diffContOnCl τ) (lensGraphBody_convex hτ0 hτ1)
    (lensGraphBody_isClosed hτ0 hτ1)
  · intro w hw
    have hn : ‖w‖ = 1 := by simpa [frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hw
    exact lensCircleImage_subset_graphBody hτ0 hτ1 ⟨w, hn, rfl⟩
  · simpa only [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hz

theorem tiltedLens_not_constant_on_disk {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ¬∃ c, ∀ z ∈ ball (0 : ℂ) 1, tiltedLens τ z = c := by
  rintro ⟨c, hc⟩
  have hc0 : c = 0 := by
    simpa only [tiltedLens_zero] using (hc 0 (mem_ball_self (by norm_num))).symm
  have he : EqOn (tiltedLens τ) (fun _ => c) (closure (ball (0 : ℂ) 1)) :=
    (show EqOn (tiltedLens τ) (fun _ => c) (ball (0 : ℂ) 1) from hc).of_subset_closure
      (tiltedLens_diffContOnCl τ).continuousOn continuousOn_const subset_closure subset_rfl
  have hi : Complex.I ∈ closure (ball (0 : ℂ) 1) := by
    rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    simp
  have h := congrArg Complex.im (he hi)
  rw [lensBoundary_im_right hτ0 hτ1, hc0, Complex.zero_im] at h
  norm_num at h

theorem tiltedLens_isOpen_on_disk {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ∀ s ⊆ ball (0 : ℂ) 1, IsOpen s → IsOpen (tiltedLens τ '' s) :=
  (((tiltedLens_diffContOnCl τ).differentiableOn.analyticOnNhd isOpen_ball).is_constant_or_isOpen
    (convex_ball (0 : ℂ) 1).isPreconnected).resolve_left (tiltedLens_not_constant_on_disk hτ0 hτ1)

theorem tiltedLens_mapsTo_ball_interior {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    MapsTo (tiltedLens τ) (ball 0 1) (interior (lensGraphBody τ)) := by
  have ho := tiltedLens_isOpen_on_disk hτ0 hτ1 _ subset_rfl isOpen_ball
  have hs : tiltedLens τ '' ball 0 1 ⊆ lensGraphBody τ := by
    rintro w ⟨z, hz, rfl⟩
    exact tiltedLens_mapsTo_closedBall hτ0 hτ1 (ball_subset_closedBall hz)
  intro z hz
  exact interior_maximal hs ho ⟨z, hz, rfl⟩

theorem tiltedLens_preimage_interior_mem_ball {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {z : ℂ} (hz : z ∈ closedBall 0 1) (hf : tiltedLens τ z ∈ interior (lensGraphBody τ)) :
    z ∈ ball 0 1 := by
  have hn : ‖z‖ ≤ 1 := by simpa using hz
  apply mem_ball_zero_iff.mpr
  apply lt_of_le_of_ne hn
  intro he
  have hb : tiltedLens τ z ∈ frontier (lensGraphBody τ) :=
    lensCircleImage_subset_frontier hτ0 hτ1 ⟨z, he, rfl⟩
  exact hb.2 hf

theorem tiltedLens_closure_image_inter_interior {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    closure (tiltedLens τ '' ball 0 1) ∩ interior (lensGraphBody τ) ⊆
      tiltedLens τ '' ball 0 1 := by
  have hc : IsClosed (tiltedLens τ '' closedBall 0 1) := by
    simpa only [closedBall, dist_zero_right] using (tiltedLens_isCompact_image τ).isClosed
  have hs : closure (tiltedLens τ '' ball 0 1) ⊆ tiltedLens τ '' closedBall 0 1 :=
    closure_minimal (image_mono ball_subset_closedBall) hc
  rintro w ⟨hw, hi⟩
  obtain ⟨z, hz, rfl⟩ := hs hw
  exact ⟨z, tiltedLens_preimage_interior_mem_ball hτ0 hτ1 hz hi, rfl⟩

theorem tiltedLens_image_ball {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    tiltedLens τ '' ball 0 1 = interior (lensGraphBody τ) := by
  apply Subset.antisymm (tiltedLens_mapsTo_ball_interior hτ0 hτ1).image_subset
  apply (lensGraphBody_convex hτ0 hτ1).interior.isPreconnected.subset_of_closure_inter_subset
    (tiltedLens_isOpen_on_disk hτ0 hτ1 _ subset_rfl isOpen_ball)
  · exact ⟨0, lensGraphBody_zero_mem_interior hτ0 hτ1,
      ⟨0, mem_ball_self (by norm_num), tiltedLens_zero τ⟩⟩
  · exact tiltedLens_closure_image_inter_interior hτ0 hτ1

theorem tiltedLens_image_closedBall {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    tiltedLens τ '' closedBall 0 1 = lensGraphBody τ := by
  apply Subset.antisymm (tiltedLens_mapsTo_closedBall hτ0 hτ1).image_subset
  intro w hw
  by_cases hi : w ∈ interior (lensGraphBody τ)
  · rw [← tiltedLens_image_ball hτ0 hτ1] at hi
    exact image_mono ball_subset_closedBall hi
  · have hb : w ∈ frontier (lensGraphBody τ) := ⟨subset_closure hw, hi⟩
    rw [lensGraphBody_frontier_eq_circleImage hτ0 hτ1] at hb
    obtain ⟨z, hz, rfl⟩ := hb
    exact ⟨z, by simpa using hz.le, rfl⟩

theorem tiltedLens_image_ball_convex {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    Convex ℝ (tiltedLens τ '' ball 0 1) := by
  rw [tiltedLens_image_ball hτ0 hτ1]
  exact (lensGraphBody_convex hτ0 hτ1).interior

end
end Funk
