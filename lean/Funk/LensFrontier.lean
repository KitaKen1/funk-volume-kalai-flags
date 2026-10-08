import Funk.LensConvexBody
import Mathlib.Analysis.Normed.Module.Convex

/-! Identification of the actual unit-circle image with the frontier of the
explicit convex region between its two arcs.  Disk univalence and equality
with the holomorphic disk image are separate, still unproved, assertions. -/

open Set Filter
open scoped Topology

namespace Funk
noncomputable section

theorem lensProfile_continuousAt {τ y : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hy : 0 < 1 - τ * y) : ContinuousAt (lensProfile τ) y :=
  ((lensChordCoordinate_continuous τ).comp (lensBoundary_continuous τ)).continuousAt.comp
    (lensHeightAngle_continuousAt hτ0 hτ1 hy)

theorem lensGraphBody_isClosed {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    IsClosed (lensGraphBody τ) := by
  let S : Set ℂ := {z | z.im ∈ Icc (-1) 1}
  have hs : IsClosed S := isClosed_Icc.preimage Complex.continuous_im
  have hr : ContinuousOn (fun z : ℂ => lensProfile τ z.im) S :=
    (lensProfile_continuousOn hτ0 hτ1).comp Complex.continuous_im.continuousOn
      (fun _ hz => hz)
  have hl : ContinuousOn (fun z : ℂ => -lensProfile τ (-z.im)) S := by
    apply ContinuousOn.neg
    apply (lensProfile_continuousOn hτ0 hτ1).comp Complex.continuous_im.neg.continuousOn
    intro z hz
    change -z.im ∈ Icc (-1) 1
    change z.im ∈ Icc (-1) 1 at hz
    exact ⟨by linarith [hz.2], by linarith [hz.1]⟩
  have hq := (lensChordCoordinate_continuous τ).continuousOn (s := S)
  have h := (hs.isClosed_le hl hq).inter (hs.isClosed_le hq hr)
  convert h using 1
  ext z
  simp only [lensGraphBody, mem_ofPred_eq, mem_inter_iff, S]
  tauto

theorem lensGraphBody_isCompact {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    IsCompact (lensGraphBody τ) := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨lensGraphBody_isClosed hτ0 hτ1, ?_⟩
  rw [lensGraphBody_eq_convexHull hτ0 hτ1, isBounded_convexHull]
  exact (tiltedLens_image_bounded τ).subset (image_mono (fun z hz => hz.le))

theorem lensGraphBody_mem_interior {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) {z : ℂ}
    (hy : z.im ∈ Ioo (-1) 1)
    (hl : -lensProfile τ (-z.im) < lensChordCoordinate τ z)
    (hr : lensChordCoordinate τ z < lensProfile τ z.im) :
    z ∈ interior (lensGraphBody τ) := by
  have cq := (lensChordCoordinate_continuous τ).continuousAt (x := z)
  have cr : ContinuousAt (fun w : ℂ => lensProfile τ w.im) z := (lensProfile_continuousAt hτ0 hτ1
    (lensHeight_margin_pos_of_le_one hτ0 hτ1 hy.2.le)).comp
      Complex.continuous_im.continuousAt
  have cl : ContinuousAt (fun w : ℂ => -lensProfile τ (-w.im)) z := ((lensProfile_continuousAt hτ0 hτ1
    (lensHeight_margin_pos_of_le_one hτ0 hτ1 (show -z.im ≤ 1 by linarith [hy.1]))).comp
      (f := fun w : ℂ => -w.im)
      Complex.continuous_im.neg.continuousAt).neg
  apply mem_interior_iff_mem_nhds.mpr
  have hlow := continuousAt_const.eventually_lt Complex.continuous_im.continuousAt hy.1
  have hhigh := Complex.continuous_im.continuousAt.eventually_lt continuousAt_const hy.2
  filter_upwards [hlow, hhigh, cl.eventually_lt cq hl, cq.eventually_lt cr hr] with w hw0 hw1 hwl hwr
  exact ⟨⟨hw0.le, hw1.le⟩, hwl.le, hwr.le⟩

theorem lensGraphBody_zero_mem_interior {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    (0 : ℂ) ∈ interior (lensGraphBody τ) := by
  apply lensGraphBody_mem_interior hτ0 hτ1 (by norm_num)
  · simpa [lensChordCoordinate] using neg_neg_of_pos
      (lensProfile_pos hτ0 hτ1 (show (0 : ℝ) ∈ Ioo (-1) 1 by norm_num))
  · simpa [lensChordCoordinate] using
      lensProfile_pos hτ0 hτ1 (show (0 : ℝ) ∈ Ioo (-1) 1 by norm_num)

theorem lensGraphBody_not_interior_right (τ : ℝ) {z : ℂ}
    (he : lensChordCoordinate τ z = lensProfile τ z.im) :
    z ∉ interior (lensGraphBody τ) := by
  intro hi
  obtain ⟨ε, hε, hs⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hi)
  have hm : z + (ε / 2 : ℝ) ∈ Metric.ball z ε := by
    simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  have hh := (hs hm).2.2
  have hq : lensChordCoordinate τ (z + (ε / 2 : ℝ)) = lensChordCoordinate τ z + ε / 2 := by
    simp [lensChordCoordinate]
    ring
  rw [hq, he] at hh
  simp only [Complex.add_im, Complex.ofReal_im, add_zero] at hh
  linarith

theorem lensGraphBody_not_interior_left (τ : ℝ) {z : ℂ}
    (he : lensChordCoordinate τ z = -lensProfile τ (-z.im)) :
    z ∉ interior (lensGraphBody τ) := by
  intro hi
  obtain ⟨ε, hε, hs⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hi)
  have hm : z - (ε / 2 : ℝ) ∈ Metric.ball z ε := by
    simp only [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  have hh := (hs hm).2.1
  have hq : lensChordCoordinate τ (z - (ε / 2 : ℝ)) = lensChordCoordinate τ z - ε / 2 := by
    simp [lensChordCoordinate]
    ring
  rw [hq, he] at hh
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at hh
  linarith

theorem lensCircleImage_eq_arcs {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    lensCircleImage τ = lensRightPoint τ '' Icc (-1) 1 ∪ lensLeftPoint τ '' Icc (-1) 1 := by
  apply Subset.antisymm
  · rintro z ⟨w, hw, rfl⟩
    rw [← circleMap_image_lens_period] at hw
    obtain ⟨θ, hθ, rfl⟩ := hw
    by_cases hr : θ ≤ Real.pi / 2
    · left
      refine ⟨tiltedHeight τ θ, tiltedHeight_mem_Icc hτ0 hτ1 ⟨hθ.1.le, hr⟩, ?_⟩
      simp only [lensRightPoint, lensHeightAngle_tiltedHeight hτ0 hτ1, lensRadialTrace]
    · right
      have hs : θ - Real.pi ∈ Icc (-Real.pi / 2) (Real.pi / 2) :=
        ⟨by linarith, by linarith [hθ.2]⟩
      have hy := tiltedHeight_mem_Icc hτ0 hτ1 hs
      refine ⟨-tiltedHeight τ (θ - Real.pi), ⟨by linarith [hy.2], by linarith [hy.1]⟩, ?_⟩
      simp only [lensLeftPoint, neg_neg, lensRightPoint, lensHeightAngle_tiltedHeight hτ0 hτ1]
      change -lensRadialTrace τ 1 (θ - Real.pi) = lensRadialTrace τ 1 θ
      simpa only [sub_add_cancel] using (lensRadialTrace_add_pi τ (θ - Real.pi)).symm
  · rintro z (⟨y, _, rfl⟩ | ⟨y, _, rfl⟩)
    · exact lensRightPoint_mem_circleImage τ y
    · exact lensLeftPoint_mem_circleImage τ y

theorem lensCircleImage_subset_frontier {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    lensCircleImage τ ⊆ frontier (lensGraphBody τ) := by
  intro z hz
  apply (mem_frontier_iff_notMem_interior (lensCircleImage_subset_graphBody hτ0 hτ1 hz)).mpr
  rw [lensCircleImage_eq_arcs hτ0 hτ1] at hz
  rcases hz with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
  · apply lensGraphBody_not_interior_right
    rw [lensRightPoint_im hτ0 hτ1 hy, lensRightPoint_chord]
  · apply lensGraphBody_not_interior_left
    rw [lensLeftPoint_im hτ0 hτ1 hy, lensLeftPoint_chord]

theorem lensGraphBody_frontier_subset_circleImage {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    frontier (lensGraphBody τ) ⊆ lensCircleImage τ := by
  intro z hz
  have hm : z ∈ lensGraphBody τ := (lensGraphBody_isClosed hτ0 hτ1).closure_eq ▸ hz.1
  have hn : z ∉ interior (lensGraphBody τ) := hz.2
  by_cases hr : lensChordCoordinate τ z = lensProfile τ z.im
  · have he : z = lensRightPoint τ z.im := by
      apply Complex.ext
      · have hq := lensRightPoint_chord τ z.im
        dsimp only [lensChordCoordinate] at hr hq
        rw [lensRightPoint_im hτ0 hτ1 hm.1] at hq
        linarith
      · exact (lensRightPoint_im hτ0 hτ1 hm.1).symm
    rw [he]
    exact lensRightPoint_mem_circleImage τ _
  by_cases hl : lensChordCoordinate τ z = -lensProfile τ (-z.im)
  · have he : z = lensLeftPoint τ z.im := by
      apply Complex.ext
      · have hq := lensLeftPoint_chord τ z.im
        dsimp only [lensChordCoordinate] at hl hq
        rw [lensLeftPoint_im hτ0 hτ1 hm.1] at hq
        linarith
      · exact (lensLeftPoint_im hτ0 hτ1 hm.1).symm
    rw [he]
    exact lensLeftPoint_mem_circleImage τ _
  have hlt : -lensProfile τ (-z.im) < lensChordCoordinate τ z :=
    lt_of_le_of_ne hm.2.1 (fun h => hl h.symm)
  have hrt : lensChordCoordinate τ z < lensProfile τ z.im := lt_of_le_of_ne hm.2.2 hr
  have he := lensProfile_endpoints hτ0 hτ1
  have hy : z.im ∈ Ioo (-1) 1 := by
    constructor
    · apply lt_of_le_of_ne hm.1.1
      intro hh
      simp only [← hh, neg_neg, he.1, he.2] at hlt hrt
      linarith
    · apply lt_of_le_of_ne hm.1.2
      intro hh
      simp only [hh, he.1, he.2] at hlt hrt
      linarith
  exact (hn (lensGraphBody_mem_interior hτ0 hτ1 hy hlt hrt)).elim

/-- The actual circle image is exactly the boundary of the compact convex body. -/
theorem lensGraphBody_frontier_eq_circleImage {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    frontier (lensGraphBody τ) = lensCircleImage τ :=
  Subset.antisymm (lensGraphBody_frontier_subset_circleImage hτ0 hτ1)
    (lensCircleImage_subset_frontier hτ0 hτ1)

/-- A compact centrally symmetric convex body with interior origin whose
frontier is exactly the actual lens image of the unit circle. -/
theorem tiltedLens_convex_boundary {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    IsCompact (lensGraphBody τ) ∧ Convex ℝ (lensGraphBody τ) ∧
      (∀ z ∈ lensGraphBody τ, -z ∈ lensGraphBody τ) ∧
      (0 : ℂ) ∈ interior (lensGraphBody τ) ∧
      frontier (lensGraphBody τ) = tiltedLens τ '' {z : ℂ | ‖z‖ = 1} :=
  ⟨lensGraphBody_isCompact hτ0 hτ1, lensGraphBody_convex hτ0 hτ1,
    fun _ hz => lensGraphBody_neg hz, lensGraphBody_zero_mem_interior hτ0 hτ1,
    lensGraphBody_frontier_eq_circleImage hτ0 hτ1⟩

end
end Funk
