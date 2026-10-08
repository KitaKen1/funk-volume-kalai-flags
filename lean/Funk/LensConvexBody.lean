import Funk.LensConcavity
import Funk.LensBoundaryInjective
import Mathlib.Analysis.Convex.Hull

/-! The region between the two actual height-parametrized arcs is convex and
equals the convex hull of the actual unit-circle image.  This file does not
identify it with the image of the disk under the holomorphic lens map. -/

open Set

namespace Funk
noncomputable section

def lensRightPoint (τ y : ℝ) : ℂ := lensRadialTrace τ 1 (lensHeightAngle τ y)

def lensLeftPoint (τ y : ℝ) : ℂ := -lensRightPoint τ (-y)

def lensCircleImage (τ : ℝ) : Set ℂ := tiltedLens τ '' {z : ℂ | ‖z‖ = 1}

/-- Horizontal slices between the actual two arcs, using a linear shear. -/
def lensGraphBody (τ : ℝ) : Set ℂ :=
  {z | z.im ∈ Icc (-1) 1 ∧ -lensProfile τ (-z.im) ≤ lensChordCoordinate τ z ∧
    lensChordCoordinate τ z ≤ lensProfile τ z.im}

theorem lensChordCoordinate_combo (τ : ℝ) (z w : ℂ) (a b : ℝ) :
    lensChordCoordinate τ (a • z + b • w) =
      a * lensChordCoordinate τ z + b * lensChordCoordinate τ w := by
  simp [lensChordCoordinate]
  ring

theorem lensRightPoint_im {τ y : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hy : y ∈ Icc (-1) 1) : (lensRightPoint τ y).im = y := by
  exact (lensBoundary_im_eq_tiltedHeight hτ0 hτ1
    (lensHeightAngle_mem_Icc hτ0 hτ1 hy)).trans
    (tiltedHeight_lensHeightAngle hτ0 hτ1
      (lensHeight_margin_pos_of_le_one hτ0 hτ1 hy.2))

theorem lensLeftPoint_im {τ y : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hy : y ∈ Icc (-1) 1) : (lensLeftPoint τ y).im = y := by
  rw [lensLeftPoint, Complex.neg_im, lensRightPoint_im hτ0 hτ1
    ⟨by linarith [hy.2], by linarith [hy.1]⟩, neg_neg]

theorem lensRightPoint_chord (τ y : ℝ) :
    lensChordCoordinate τ (lensRightPoint τ y) = lensProfile τ y := rfl

theorem lensLeftPoint_chord (τ y : ℝ) :
    lensChordCoordinate τ (lensLeftPoint τ y) = -lensProfile τ (-y) := by
  rw [lensLeftPoint, lensChordCoordinate_neg, lensRightPoint_chord]

theorem lensRightPoint_mem_circleImage (τ y : ℝ) :
    lensRightPoint τ y ∈ lensCircleImage τ := by
  refine ⟨circleMap 0 1 (lensHeightAngle τ y), ?_, rfl⟩
  simp

theorem lensLeftPoint_mem_circleImage (τ y : ℝ) :
    lensLeftPoint τ y ∈ lensCircleImage τ := by
  refine ⟨-circleMap 0 1 (lensHeightAngle τ (-y)), ?_, ?_⟩
  · simp
  · exact tiltedLens_neg τ _

theorem lensGraphBody_neg {τ : ℝ} {z : ℂ} (hz : z ∈ lensGraphBody τ) :
    -z ∈ lensGraphBody τ := by
  rcases hz with ⟨hy, hl, hr⟩
  simp only [lensGraphBody, mem_ofPred_eq, Complex.neg_im, lensChordCoordinate_neg, neg_neg]
  exact ⟨⟨by linarith [hy.2], by linarith [hy.1]⟩, by linarith, by linarith⟩

theorem lensGraphBody_convex {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    Convex ℝ (lensGraphBody τ) := by
  intro z hz w hw a b ha hb hab
  have hq := lensProfile_concaveOn hτ0 hτ1
  have hz' : -z.im ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hz.1.2], by linarith [hz.1.1]⟩
  have hw' : -w.im ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hw.1.2], by linarith [hw.1.1]⟩
  have hr := hq.2 hz.1 hw.1 ha hb hab
  have hl := hq.2 hz' hw' ha hb hab
  simp only [smul_eq_mul] at hr hl
  have him : (a • z + b • w).im = a * z.im + b * w.im := by simp
  change (a • z + b • w).im ∈ Icc (-1) 1 ∧ _
  rw [him, lensChordCoordinate_combo]
  refine ⟨(convex_Icc (-1 : ℝ) 1) hz.1 hw.1 ha hb hab, ?_, ?_⟩
  · have he : -(a * z.im + b * w.im) = a * -z.im + b * -w.im := by ring
    rw [he]
    calc
      -lensProfile τ (a * -z.im + b * -w.im) ≤
          a * (-lensProfile τ (-z.im)) + b * (-lensProfile τ (-w.im)) := by linarith
      _ ≤ a * lensChordCoordinate τ z + b * lensChordCoordinate τ w :=
        add_le_add (mul_le_mul_of_nonneg_left hz.2.1 ha)
          (mul_le_mul_of_nonneg_left hw.2.1 hb)
  · exact (add_le_add (mul_le_mul_of_nonneg_left hz.2.2 ha)
      (mul_le_mul_of_nonneg_left hw.2.2 hb)).trans hr

theorem lensRightPoint_mem_graphBody {τ y : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hy : y ∈ Icc (-1) 1) : lensRightPoint τ y ∈ lensGraphBody τ := by
  change (lensRightPoint τ y).im ∈ Icc (-1) 1 ∧ _
  rw [lensRightPoint_im hτ0 hτ1 hy, lensRightPoint_chord]
  refine ⟨hy, ?_, le_rfl⟩
  have hn := lensProfile_nonneg hτ0 hτ1 hy
  have hp := lensProfile_nonneg hτ0 hτ1
    (show -y ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hy.2], by linarith [hy.1]⟩)
  linarith

theorem lensRightArc_mem_graphBody {τ θ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hθ : θ ∈ Icc (-Real.pi / 2) (Real.pi / 2)) :
    lensRadialTrace τ 1 θ ∈ lensGraphBody τ := by
  have h := lensRightPoint_mem_graphBody hτ0 hτ1 (tiltedHeight_mem_Icc hτ0 hτ1 hθ)
  simpa only [lensRightPoint, lensHeightAngle_tiltedHeight hτ0 hτ1] using h

theorem lensCircleImage_subset_graphBody {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    lensCircleImage τ ⊆ lensGraphBody τ := by
  rintro z ⟨w, hw, rfl⟩
  rw [← circleMap_image_lens_period] at hw
  obtain ⟨θ, hθ, rfl⟩ := hw
  change lensRadialTrace τ 1 θ ∈ lensGraphBody τ
  by_cases hr : θ ≤ Real.pi / 2
  · exact lensRightArc_mem_graphBody hτ0 hτ1 ⟨hθ.1.le, hr⟩
  · have hs : θ - Real.pi ∈ Icc (-Real.pi / 2) (Real.pi / 2) :=
      ⟨by linarith, by linarith [hθ.2]⟩
    have he : lensRadialTrace τ 1 θ = -lensRadialTrace τ 1 (θ - Real.pi) := by
      simpa only [sub_add_cancel] using lensRadialTrace_add_pi τ (θ - Real.pi)
    rw [he]
    exact lensGraphBody_neg (lensRightArc_mem_graphBody hτ0 hτ1 hs)

/-- Every slice point is an actual convex combination of its two arc endpoints. -/
theorem lensGraphBody_subset_convexHull {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    lensGraphBody τ ⊆ convexHull ℝ (lensCircleImage τ) := by
  intro z hz
  obtain ⟨a, b, ha, hb, hab, hc⟩ := (Convex.mem_Icc (hz.2.1.trans hz.2.2)).mp hz.2
  have he : a • lensLeftPoint τ z.im + b • lensRightPoint τ z.im = z := by
    have him : (a • lensLeftPoint τ z.im + b • lensRightPoint τ z.im).im = z.im := by
      simp only [Complex.add_im, Complex.smul_im, smul_eq_mul,
        lensLeftPoint_im hτ0 hτ1 hz.1, lensRightPoint_im hτ0 hτ1 hz.1]
      rw [← add_mul, hab, one_mul]
    have hch : lensChordCoordinate τ (a • lensLeftPoint τ z.im + b • lensRightPoint τ z.im) =
        lensChordCoordinate τ z := by
      rw [lensChordCoordinate_combo, lensLeftPoint_chord, lensRightPoint_chord]
      exact hc
    apply Complex.ext
    · dsimp only [lensChordCoordinate] at hch
      rw [him] at hch
      linarith
    · exact him
  rw [← he]
  exact (convex_convexHull ℝ (lensCircleImage τ))
    (subset_convexHull ℝ _ (lensLeftPoint_mem_circleImage τ z.im))
    (subset_convexHull ℝ _ (lensRightPoint_mem_circleImage τ z.im)) ha hb hab

theorem lensGraphBody_eq_convexHull {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    lensGraphBody τ = convexHull ℝ (lensCircleImage τ) :=
  Subset.antisymm (lensGraphBody_subset_convexHull hτ0 hτ1)
    (convexHull_min (lensCircleImage_subset_graphBody hτ0 hτ1)
      (lensGraphBody_convex hτ0 hτ1))

end
end Funk
