import Funk.LensHeightMeasure
import Funk.LensFrontier
import Mathlib.MeasureTheory.Group.Arithmetic

/-! Normalized angular measure on the actual lens boundary, and its exact
geometric branch/height law. Endpoint tags are irrelevant only after proving
that those endpoints have zero angular measure. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

/-- One full period of normalized angular Lebesgue measure. -/
def lensAngular : Measure ℝ :=
  ENNReal.ofReal (1 / (2 * Real.pi)) •
    volume.restrict (Ioc (-Real.pi / 2) (3 * Real.pi / 2))

/-- This is the pushforward through the actual holomorphic lens boundary. -/
def lensBoundaryMeasure (τ : ℝ) : Measure ℂ :=
  lensAngular.map (lensRadialTrace τ 1)

/-- The tag is determined by which side of the actual endpoint chord contains z. -/
def lensBoundaryCoordinates (τ : ℝ) (z : ℂ) : Bool × ℝ :=
  (if 0 ≤ lensChordCoordinate τ z then true else false, z.im)

theorem measurable_lensBoundaryCoordinates (τ : ℝ) :
    Measurable (lensBoundaryCoordinates τ) := by
  apply Measurable.prodMk
  · exact Measurable.ite
      (measurableSet_le measurable_const (lensChordCoordinate_continuous τ).measurable)
      measurable_const measurable_const
  · exact Complex.continuous_im.measurable

theorem lensHalfAngular_translate :
    lensHalfAngular.map (fun θ => θ + Real.pi) =
      ENNReal.ofReal (1 / (2 * Real.pi)) •
        volume.restrict (Icc (Real.pi / 2) (3 * Real.pi / 2)) := by
  rw [lensHalfAngular, Measure.map_smul _ (by fun_prop)]
  congr 1
  have h := (MeasurableEquiv.addRight Real.pi).restrict_map (volume : Measure ℝ)
    (Icc (Real.pi / 2) (3 * Real.pi / 2))
  have he : (MeasurableEquiv.addRight Real.pi) ⁻¹' Icc (Real.pi / 2) (3 * Real.pi / 2) =
      Icc (-Real.pi / 2) (Real.pi / 2) := by
    ext x
    change (Real.pi / 2 ≤ x + Real.pi ∧ x + Real.pi ≤ 3 * Real.pi / 2) ↔ _
    constructor <;> intro hx <;> constructor <;> linarith [hx.1, hx.2]
  rw [he] at h
  have hm := (measurePreserving_add_right (volume : Measure ℝ) Real.pi).map_eq
  change Measure.map (fun θ : ℝ => θ + Real.pi) volume = volume at hm
  simpa only [MeasurableEquiv.coe_addRight, hm] using h.symm

theorem lensAngular_split :
    lensAngular = lensHalfAngular + lensHalfAngular.map (fun θ => θ + Real.pi) := by
  rw [lensHalfAngular_translate, lensAngular, lensHalfAngular,
    ← restrict_Ioc_eq_restrict_Icc, ← restrict_Ioc_eq_restrict_Icc, ← smul_add]
  congr 1
  rw [← Measure.restrict_union]
  · rw [Ioc_union_Ioc_eq_Ioc (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  · exact Set.disjoint_left.mpr (fun _ hx hy => not_lt_of_ge hx.2 hy.1)
  · exact measurableSet_Ioc

theorem lensAngular_univ : lensAngular univ = 1 := by
  rw [lensAngular_split, Measure.add_apply, Measure.map_apply (by fun_prop) MeasurableSet.univ,
    preimage_univ, lensHalfAngular_univ]
  exact ENNReal.add_halves 1

instance lensAngular_isProbabilityMeasure : IsProbabilityMeasure lensAngular :=
  ⟨lensAngular_univ⟩

theorem lensBoundaryMeasure_isProbability (τ : ℝ) :
    IsProbabilityMeasure (lensBoundaryMeasure τ) := by
  unfold lensBoundaryMeasure
  constructor
  rw [Measure.map_apply (lensBoundary_continuous τ).measurable MeasurableSet.univ,
    preimage_univ, lensAngular_univ]

theorem lensBoundaryCoordinates_right {τ θ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hθ : θ ∈ Ioo (-Real.pi / 2) (Real.pi / 2)) :
    lensBoundaryCoordinates τ (lensRadialTrace τ 1 θ) = (true, tiltedHeight τ θ) := by
  have hq := lensChordCoordinate_pos hτ0 hτ1 hθ
  have hh := lensBoundary_im_eq_tiltedHeight hτ0 hτ1 (Ioo_subset_Icc_self hθ)
  dsimp only at hh
  simp only [lensBoundaryCoordinates, ite_eq_left hq.le, hh]

theorem lensBoundaryCoordinates_left {τ θ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hθ : θ ∈ Ioo (-Real.pi / 2) (Real.pi / 2)) :
    lensBoundaryCoordinates τ (lensRadialTrace τ 1 (θ + Real.pi)) =
      (false, -tiltedHeight τ θ) := by
  have hq := lensChordCoordinate_pos hτ0 hτ1 hθ
  have hh := lensBoundary_im_eq_tiltedHeight hτ0 hτ1 (Ioo_subset_Icc_self hθ)
  dsimp only at hh
  rw [lensRadialTrace_add_pi]
  simp only [lensBoundaryCoordinates, lensChordCoordinate_neg,
    ite_eq_right (show ¬0 ≤ -lensChordCoordinate τ (lensRadialTrace τ 1 θ) by linarith),
    Complex.neg_im, hh]

theorem lensBoundaryMeasure_map_coordinates {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    (lensBoundaryMeasure τ).map (lensBoundaryCoordinates τ) = branchJoint τ := by
  rw [lensBoundaryMeasure, Measure.map_map (measurable_lensBoundaryCoordinates τ)
    (lensBoundary_continuous τ).measurable, lensAngular_split,
    Measure.map_add _ _ ((measurable_lensBoundaryCoordinates τ).comp
      (lensBoundary_continuous τ).measurable),
    Measure.map_map ((measurable_lensBoundaryCoordinates τ).comp
      (lensBoundary_continuous τ).measurable) (by fun_prop)]
  have hr : lensHalfAngular.map (lensBoundaryCoordinates τ ∘ lensRadialTrace τ 1) =
      (branchMeasure τ 1).map (Prod.mk true) := by
    calc
      _ = lensHalfAngular.map (Prod.mk true ∘ lensBranchHeight τ true) := by
        apply Measure.map_congr
        filter_upwards [lensHalfAngular_ae_mem_Ioo] with θ hθ
        exact lensBoundaryCoordinates_right hτ0 hτ1 hθ
      _ = _ := by rw [← Measure.map_map (by fun_prop) (measurable_lensBranchHeight τ true),
        lensBranchHeight_map hτ0 hτ1]; rfl
  have hl : lensHalfAngular.map ((lensBoundaryCoordinates τ ∘ lensRadialTrace τ 1) ∘
        (fun θ => θ + Real.pi)) = (branchMeasure τ (-1)).map (Prod.mk false) := by
    calc
      _ = lensHalfAngular.map (Prod.mk false ∘ lensBranchHeight τ false) := by
        apply Measure.map_congr
        filter_upwards [lensHalfAngular_ae_mem_Ioo] with θ hθ
        exact lensBoundaryCoordinates_left hτ0 hτ1 hθ
      _ = _ := by rw [← Measure.map_map (by fun_prop) (measurable_lensBranchHeight τ false),
        lensBranchHeight_map hτ0 hτ1]; rfl
  rw [hr, hl]
  rfl

end
end Funk
