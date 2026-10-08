import Funk.LensBoundaryMeasure

/-! Events and independent row products for the actual complex lens boundary.
Independence holds between rows; branch and height within a row remain coupled. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

theorem lensBoundaryMeasure_slice {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (b : Bool) {s : Set ℝ} (hs : MeasurableSet s) :
    lensBoundaryMeasure τ (lensBoundaryCoordinates τ ⁻¹' ({b} ×ˢ s)) =
      branchMeasure τ (branchSign b) s := by
  rw [← Measure.map_apply (measurable_lensBoundaryCoordinates τ)
    ((measurableSet_singleton b).prod hs), lensBoundaryMeasure_map_coordinates hτ0 hτ1]
  exact branchJoint_slice τ b hs

theorem lensBoundaryMeasure_sign_mass {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (b : Bool) :
    lensBoundaryMeasure τ (lensBoundaryCoordinates τ ⁻¹' ({b} ×ˢ (univ : Set ℝ))) =
      1 / 2 := by
  rw [lensBoundaryMeasure_slice hτ0 hτ1 b MeasurableSet.univ]
  exact branchMeasure_univ hτ0 hτ1 (branchSign_cases b)

theorem lensBoundaryMeasure_height_singleton {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (t : ℝ) : lensBoundaryMeasure τ {z | z.im = t} = 0 := by
  have h := branchJoint_height_singleton τ t
  rw [← lensBoundaryMeasure_map_coordinates hτ0 hτ1,
    Measure.map_apply (measurable_lensBoundaryCoordinates τ)
      (MeasurableSet.univ.prod (measurableSet_singleton t))] at h
  simpa only [preimage, mem_prod, mem_univ, mem_singleton_iff, true_and,
    lensBoundaryCoordinates] using h

theorem lensBoundaryMeasure_frontier {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    lensBoundaryMeasure τ (frontier (lensGraphBody τ)) = 1 := by
  have hp : lensRadialTrace τ 1 ⁻¹' frontier (lensGraphBody τ) = univ := by
    apply eq_univ_of_forall
    intro θ
    apply lensCircleImage_subset_frontier hτ0 hτ1
    refine ⟨circleMap 0 1 θ, ?_, rfl⟩
    simp
  rw [lensBoundaryMeasure, Measure.map_apply (lensBoundary_continuous τ).measurable
    isClosed_frontier.measurableSet, hp, lensAngular_univ]

/-- Independent sampling on the actual complex boundary, before taking coordinates. -/
def lensBoundaryRows (m : ℕ) (τ : ℝ) : Measure (Fin m → ℂ) :=
  Measure.pi (fun _ => lensBoundaryMeasure τ)

def lensBoundaryRowCoordinates (m : ℕ) (τ : ℝ) (z : Fin m → ℂ) : Fin m → Bool × ℝ :=
  fun i => lensBoundaryCoordinates τ (z i)

theorem measurable_lensBoundaryRowCoordinates (m : ℕ) (τ : ℝ) :
    Measurable (lensBoundaryRowCoordinates m τ) := by
  exact Measurable.of_eval (fun i =>
    (measurable_lensBoundaryCoordinates τ).comp (measurable_pi_apply i))

theorem lensBoundaryRows_isProbability (m : ℕ) (τ : ℝ) :
    IsProbabilityMeasure (lensBoundaryRows m τ) := by
  let := lensBoundaryMeasure_isProbability τ
  unfold lensBoundaryRows
  infer_instance

theorem lensBoundaryRows_map_coordinates (m : ℕ) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    (lensBoundaryRows m τ).map (lensBoundaryRowCoordinates m τ) = rowJoint m τ := by
  have hi : IsProbabilityMeasure
      ((lensBoundaryMeasure τ).map (lensBoundaryCoordinates τ)) := by
    rw [lensBoundaryMeasure_map_coordinates hτ0 hτ1]
    exact branchJoint_isProbability hτ0 hτ1
  let (i : Fin m) : SigmaFinite
      ((lensBoundaryMeasure τ).map (lensBoundaryCoordinates τ)) := inferInstance
  unfold lensBoundaryRows lensBoundaryRowCoordinates rowJoint
  rw [Measure.pi_map_pi (fun _ => (measurable_lensBoundaryCoordinates τ).aemeasurable)]
  simp only [lensBoundaryMeasure_map_coordinates hτ0 hτ1]

theorem lensBoundaryRows_box (m : ℕ) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (b : Fin m → Bool) (s : Fin m → Set ℝ) (hs : ∀ i, MeasurableSet (s i)) :
    lensBoundaryRows m τ
      (lensBoundaryRowCoordinates m τ ⁻¹' (univ.pi (fun i => {b i} ×ˢ s i))) =
        ∏ i, branchMeasure τ (branchSign (b i)) (s i) := by
  rw [← Measure.map_apply (measurable_lensBoundaryRowCoordinates m τ)
    (MeasurableSet.univ_pi (fun i => (measurableSet_singleton (b i)).prod (hs i))),
    lensBoundaryRows_map_coordinates m hτ0 hτ1]
  exact rowJoint_box m hτ0 hτ1 b s hs

theorem lensBoundaryRows_signs_mass (m : ℕ) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (b : Fin m → Bool) :
    lensBoundaryRows m τ
      (lensBoundaryRowCoordinates m τ ⁻¹' (univ.pi (fun i => {b i} ×ˢ (univ : Set ℝ)))) =
        (1 / 2) ^ m := by
  rw [lensBoundaryRows_box m hτ0 hτ1 b _ (fun _ => MeasurableSet.univ)]
  simp only [branchMeasure_univ hτ0 hτ1 (branchSign_cases _), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- Every nonnegative measurable observable has the same integral under the
actual geometric coordinates and the branch/height model. -/
theorem lensBoundaryMeasure_lintegral {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {g : Bool × ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, g (lensBoundaryCoordinates τ z) ∂lensBoundaryMeasure τ =
      ∫⁻ x, g x ∂branchJoint τ := by
  rw [← lintegral_map hg (measurable_lensBoundaryCoordinates τ),
    lensBoundaryMeasure_map_coordinates hτ0 hτ1]

theorem lensBoundaryRows_lintegral (m : ℕ) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {g : (Fin m → Bool × ℝ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, g (lensBoundaryRowCoordinates m τ z) ∂lensBoundaryRows m τ =
      ∫⁻ x, g x ∂rowJoint m τ := by
  rw [← lintegral_map hg (measurable_lensBoundaryRowCoordinates m τ),
    lensBoundaryRows_map_coordinates m hτ0 hτ1]

theorem lensBoundaryRows_box_density (m : ℕ) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (b : Fin m → Bool) (s : Fin m → Set ℝ) (hs : ∀ i, MeasurableSet (s i)) :
    lensBoundaryRows m τ
      (lensBoundaryRowCoordinates m τ ⁻¹' (univ.pi (fun i => {b i} ×ˢ s i))) =
        ∏ i, ∫⁻ t in s i ∩ Icc (-1) 1, ENNReal.ofReal (branchDensity τ (branchSign (b i)) t) := by
  rw [lensBoundaryRows_box m hτ0 hτ1 b s hs]
  exact Finset.prod_congr rfl (fun i _ => branchMeasure_apply τ (branchSign (b i)) (hs i))

end
end Funk
