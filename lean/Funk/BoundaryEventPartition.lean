import Funk.BoundaryInterpolation
import Funk.CanonicalBasisFamily

/-! Exact sign partition of actual direct boundary interpolation probabilities.
This removes sign/height charts from the remaining probability-cover specification.
The inequality itself is not assumed to follow from this event identification. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

/-- Decode the existing event without any boundary or invertibility assumption. -/
theorem mem_basisBoundaryEvent_coordinates {n : ℕ} (τ : ℝ) (b : Fin n → Bool)
    (B : Matrix (Fin n) (Fin n) ℝ) (S : Set (Space n)) (z : Fin n → ℂ) :
    z ∈ basisBoundaryEvent τ b B S ↔
      (∀ i, (lensBoundaryCoordinates τ (z i)).1 = b i) ∧
      ∃ X ∈ S, ∀ i, dotProduct (B i) X = (z i).im := by
  change (lensBoundaryRowCoordinates n τ z ∈ rowSignSet b ∧
    rowHeights (lensBoundaryRowCoordinates n τ z) ∈ basisMap B '' S) ↔ _
  have ht : lensBoundaryRowCoordinates n τ z ∈ rowSignSet b ↔
      ∀ i, (lensBoundaryCoordinates τ (z i)).1 = b i := by
    simp [rowSignSet, lensBoundaryRowCoordinates]
  rw [ht]
  constructor
  · rintro ⟨hb, X, hX, he⟩
    exact ⟨hb, X, hX, fun i => congrFun he i⟩
  · rintro ⟨hb, X, hX, he⟩
    exact ⟨hb, X, hX, funext he⟩

/-- On genuine boundary samples, sign/height feasibility is precisely direct interpolation. -/
theorem basisBoundaryEvent_iff_interpolation_on_frontier {n : ℕ} {ι : Type*}
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : ι → Space n) (s : Fin n → ι)
    (hB : Matrix.det (fun i => rows (s i)) ≠ 0) (b : Fin n → Bool) (z : Fin n → ℂ)
    (hz : ∀ i, z i ∈ frontier (lensGraphBody τ)) :
    z ∈ basisBoundaryEvent τ b (fun i => rows (s i)) (basisFeasibleRegion τ rows s b) ↔
      (∀ i, (lensBoundaryCoordinates τ (z i)).1 = b i) ∧
      z ∈ boundaryInterpolationEvent τ rows s := by
  erw [mem_basisBoundaryEvent_coordinates τ b (fun i => rows (s i))
    (basisFeasibleRegion τ rows s b) z]
  constructor
  · rintro ⟨hb, X, hX, he⟩
    obtain ⟨_, Y, hY, hall⟩ := (mem_basisFeasibleRegion_iff hτ0 hτ1 rows s b hB X).mp hX
    refine ⟨hb, (mem_boundaryInterpolationEvent_iff τ rows s hB z).mpr ⟨Y, X, ?_, hall⟩⟩
    intro i
    rw [hY i, he i]
    have hr := lensBranchPoint_boundaryCoordinates hτ0 hτ1 (hz i)
    change lensBranchPoint τ (lensBoundaryCoordinates τ (z i)).1 (z i).im = z i at hr
    rw [hb i] at hr
    exact hr
  · rintro ⟨hb, hevent⟩
    obtain ⟨Y, X, hY, hall⟩ := (mem_boundaryInterpolationEvent_iff τ rows s hB z).mp hevent
    have hi (i : Fin n) : dotProduct (rows (s i)) X = (z i).im := congrArg Complex.im (hY i)
    have hX : X ∈ stripBody rows := by
      intro j
      exact abs_le.mpr (hall j).1
    refine ⟨hb, X, (mem_basisFeasibleRegion_iff hτ0 hτ1 rows s b hB X).mpr
      ⟨hX, Y, ?_, hall⟩, hi⟩
    intro i
    rw [hY i, hi i]
    have hr := lensBranchPoint_boundaryCoordinates hτ0 hτ1 (hz i)
    change lensBranchPoint τ (lensBoundaryCoordinates τ (z i)).1 (z i).im = z i at hr
    rw [hb i] at hr
    exact hr.symm

/-- Different sign vectors describe disjoint events, including endpoint tag conventions. -/
theorem basisBoundaryEvent_pairwiseDisjoint {n : ℕ} (τ : ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (S : (Fin n → Bool) → Set (Space n)) :
    Pairwise (fun b c => Disjoint (basisBoundaryEvent τ b B (S b))
      (basisBoundaryEvent τ c B (S c))) := by
  intro b c hbc
  apply Set.disjoint_left.mpr
  intro z hb hc
  have ht := (mem_basisBoundaryEvent_coordinates τ b B (S b) z).mp hb
  have hu := (mem_basisBoundaryEvent_coordinates τ c B (S c) z).mp hc
  apply hbc
  funext i
  exact (ht.1 i).symm.trans (hu.1 i)

/-- Every actual sampled row lies on the actual lens frontier almost everywhere. -/
theorem lensBoundaryRows_ae_frontier (n : ℕ) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ∀ᵐ z ∂lensBoundaryRows n τ, ∀ i, z i ∈ frontier (lensGraphBody τ) := by
  let := lensBoundaryRows_isProbability n τ
  let := lensBoundaryMeasure_isProbability τ
  have hm : lensBoundaryRows n τ (univ.pi (fun _ => frontier (lensGraphBody τ))) = 1 := by
    rw [lensBoundaryRows, Measure.pi_pi]
    simp only [lensBoundaryMeasure_frontier hτ0 hτ1, Finset.prod_const_one]
  have ha := (mem_ae_iff_prob_eq_one
    (MeasurableSet.univ_pi (fun _ : Fin n => isClosed_frontier.measurableSet))).mpr hm
  change ∀ᵐ z ∂lensBoundaryRows n τ, z ∈ univ.pi (fun _ => frontier (lensGraphBody τ)) at ha
  simpa only [mem_pi, mem_univ, forall_const] using ha

/-- The direct event is the union of the sign-specific events almost everywhere. -/
theorem boundaryInterpolationEvent_ae_eq_sign_union {n : ℕ} {ι : Type*}
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : ι → Space n) (s : Fin n → ι)
    (hB : Matrix.det (fun i => rows (s i)) ≠ 0) :
    boundaryInterpolationEvent τ rows s =ᵐ[lensBoundaryRows n τ]
      ⋃ b : Fin n → Bool, basisBoundaryEvent τ b (fun i => rows (s i))
        (basisFeasibleRegion τ rows s b) := by
  filter_upwards [lensBoundaryRows_ae_frontier n hτ0 hτ1] with z hz
  apply propext
  simp only [mem_iUnion]
  constructor
  · intro he
    let b : Fin n → Bool := fun i => (lensBoundaryCoordinates τ (z i)).1
    exact ⟨b, (basisBoundaryEvent_iff_interpolation_on_frontier hτ0 hτ1 rows s hB b z hz).mpr
      ⟨fun _ => rfl, he⟩⟩
  · rintro ⟨b, hb⟩
    exact ((basisBoundaryEvent_iff_interpolation_on_frontier hτ0 hτ1 rows s hB b z hz).mp hb).2

/-- Exact probability identity: summing signs recovers the untagged boundary event. -/
theorem boundaryInterpolationEvent_probability_eq_sum_signs {n : ℕ} {ι : Type*} [Countable ι]
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : ι → Space n) (s : Fin n → ι)
    (hB : Matrix.det (fun i => rows (s i)) ≠ 0) :
    lensBoundaryRows n τ (boundaryInterpolationEvent τ rows s) =
      ∑ b : Fin n → Bool, lensBoundaryRows n τ
        (basisBoundaryEvent τ b (fun i => rows (s i)) (basisFeasibleRegion τ rows s b)) := by
  rw [measure_congr (boundaryInterpolationEvent_ae_eq_sign_union hτ0 hτ1 rows s hB),
    measure_iUnion (basisBoundaryEvent_pairwiseDisjoint τ (fun i => rows (s i))
      (basisFeasibleRegion τ rows s))
      (fun b => measurableSet_basisBoundaryEvent τ b hB
        (measurableSet_basisFeasibleRegion hτ0 hτ1 rows s b)), tsum_fintype]

end
end Funk
