import Funk.BoundaryEventPartition
import Funk.SharpFlagUpper

/-! The sole remaining cover input, expressed with sorted unsigned real bases and
independent angular samples on the actual holomorphic lens boundary.
Every identity below is exact; none proves the probability-cover inequality. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

/-- Increasing nonsingular selections, with the independent sign chart removed. -/
def unsignedBasisIndices {n m : ℕ} (rows : Fin m → Space n) : Finset (Fin n → Fin m) := by
  classical
  exact Finset.univ.filter (fun s => StrictMono s ∧
    Matrix.det (fun i => rows (s i) : Matrix (Fin n) (Fin n) ℝ) ≠ 0)

theorem mem_unsignedBasisIndices {n m : ℕ} (rows : Fin m → Space n) (s : Fin n → Fin m) :
    s ∈ unsignedBasisIndices rows ↔ StrictMono s ∧
      Matrix.det (fun i => rows (s i) : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  classical
  simp [unsignedBasisIndices]

theorem canonicalBasisIndices_eq_product {n m : ℕ} (rows : Fin m → Space n) :
    canonicalBasisIndices rows = (unsignedBasisIndices rows).product Finset.univ := by
  classical
  ext k
  simp [mem_canonicalBasisIndices, mem_unsignedBasisIndices]

/-- Summing all actual branch events equals summing one direct event for each basis. -/
theorem canonical_probability_sum_eq_unsigned {n m : ℕ}
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) :
    (∑ k ∈ canonicalBasisIndices rows, lensBoundaryRows n τ
      (basisBoundaryEvent τ k.2 (fun i => rows (k.1 i))
        (basisFeasibleRegion τ rows k.1 k.2))) =
      ∑ s ∈ unsignedBasisIndices rows, lensBoundaryRows n τ (boundaryInterpolationEvent τ rows s) := by
  classical
  rw [canonicalBasisIndices_eq_product]
  erw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro s hs
  exact (boundaryInterpolationEvent_probability_eq_sum_signs hτ0 hτ1 rows s
    ((mem_unsignedBasisIndices rows s).mp hs).2).symm

/-- A probability measure on n independent normalized angular coordinates. -/
def lensAngularRows (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => lensAngular)

/-- The literal boundary trace used to sample the complex interpolation event. -/
def lensBoundaryTraceRows (n : ℕ) (τ : ℝ) (θ : Fin n → ℝ) : Fin n → ℂ :=
  fun i => lensRadialTrace τ 1 (θ i)

theorem lensAngularRows_isProbability (n : ℕ) : IsProbabilityMeasure (lensAngularRows n) := by
  unfold lensAngularRows
  infer_instance

theorem measurable_lensBoundaryTraceRows (n : ℕ) (τ : ℝ) :
    Measurable (lensBoundaryTraceRows n τ) := by
  exact Measurable.of_eval (fun i => (lensBoundary_continuous τ).measurable.comp
    (measurable_pi_apply i))

theorem lensAngularRows_map_trace (n : ℕ) (τ : ℝ) :
    (lensAngularRows n).map (lensBoundaryTraceRows n τ) = lensBoundaryRows n τ := by
  let := lensBoundaryMeasure_isProbability τ
  let (_ : Fin n) : SigmaFinite (lensAngular.map (lensRadialTrace τ 1)) := inferInstance
  unfold lensAngularRows lensBoundaryTraceRows lensBoundaryRows lensBoundaryMeasure
  exact Measure.pi_map_pi (fun _ => (lensBoundary_continuous τ).measurable.aemeasurable)

/-- Independent uniform angular samples give exactly the local boundary probability. -/
theorem boundaryInterpolation_probability_eq_angular {n m : ℕ}
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (s : Fin n → Fin m) :
    lensBoundaryRows n τ (boundaryInterpolationEvent τ rows s) =
      lensAngularRows n ((lensBoundaryTraceRows n τ) ⁻¹' boundaryInterpolationEvent τ rows s) := by
  rw [← lensAngularRows_map_trace n τ, Measure.map_apply
    (measurable_lensBoundaryTraceRows n τ)
    (isClosed_boundaryInterpolationEvent hτ0 hτ1 rows s).measurableSet]

/-- A proved unsigned boundary cover would close both frozen main goals. -/
theorem funkAndKalaiGoals_of_unsigned_interpolation_covers
    (cover : ∀ (n : ℕ), 1 ≤ n → ∀ (m : ℕ) (rows : Fin m → Space n),
      SignedIrredundant rows → IsSymmetricConvexBody (stripBody rows) →
      ∀ τ : ℝ, 0 < τ → τ < 1 →
        1 ≤ ∑ s ∈ unsignedBasisIndices rows,
          lensBoundaryRows n τ (boundaryInterpolationEvent τ rows s)) :
    FunkLowerBoundGoal ∧ KalaiFullFlagsGoal := by
  apply funkAndKalaiGoals_of_irredundant_covers
  intro n hn m rows hir hK τ hτ0 hτ1
  rw [canonical_probability_sum_eq_unsigned hτ0 hτ1 rows]
  exact cover n hn m rows hir hK τ hτ0 hτ1

/-- The same final consumer in the angular probability language of the manuscript. -/
theorem funkAndKalaiGoals_of_angular_interpolation_covers
    (cover : ∀ (n : ℕ), 1 ≤ n → ∀ (m : ℕ) (rows : Fin m → Space n),
      SignedIrredundant rows → IsSymmetricConvexBody (stripBody rows) →
      ∀ τ : ℝ, 0 < τ → τ < 1 →
        1 ≤ ∑ s ∈ unsignedBasisIndices rows,
          lensAngularRows n ((lensBoundaryTraceRows n τ) ⁻¹' boundaryInterpolationEvent τ rows s)) :
    FunkLowerBoundGoal ∧ KalaiFullFlagsGoal := by
  apply funkAndKalaiGoals_of_unsigned_interpolation_covers
  intro n hn m rows hir hK τ hτ0 hτ1
  simp_rw [boundaryInterpolation_probability_eq_angular hτ0 hτ1 rows]
  exact cover n hn m rows hir hK τ hτ0 hτ1

end
end Funk
