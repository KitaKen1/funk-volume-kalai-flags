import Funk.FiniteDensityProduct
import Funk.LensBoundaryProbability
import Funk.CubeFunk

/-! The joint law on arbitrary measurable height regions, retaining fixed signs.
This extends the box-event law to coupled events needed for basis matrices. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

def rowBranchMeasure (n : ℕ) (τ : ℝ) (b : Fin n → Bool) : Measure (Space n) :=
  Measure.pi (fun i => branchMeasure τ (branchSign (b i)))

def rowDensity (n : ℕ) (τ : ℝ) (b : Fin n → Bool) (t : Space n) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal (branchDensity τ (branchSign (b i)) (t i))

def rowTag {n : ℕ} (b : Fin n → Bool) (t : Space n) : Fin n → Bool × ℝ :=
  fun i => (b i, t i)

def rowHeights {n : ℕ} (x : Fin n → Bool × ℝ) : Space n := fun i => (x i).2

def rowSignSet {n : ℕ} (b : Fin n → Bool) : Set (Fin n → Bool × ℝ) :=
  univ.pi (fun i => {b i} ×ˢ (univ : Set ℝ))

theorem measurable_rowDensity (n : ℕ) (τ : ℝ) (b : Fin n → Bool) :
    Measurable (rowDensity n τ b) := by
  apply Finset.measurable_prod
  intro i _
  exact (measurable_branchDensity τ (branchSign (b i))).ennreal_ofReal.comp
    (measurable_pi_apply i)

theorem measurable_rowTag {n : ℕ} (b : Fin n → Bool) : Measurable (rowTag b) := by
  unfold rowTag
  fun_prop

theorem measurable_rowHeights (n : ℕ) : Measurable (@rowHeights n) := by
  unfold rowHeights
  fun_prop

theorem measurableSet_rowSignSet {n : ℕ} (b : Fin n → Bool) :
    MeasurableSet (rowSignSet b) :=
  MeasurableSet.univ_pi (fun i => (measurableSet_singleton (b i)).prod MeasurableSet.univ)

theorem branchMeasure_isFinite {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (b : Bool) :
    IsFiniteMeasure (branchMeasure τ (branchSign b)) :=
  ⟨by rw [branchMeasure_univ hτ0 hτ1 (branchSign_cases b)]; norm_num⟩

theorem rowBranchMeasure_withDensity {n : ℕ} {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (b : Fin n → Bool) :
    rowBranchMeasure n τ b = (volume.restrict (coordinateCube n)).withDensity (rowDensity n τ b) := by
  let (i : Fin n) := branchMeasure_isFinite hτ0 hτ1 (b i)
  unfold rowBranchMeasure branchMeasure rowDensity
  rw [pi_withDensity_fin (fun i => (measurable_branchDensity τ (branchSign (b i))).ennreal_ofReal)]
  rw [coordinateCube_eq_box, coordinateBox,
    show (volume : Measure (Space n)) = Measure.pi (fun _ => volume) from rfl,
    Measure.restrict_pi_pi]

theorem rowBranchMeasure_apply {n : ℕ} {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (b : Fin n → Bool) {s : Set (Space n)} (hs : MeasurableSet s) :
    rowBranchMeasure n τ b s = ∫⁻ t in s ∩ coordinateCube n, rowDensity n τ b t := by
  rw [rowBranchMeasure_withDensity hτ0 hτ1 b, withDensity_apply _ hs,
    Measure.restrict_restrict hs]

theorem branchJoint_restrict_sign (τ : ℝ) (b : Bool) :
    (branchJoint τ).restrict ({b} ×ˢ (univ : Set ℝ)) =
      (branchMeasure τ (branchSign b)).map (Prod.mk b) := by
  rw [branchJoint, Measure.restrict_add,
    Measure.restrict_map (by fun_prop) ((measurableSet_singleton b).prod MeasurableSet.univ),
    Measure.restrict_map (by fun_prop) ((measurableSet_singleton b).prod MeasurableSet.univ)]
  cases b <;> simp [branchSign]

theorem rowJoint_restrict_sign {n : ℕ} {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (b : Fin n → Bool) :
    (rowJoint n τ).restrict (rowSignSet b) = (rowBranchMeasure n τ b).map (rowTag b) := by
  let := branchJoint_isProbability hτ0 hτ1
  let (i : Fin n) := branchMeasure_isFinite hτ0 hτ1 (b i)
  rw [rowJoint, rowSignSet, Measure.restrict_pi_pi]
  simp_rw [branchJoint_restrict_sign]
  rw [← Measure.pi_map_pi (fun _ => (by fun_prop))]
  rfl

theorem rowJoint_region {n : ℕ} {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (b : Fin n → Bool) {s : Set (Space n)} (hs : MeasurableSet s) :
    rowJoint n τ (rowSignSet b ∩ rowHeights ⁻¹' s) = rowBranchMeasure n τ b s := by
  rw [inter_comm, ← Measure.restrict_apply ((measurable_rowHeights n) hs),
    rowJoint_restrict_sign hτ0 hτ1 b,
    Measure.map_apply (measurable_rowTag b) ((measurable_rowHeights n) hs)]
  rfl

theorem lensBoundaryRows_region {n : ℕ} {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (b : Fin n → Bool) {s : Set (Space n)} (hs : MeasurableSet s) :
    lensBoundaryRows n τ (lensBoundaryRowCoordinates n τ ⁻¹'
      (rowSignSet b ∩ rowHeights ⁻¹' s)) =
        ∫⁻ t in s ∩ coordinateCube n, rowDensity n τ b t := by
  rw [← Measure.map_apply (measurable_lensBoundaryRowCoordinates n τ)
    ((measurableSet_rowSignSet b).inter ((measurable_rowHeights n) hs)),
    lensBoundaryRows_map_coordinates n hτ0 hτ1, rowJoint_region hτ0 hτ1 b hs,
    rowBranchMeasure_apply hτ0 hτ1 b hs]

end
end Funk
