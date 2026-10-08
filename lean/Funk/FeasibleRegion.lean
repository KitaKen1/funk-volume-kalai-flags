import Funk.BasisDensityTransport
import Funk.LensFrontier

/-! Explicit geometric feasible regions. A nonsingular basis reconstructs the
unique real witness from selected boundary points. This does not assert the
upstream covering inequality or disjointness of the resulting simplices. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

/-- True selects the right arc, false the left arc. -/
def lensBranchPoint (τ : ℝ) (b : Bool) (t : ℝ) : ℂ :=
  if b then lensRightPoint τ t else lensLeftPoint τ t

theorem measurable_lensBranchPoint (τ : ℝ) (b : Bool) :
    Measurable (lensBranchPoint τ b) := by
  have ha : Measurable (lensHeightAngle τ) := by unfold lensHeightAngle; fun_prop
  have hr : Measurable (lensRightPoint τ) := (lensBoundary_continuous τ).measurable.comp ha
  cases b
  · exact (hr.comp measurable_neg).neg
  · exact hr

theorem lensBranchPoint_im {τ t : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (b : Bool) (ht : t ∈ Icc (-1) 1) : (lensBranchPoint τ b t).im = t := by
  cases b
  · exact lensLeftPoint_im hτ0 hτ1 ht
  · exact lensRightPoint_im hτ0 hτ1 ht

theorem lensBranchPoint_mem_frontier {τ t : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (b : Bool) : lensBranchPoint τ b t ∈ frontier (lensGraphBody τ) := by
  apply lensCircleImage_subset_frontier hτ0 hτ1
  cases b
  · exact lensLeftPoint_mem_circleImage τ t
  · exact lensRightPoint_mem_circleImage τ t

/-- Real and imaginary row evaluations, with no basis or feasibility assumption. -/
def complexRow {n : ℕ} (row Y X : Space n) : ℂ :=
  ⟨dotProduct row Y, dotProduct row X⟩

/-- The inverse matrix is an explicit, kernel-checked witness. -/
def basisRealWitness {n : ℕ} (τ : ℝ) (b : Fin n → Bool)
    (B : Matrix (Fin n) (Fin n) ℝ) (X : Space n) : Space n :=
  basisMap B⁻¹ (fun i => (lensBranchPoint τ (b i) (basisMap B X i)).re)

theorem measurable_basisRealWitness {n : ℕ} (τ : ℝ) (b : Fin n → Bool)
    (B : Matrix (Fin n) (Fin n) ℝ) : Measurable (basisRealWitness τ b B) := by
  apply (basisMap B⁻¹).continuous.measurable.comp
  apply Measurable.of_eval
  intro i
  exact Complex.measurable_re.comp ((measurable_lensBranchPoint τ (b i)).comp
    ((measurable_pi_apply i).comp (basisMap B).continuous.measurable))

theorem basisMap_realWitness {n : ℕ} (τ : ℝ) (b : Fin n → Bool)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.det ≠ 0) (X : Space n) :
    basisMap B (basisRealWitness τ b B X) =
      (fun i => (lensBranchPoint τ (b i) (basisMap B X i)).re) := by
  change B.mulVec (B⁻¹.mulVec _) = _
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hB),
    Matrix.one_mulVec]

theorem complexRow_realWitness {n : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (b : Fin n → Bool)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.det ≠ 0)
    {X : Space n} (hX : X ∈ stripBody B) (i : Fin n) :
    complexRow (B i) (basisRealWitness τ b B X) X =
      lensBranchPoint τ (b i) (basisMap B X i) := by
  apply Complex.ext
  · exact congr_fun (basisMap_realWitness τ b hB X) i
  · exact (lensBranchPoint_im hτ0 hτ1 (b i) (abs_le.mp (hX i))).symm

theorem basisRealWitness_unique {n : ℕ} (τ : ℝ) (b : Fin n → Bool)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.det ≠ 0) {X Y : Space n}
    (hY : ∀ i, complexRow (B i) Y X = lensBranchPoint τ (b i) (basisMap B X i)) :
    Y = basisRealWitness τ b B X := by
  apply basisMap_injective hB
  rw [basisMap_realWitness τ b hB]
  funext i
  exact congr_arg Complex.re (hY i)

/-- All rows lie in the actual closed lens; selected rows lie on prescribed arcs. -/
def basisFeasibleRegion {n : ℕ} {ι : Type*} (τ : ℝ) (rows : ι → Space n)
    (selected : Fin n → ι) (b : Fin n → Bool) : Set (Space n) :=
  {X | X ∈ stripBody rows ∧ ∀ j,
    complexRow (rows j) (basisRealWitness τ b (fun i => rows (selected i)) X) X ∈
      lensGraphBody τ}

theorem basisFeasibleRegion_subset {n : ℕ} {ι : Type*} (τ : ℝ) (rows : ι → Space n)
    (selected : Fin n → ι) (b : Fin n → Bool) :
    basisFeasibleRegion τ rows selected b ⊆ stripBody rows := fun _ h => h.1

theorem measurableSet_stripBody {n : ℕ} {ι : Type*} [Countable ι] (rows : ι → Space n) :
    MeasurableSet (stripBody rows) := by
  unfold stripBody
  rw [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply measurableSet_le
  · unfold dotProduct; fun_prop
  · exact measurable_const

theorem measurableSet_basisFeasibleRegion {n : ℕ} {ι : Type*} [Countable ι]
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : ι → Space n)
    (selected : Fin n → ι) (b : Fin n → Bool) :
    MeasurableSet (basisFeasibleRegion τ rows selected b) := by
  have hall : MeasurableSet {X : Space n | ∀ j,
      complexRow (rows j) (basisRealWitness τ b
        (fun i => rows (selected i) : Matrix (Fin n) (Fin n) ℝ) X) X ∈ lensGraphBody τ} := by
    rw [ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    apply (lensGraphBody_isClosed hτ0 hτ1).measurableSet.preimage
    have hw := measurable_basisRealWitness τ b (fun i => rows (selected i))
    have hp : Measurable (fun X : Space n =>
        (dotProduct (rows j) (basisRealWitness τ b (fun i => rows (selected i)) X),
          dotProduct (rows j) X)) := by
      unfold dotProduct
      fun_prop
    exact Complex.equivRealProdCLM.symm.continuous.measurable.comp hp
  exact (measurableSet_stripBody rows).inter hall

/-- Eliminate the existential real witness without a projection-measurability theorem. -/
theorem mem_basisFeasibleRegion_iff {n : ℕ} {ι : Type*}
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : ι → Space n)
    (selected : Fin n → ι) (b : Fin n → Bool)
    (hB : Matrix.det (fun i => rows (selected i)) ≠ 0) (X : Space n) :
    X ∈ basisFeasibleRegion τ rows selected b ↔
      X ∈ stripBody rows ∧ ∃ Y : Space n,
        (∀ i, complexRow (rows (selected i)) Y X =
          lensBranchPoint τ (b i) (dotProduct (rows (selected i)) X)) ∧
        ∀ j, complexRow (rows j) Y X ∈ lensGraphBody τ := by
  constructor
  · intro hX
    refine ⟨hX.1, basisRealWitness τ b (fun i => rows (selected i)) X, ?_, hX.2⟩
    exact complexRow_realWitness hτ0 hτ1 b hB (fun i => hX.1 (selected i))
  · rintro ⟨hX, Y, hY, hall⟩
    have he := basisRealWitness_unique τ b hB hY
    exact ⟨hX, he ▸ hall⟩

/-- The earlier exact probability identity now applies to a concrete feasible region. -/
theorem basisFeasibleRegion_probability_volume {n : ℕ} {ι : Type*} [Countable ι]
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : ι → Space n)
    (selected : Fin n → ι) (b : Fin n → Bool)
    (hB : Matrix.det (fun i => rows (selected i)) ≠ 0) :
    lensBoundaryRows n τ (basisBoundaryEvent τ b (fun i => rows (selected i))
      (basisFeasibleRegion τ rows selected b)) =
      basisVolumeFactor n τ * ∫⁻ X in basisFeasibleRegion τ rows selected b,
        volume (rowSimplex (vertexMatrix τ (fun i => branchSign (b i))
          (fun i => rows (selected i)) X)) := by
  apply basisBoundaryEvent_probability_volume hτ0 hτ1 b hB
    (measurableSet_basisFeasibleRegion hτ0 hτ1 rows selected b)
  intro X hX i
  exact hX.1 (selected i)

/-- Every prescribed sign is geometrically feasible when the rows are a basis. -/
theorem basisFeasibleRegion_basis {n : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (b : Fin n → Bool)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.det ≠ 0) :
    basisFeasibleRegion τ B id b = stripBody B := by
  ext X
  constructor
  · exact fun h => h.1
  · intro hX
    refine ⟨hX, ?_⟩
    intro j
    change complexRow (B j) (basisRealWitness τ b B X) X ∈ lensGraphBody τ
    rw [complexRow_realWitness hτ0 hτ1 b hB hX j]
    apply lensCircleImage_subset_graphBody hτ0 hτ1
    cases b j
    · exact lensLeftPoint_mem_circleImage τ _
    · exact lensRightPoint_mem_circleImage τ _

end
end Funk
