import Funk.FeasibleFunk
import Funk.SeparationCertificate

/-! The actual real witnesses supply separating linear functionals. Distinct
witnesses imply non-overlap. Collisions of different bases at one witness are
not excluded by this file and remain a separate geometric obligation. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

/-- A branch endpoint maximizes its signed horizontal coordinate in its slice. -/
theorem lensBranchPoint_support {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (b : Bool) {z : ℂ} (hz : z ∈ lensGraphBody τ) :
    branchSign b * z.re ≤ branchSign b * (lensBranchPoint τ b z.im).re := by
  cases b
  · have hc := lensLeftPoint_chord τ z.im
    have hi := lensLeftPoint_im hτ0 hτ1 hz.1
    have hl := hz.2.1
    dsimp only [lensChordCoordinate] at hc hl
    rw [hi] at hc
    change -1 * z.re ≤ -1 * (lensLeftPoint τ z.im).re
    linarith
  · have hc := lensRightPoint_chord τ z.im
    have hi := lensRightPoint_im hτ0 hτ1 hz.1
    have hr := hz.2.2
    dsimp only [lensChordCoordinate] at hc hr
    rw [hi] at hc
    change 1 * z.re ≤ 1 * (lensRightPoint τ z.im).re
    linarith

/-- The known polar vertex is a positive rescaling of the slice support normal. -/
theorem polarVertex_support_difference {n : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (b : Bool) (row X Y Z : Space n)
    (hX : |dotProduct row X| ≤ 1)
    (hY : complexRow row Y X = lensBranchPoint τ b (dotProduct row X))
    (hZ : complexRow row Z X ∈ lensGraphBody τ) :
    0 ≤ dotProduct (polarVertex τ (branchSign b) row X) (Y - Z) := by
  have hs := lensBranchPoint_support hτ0 hτ1 b hZ
  have he := congr_arg Complex.re hY
  change dotProduct row Y = _ at he
  change branchSign b * dotProduct row Z ≤
    branchSign b * (lensBranchPoint τ b (dotProduct row X)).re at hs
  rw [← he] at hs
  have hp : 0 < 1 - branchSign b * τ * dotProduct row X :=
    denominator_pos hτ0.le hτ1 (branchSign_cases b) hX
  simp only [polarVertex, smul_dotProduct, dotProduct_sub, smul_eq_mul]
  rw [div_mul_eq_mul_div]
  have hn : 0 ≤ branchSign b * (dotProduct row Y - dotProduct row Z) := by nlinarith
  convert div_nonneg hn hp.le using 1
  ring

/-- The separating functional is constructed, not requested as an input. -/
def witnessSeparator {n : ℕ} (Y Z : Space n) : Space n →ₗ[ℝ] ℝ :=
  dotProductBilin ℝ ℝ (Y - Z)

theorem witnessSeparator_swap {n : ℕ} (Y Z v : Space n) :
    witnessSeparator Y Z v = -witnessSeparator Z Y v := by
  change dotProduct (Y - Z) v = -dotProduct (Z - Y) v
  rw [sub_dotProduct, sub_dotProduct]
  ring

theorem witnessSeparator_ne_zero {n : ℕ} {Y Z : Space n} (hYZ : Y ≠ Z) :
    witnessSeparator Y Z ≠ 0 := by
  intro h
  have he := LinearMap.congr_fun h (Y - Z)
  change dotProduct (Y - Z) (Y - Z) = 0 at he
  exact hYZ (sub_eq_zero.mp (dotProduct_self_eq_zero.mp he))

theorem feasible_vertex_separator_nonneg {n : ℕ} {ι : Type*}
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : ι → Space n)
    (s t : Fin n → ι) (b c : Fin n → Bool)
    (hB : Matrix.det (fun i => rows (s i)) ≠ 0) {X : Space n}
    (hS : X ∈ basisFeasibleRegion τ rows s b)
    (hT : X ∈ basisFeasibleRegion τ rows t c) (i : Fin n) :
    0 ≤ witnessSeparator (basisRealWitness τ b (fun j => rows (s j)) X)
      (basisRealWitness τ c (fun j => rows (t j)) X)
      (vertexMatrix τ (fun j => branchSign (b j)) (fun j => rows (s j)) X i) := by
  change 0 ≤ dotProduct _ (polarVertex τ (branchSign (b i)) (rows (s i)) X)
  rw [dotProduct_comm]
  exact polarVertex_support_difference hτ0 hτ1 (b i) _ _ _ _ (hS.1 (s i))
    (complexRow_realWitness hτ0 hτ1 b hB (fun j => hS.1 (s j)) i) (hT.2 (s i))

theorem feasible_vertex_separator_nonpos {n : ℕ} {ι : Type*}
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : ι → Space n)
    (s t : Fin n → ι) (b c : Fin n → Bool)
    (hC : Matrix.det (fun i => rows (t i)) ≠ 0) {X : Space n}
    (hS : X ∈ basisFeasibleRegion τ rows s b)
    (hT : X ∈ basisFeasibleRegion τ rows t c) (i : Fin n) :
    witnessSeparator (basisRealWitness τ b (fun j => rows (s j)) X)
      (basisRealWitness τ c (fun j => rows (t j)) X)
      (vertexMatrix τ (fun j => branchSign (c j)) (fun j => rows (t j)) X i) ≤ 0 := by
  have h := feasible_vertex_separator_nonneg hτ0 hτ1 rows t s c b hC hT hS i
  rw [witnessSeparator_swap]
  exact neg_nonpos.mpr h

/-- No generic-position or null-exception claim is needed for distinct witnesses. -/
theorem feasible_simplex_aedisjoint_of_witness_ne {n : ℕ} {ι : Type*}
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : ι → Space n)
    (s t : Fin n → ι) (b c : Fin n → Bool)
    (hB : Matrix.det (fun i => rows (s i)) ≠ 0)
    (hC : Matrix.det (fun i => rows (t i)) ≠ 0) {X : Space n}
    (hS : X ∈ basisFeasibleRegion τ rows s b)
    (hT : X ∈ basisFeasibleRegion τ rows t c)
    (hne : basisRealWitness τ b (fun i => rows (s i)) X ≠
      basisRealWitness τ c (fun i => rows (t i)) X) :
    AEDisjoint volume
      (rowSimplex (vertexMatrix τ (fun i => branchSign (b i)) (fun i => rows (s i)) X))
      (rowSimplex (vertexMatrix τ (fun i => branchSign (c i)) (fun i => rows (t i)) X)) :=
  rowSimplex_aedisjoint_of_separator _ _ _ (witnessSeparator_ne_zero hne)
    (feasible_vertex_separator_nonneg hτ0 hτ1 rows s t b c hB hS hT)
    (feasible_vertex_separator_nonpos hτ0 hτ1 rows s t b c hC hS hT)

theorem feasible_simplex_interior_disjoint_of_witness_ne {n : ℕ} {ι : Type*}
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : ι → Space n)
    (s t : Fin n → ι) (b c : Fin n → Bool)
    (hB : Matrix.det (fun i => rows (s i)) ≠ 0)
    (hC : Matrix.det (fun i => rows (t i)) ≠ 0) {X : Space n}
    (hS : X ∈ basisFeasibleRegion τ rows s b)
    (hT : X ∈ basisFeasibleRegion τ rows t c)
    (hne : basisRealWitness τ b (fun i => rows (s i)) X ≠
      basisRealWitness τ c (fun i => rows (t i)) X) :
    Disjoint
      (interior (rowSimplex (vertexMatrix τ (fun i => branchSign (b i)) (fun i => rows (s i)) X)))
      (interior (rowSimplex (vertexMatrix τ (fun i => branchSign (c i)) (fun i => rows (t i)) X))) := by
  apply disjoint_iff_inter_eq_empty.mpr
  apply ((isOpen_interior.inter isOpen_interior).measure_eq_zero_iff volume).mp
  exact measure_mono_null (inter_subset_inter interior_subset interior_subset)
    (feasible_simplex_aedisjoint_of_witness_ne hτ0 hτ1 rows s t b c hB hC hS hT hne)

end
end Funk
