import Funk.BasisPackingIntegral

/-! An all-dimensional end-to-end check of the basis-event reduction.
For coordinate cubes all mass and non-overlap hypotheses are discharged by
actual boundary probabilities and signed-axis separation certificates. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

theorem cube_basis_event_mass {n : ℕ} {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (b : Fin n → Bool) :
    lensBoundaryRows n τ (basisBoundaryEvent τ b 1 (coordinateCube n)) = (1 / 2) ^ n := by
  have hC : MeasurableSet (coordinateCube n) := by
    rw [coordinateCube_eq_box]
    exact measurableSet_coordinateBox _ _ _
  have he : (basisMap (1 : Matrix (Fin n) (Fin n) ℝ) : Space n → Space n) = id := by
    ext X i
    simp [basisMap]
  rw [basisBoundaryEvent, he, image_id, lensBoundaryRows_region hτ0 hτ1 b hC,
    inter_self]
  have hm := rowBranchMeasure_apply hτ0 hτ1 b MeasurableSet.univ
  rw [univ_inter] at hm
  rw [← hm, rowBranchMeasure]
  let (i : Fin n) := branchMeasure_isFinite hτ0 hτ1 (b i)
  rw [Measure.pi_univ]
  simp [branchMeasure_univ hτ0 hτ1 (branchSign_cases _)]

theorem cube_basis_event_sum (n : ℕ) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    (∑ b : Fin n → Bool,
      lensBoundaryRows n τ (basisBoundaryEvent τ b 1 (coordinateCube n))) = 1 := by
  simp only [cube_basis_event_mass hτ0 hτ1, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  rw [← mul_pow]
  rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]

theorem cube_vertexSimplex_interior_disjoint {n : ℕ} {τ : ℝ} {X : Space n}
    (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hX : X ∈ coordinateCube n)
    {b c : Fin n → Bool} (hbc : b ≠ c) :
    Disjoint (interior (rowSimplex (vertexMatrix τ (fun i => branchSign (b i)) 1 X)))
      (interior (rowSimplex (vertexMatrix τ (fun i => branchSign (c i)) 1 X))) := by
  have ha := signedDiagonal_pairwise_aedisjoint (cubeVertexLengths τ X)
    (fun i d => (cubeVertexLengths_pos hτ0 hτ1 hX i d).le) hbc
  simp only [signedDiagonal_cube_eq_vertexMatrix] at ha
  apply disjoint_iff_inter_eq_empty.mpr
  apply ((isOpen_interior.inter isOpen_interior).measure_eq_zero_iff volume).mp
  exact measure_mono_null (inter_subset_inter interior_subset interior_subset) ha

/-- The new probability route recovers the actual sharp cube lower bound in
all dimensions, independently of the previous direct kernel-integration proof. -/
theorem cube_funk_lower_via_basis_events (n : ℕ) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) ≤
      funkVolume (coordinateCube n) τ := by
  classical
  have hC : MeasurableSet (coordinateCube n) := by
    rw [coordinateCube_eq_box]
    exact measurableSet_coordinateBox _ _ _
  apply funkVolume_strip_lower_of_basis_cover (1 : Matrix (Fin n) (Fin n) ℝ) hC
    hτ0 hτ1 Finset.univ (fun _ : Fin n → Bool => id) id (fun _ => coordinateCube n)
  · intro _ _
    change Matrix.det (1 : Matrix (Fin n) (Fin n) ℝ) ≠ 0
    simp
  · intro _ _
    exact hC
  · intro _ _
    exact Subset.rfl
  · intro X hX b _ c _ hbc _ _
    exact cube_vertexSimplex_interior_disjoint hτ0.le hτ1 hX hbc
  · exact (cube_basis_event_sum n hτ0 hτ1).ge

end
end Funk
