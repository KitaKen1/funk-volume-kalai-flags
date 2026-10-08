import Funk.IrredundantRows

/-! Irredundancy alone is not pointwise simplicity. Four irredundant strip rows
of the three-dimensional octahedron all meet at one actual lens witness when
X = 0. This example does not refute almost-everywhere simplicity or either goal. -/

open Set

namespace Funk
noncomputable section

def octahedralRows : Fin 4 → Space 3 :=
  ![![1, 1, 1], ![1, 1, -1], ![1, -1, 1], ![1, -1, -1]]

theorem octahedralRows_signedIrredundant : SignedIrredundant octahedralRows := by
  intro i hi
  have hs : octahedralRows i ∈
      stripBody (fun k : {k : Fin 4 // k ≠ i} => octahedralRows k.val) := by
    intro k
    obtain ⟨j, hj⟩ := k
    fin_cases i <;> fin_cases j
    all_goals first | exact (hj rfl).elim | norm_num [octahedralRows, dotProduct, Fin.sum_univ_succ]
  have h := strip_constraint_of_mem_signedRowHull _ hs hi
  fin_cases i <;> norm_num [octahedralRows, dotProduct, Fin.sum_univ_succ] at h

theorem octahedralRows_basis_det :
    Matrix.det (fun i : Fin 3 => octahedralRows i.castSucc) ≠ 0 := by
  have he : (fun i : Fin 3 => octahedralRows i.castSucc : Matrix (Fin 3) (Fin 3) ℝ) =
      !![1, 1, 1; 1, 1, -1; 1, -1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [he]
  norm_num [Matrix.det_fin_three]

/-- At zero imaginary part, all four rows meet at the same right-arc point. -/
theorem octahedralRows_common_witness {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (j : Fin 4) :
    complexRow (octahedralRows j) ![(lensBranchPoint τ true 0).re, 0, 0] 0 =
      lensBranchPoint τ true 0 := by
  apply Complex.ext
  · fin_cases j <;> simp [octahedralRows, complexRow, dotProduct, Fin.sum_univ_succ]
  · change dotProduct (octahedralRows j) 0 = (lensBranchPoint τ true 0).im
    rw [dotProduct_zero, lensBranchPoint_im hτ0 hτ1 true (by constructor <;> norm_num)]

theorem octahedralRows_feasible_zero {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    (0 : Space 3) ∈ basisFeasibleRegion τ octahedralRows Fin.castSucc (fun _ => true) := by
  apply (mem_basisFeasibleRegion_iff hτ0 hτ1 octahedralRows Fin.castSucc
    (fun _ => true) octahedralRows_basis_det 0).mpr
  refine ⟨?_, ![(lensBranchPoint τ true 0).re, 0, 0], ?_, ?_⟩
  · intro j
    simp
  · intro i
    simpa only [dotProduct_zero] using octahedralRows_common_witness hτ0 hτ1 i.castSucc
  · intro j
    rw [octahedralRows_common_witness hτ0 hτ1 j]
    exact lensCircleImage_subset_graphBody hτ0 hτ1 (lensRightPoint_mem_circleImage τ 0)

/-- The extra active row is genuine: no equal, opposite or convex-redundant
row remains. The collision is at one parameter, not asserted to have positive measure. -/
theorem octahedralRows_extra_active_zero {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ¬NoExtraActive τ octahedralRows Fin.castSucc (fun _ => true) (0 : Space 3) := by
  have hy : ![(lensBranchPoint τ true 0).re, 0, 0] =
      basisRealWitness τ (fun _ => true) (fun i : Fin 3 => octahedralRows i.castSucc) 0 := by
    apply basisRealWitness_unique τ (fun _ => true) octahedralRows_basis_det
    intro i
    simpa only [map_zero, Pi.zero_apply] using
      octahedralRows_common_witness hτ0 hτ1 i.castSucc
  intro h
  have hm := h 3 (by
    rw [← hy, octahedralRows_common_witness hτ0 hτ1 3]
    exact lensBranchPoint_mem_frontier hτ0 hτ1 true)
  obtain ⟨i, hi⟩ := hm
  fin_cases i <;> norm_num at hi

end
end Funk
