import Funk.FunkFinite
import Mathlib.Analysis.LocallyConvex.Separation

/-! Coordinate polar compactness and bipolarity for the exact dot-product
polar used in the frozen targets. -/

open Set

namespace Funk
noncomputable section

theorem isClosed_coordinatePolar {n : ℕ} (K : Set (Space n)) :
    IsClosed (coordinatePolar K) := by
  simp only [coordinatePolar, Set.ofPred_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro _
  exact isClosed_le (by fun_prop) continuous_const

theorem coordinatePolar_convexHull {n : ℕ} (s : Set (Space n)) :
    coordinatePolar (convexHull ℝ s) = coordinatePolar s := by
  apply Set.Subset.antisymm
  · exact coordinatePolar_antitone (subset_convexHull ℝ s)
  · intro y hy
    exact convexHull_min hy ((convex_Iic (1 : ℝ)).linear_preimage (dotProductBilin ℝ ℝ y))

theorem isCompact_coordinatePolar {n : ℕ} {K : Set (Space n)}
    (hv : Convex ℝ K) (hi : 0 ∈ interior K) : IsCompact (coordinatePolar K) := by
  obtain ⟨r, hr, haxis⟩ := exists_axis_radius hi
  have hbox : IsCompact (coordinateBox n (-(1 / r)) (1 / r)) := by
    rw [coordinateBox, Set.pi_univ_Icc]
    exact isCompact_Icc
  apply hbox.of_isClosed_subset (isClosed_coordinatePolar K)
  simpa [translate] using convex_polar_subset_box hv hr (τ := 0) (by norm_num)
    (by norm_num) haxis (interior_subset hi)

/-- Every real linear functional on coordinates has its explicit row vector. -/
theorem linearFunctional_eq_dotProduct {n : ℕ} (f : Space n →ₗ[ℝ] ℝ) (x : Space n) :
    f x = dotProduct (fun i => f (fun j => if i = j then 1 else 0)) x := by
  rw [LinearMap.pi_apply_eq_sum_univ]
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro i _
  simp only [smul_eq_mul, mul_comm]

theorem subset_coordinateBipolar {n : ℕ} (K : Set (Space n)) :
    K ⊆ coordinatePolar (coordinatePolar K) := by
  intro x hx y hy
  rw [dotProduct_comm]
  exact hy x hx

/-- Bipolarity needs only closedness, convexity, and membership of the origin. -/
theorem coordinatePolar_bipolar {n : ℕ} {K : Set (Space n)}
    (hc : IsClosed K) (hv : Convex ℝ K) (h0 : 0 ∈ K) :
    coordinatePolar (coordinatePolar K) = K := by
  apply Set.Subset.antisymm ?_ (subset_coordinateBipolar K)
  intro x hx
  by_contra hn
  obtain ⟨f, c, hf, hcx⟩ := geometric_hahn_banach_closed_point hv hc hn
  have hc0 : 0 < c := by simpa using hf 0 h0
  let row : Space n := fun i => f (fun j => if i = j then 1 else 0)
  have hrow (z : Space n) : dotProduct row z = f z :=
    (linearFunctional_eq_dotProduct f.toLinearMap z).symm
  have hpolar : c⁻¹ • row ∈ coordinatePolar K := by
    intro z hz
    rw [smul_dotProduct, smul_eq_mul, hrow, ← div_eq_inv_mul]
    exact (div_le_one hc0).mpr (hf z hz).le
  have hbound := hx _ hpolar
  rw [dotProduct_comm, smul_dotProduct, smul_eq_mul, hrow, ← div_eq_inv_mul] at hbound
  exact (not_le_of_gt hcx) ((div_le_one hc0).mp hbound)

theorem neg_mem_coordinatePolar {n : ℕ} {K : Set (Space n)}
    (hs : ∀ x ∈ K, -x ∈ K) {y : Space n} (hy : y ∈ coordinatePolar K) :
    -y ∈ coordinatePolar K := by
  intro x hx
  have h := hy (-x) (hs x hx)
  simpa only [neg_dotProduct, dotProduct_neg] using h

end
end Funk
