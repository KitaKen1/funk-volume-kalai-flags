import Funk.PolytopeFlags
import Mathlib.Analysis.Normed.Affine.Convex

/-! Symmetric multiplicative outer approximation by genuine finite polytopes.
Only a single approximant for each dilation is needed, not a nested sequence. -/

open Set
open scoped Topology

namespace Funk
noncomputable section

theorem subset_interior_dilate {n : ℕ} {K : Set (Space n)}
    (hK : Convex ℝ K) (h0 : 0 ∈ interior K) {c : ℝ} (hc : 1 < c) :
    K ⊆ interior ((fun x => c • x) '' K) := by
  have hc0 : 0 < c := by linarith
  intro x hx
  have hi : c⁻¹ • x ∈ interior K := by
    have h := hK.combo_interior_self_mem_interior h0 hx
      (a := 1 - c⁻¹) (b := c⁻¹) (by rw [sub_pos]; exact inv_lt_one_of_one_lt₀ hc)
      (inv_nonneg.mpr hc0.le) (by ring)
    simpa using h
  have hopen : IsOpen ((fun x : Space n => c • x) '' interior K) :=
    isOpenMap_smul₀ hc0.ne' _ isOpen_interior
  apply interior_maximal (Set.image_mono interior_subset) hopen
  exact ⟨c⁻¹ • x, hi, by simp only [smul_smul, mul_inv_cancel₀ hc0.ne', one_smul]⟩

/-- Symmetrize a finite generating set without leaving a convex symmetric container. -/
theorem symmetric_hull_finset {n : ℕ} (vertices : Finset (Space n)) :
    ∃ P : Set (Space n), IsFinitePolytope P ∧ Convex ℝ P ∧
      (∀ x ∈ P, -x ∈ P) ∧ convexHull ℝ (vertices : Set (Space n)) ⊆ P ∧
      ∀ K : Set (Space n), Convex ℝ K → (∀ x ∈ K, -x ∈ K) →
        convexHull ℝ (vertices : Set (Space n)) ⊆ K → P ⊆ K := by
  classical
  let V : Finset (Space n) := vertices ∪ vertices.image (fun x => -x)
  let P : Set (Space n) := convexHull ℝ (V : Set (Space n))
  have hs : ∀ x ∈ (V : Set (Space n)), -x ∈ (V : Set (Space n)) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      change - -y ∈ vertices ∪ vertices.image (fun x => -x)
      simpa only [neg_neg] using Finset.mem_union_left (vertices.image (fun x => -x)) hy
  refine ⟨P, ⟨V, rfl⟩, convex_convexHull ℝ _, ?_, ?_, ?_⟩
  · have hsub : P ⊆ (-LinearMap.id : Space n →ₗ[ℝ] Space n) ⁻¹' P := by
      apply convexHull_min _ ((convex_convexHull ℝ _).linear_preimage _)
      intro x hx
      exact subset_convexHull ℝ _ (hs x hx)
    exact fun x hx => hsub hx
  · apply convexHull_mono
    exact fun x hx => Finset.mem_union_left _ hx
  · intro K hc hn hv
    apply convexHull_min _ hc
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hv (subset_convexHull ℝ _ hx)
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact hn y (hv (subset_convexHull ℝ _ hy))

/-- Exact multiplicative sandwich, with the original target's body hypotheses. -/
theorem exists_symmetric_polytope_outer_sandwich {n : ℕ} {K : Set (Space n)}
    (hK : IsSymmetricConvexBody K) {c : ℝ} (hc : 1 < c) :
    ∃ P : Set (Space n), IsFinitePolytope P ∧ IsSymmetricConvexBody P ∧
      K ⊆ P ∧ P ⊆ (fun x => c • x) '' K := by
  have hn : (fun x => c • x) '' K ∈ 𝓝ˢ K :=
    mem_nhdsSet_iff_forall.mpr (fun x hx => mem_interior_iff_mem_nhds.mp
      (subset_interior_dilate hK.2.1 hK.2.2.2 hc hx))
  obtain ⟨vertices, hinner, houter⟩ :=
    hK.2.1.exists_subset_interior_convexHull_finset_of_isCompact hK.1 hn
  obtain ⟨P, hp, hpconv, hpsym, hsub, hmin⟩ := symmetric_hull_finset vertices
  have hKP : K ⊆ P := (hinner.trans interior_subset).trans hsub
  refine ⟨P, hp, ⟨finitePolytope_isCompact hp, hpconv, hpsym,
    interior_mono hKP hK.2.2.2⟩, hKP, ?_⟩
  apply hmin _ _ _ houter
  · exact hK.2.1.linear_image (c • LinearMap.id)
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨-x, hK.2.2.1 x hx, by simp⟩

end
end Funk
