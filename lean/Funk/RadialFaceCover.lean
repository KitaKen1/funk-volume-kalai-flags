import Funk.BoundaryFaces
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.Join

/-! A genuine radial cover by pyramids over proper faces.
This is a first covering step, not the final cover by complete flag simplices. -/

open Set Topology

namespace Funk
noncomputable section

def facePyramid {n : ℕ} (F : Set (Space n)) : Set (Space n) :=
  convexHull ℝ (insert 0 F)

theorem facePyramid_subset_body {n : ℕ} {P F : Set (Space n)}
    (hP : Convex ℝ P) (h0 : 0 ∈ P) (hF : F ⊆ P) : facePyramid F ⊆ P :=
  convexHull_min (Set.insert_subset h0 hF) hP

theorem facePyramid_eq_segments {n : ℕ} {F : Set (Space n)}
    (hc : Convex ℝ F) (hn : F.Nonempty) :
    facePyramid F = ⋃ y ∈ F, segment ℝ 0 y := by
  rw [facePyramid, convexHull_insert hn, hc.convexHull_eq, convexJoin_singleton_left]

theorem facePyramid_isCompact {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (F : PolytopeFace P) : IsCompact (facePyramid F.val) := by
  obtain ⟨vertices, hv⟩ := polytopeFace_isFinitePolytope hp F
  unfold facePyramid
  rw [hv, Set.insert_eq, convexHull_convexHull_union_right, ← Set.insert_eq]
  exact (vertices.finite_toSet.insert 0).isCompact_convexHull ℝ

/-- Radial normalization also works in relative vector spaces and needs no symmetry. -/
theorem radial_boundary_of_compact_convex {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {P : Set E} (hk : IsCompact P) (hc : Convex ℝ P)
    (h0 : 0 ∈ interior P) {x : E} (hx : x ∈ P) (hx0 : x ≠ 0) :
    ∃ y ∈ frontier P, x ∈ segment ℝ 0 y := by
  have hn : P ∈ 𝓝 (0 : E) := mem_interior_iff_mem_nhds.mp h0
  have hg : 0 < gauge P x := (gauge_pos (absorbent_nhds_zero hn)
    (NormedSpace.isVonNBounded_of_isBounded ℝ hk.isBounded)).mpr hx0
  have hle : gauge P x ≤ 1 := gauge_le_one_of_mem hx
  let y : E := (gauge P x)⁻¹ • x
  have hy : y ∈ frontier P := by
    apply (gauge_eq_one_iff_mem_frontier hc hn).mp
    dsimp [y]
    rw [gauge_smul_of_nonneg (inv_nonneg.mpr hg.le), smul_eq_mul, inv_mul_cancel₀ hg.ne']
  refine ⟨y, hy, 1 - gauge P x, gauge P x, sub_nonneg.mpr hle, hg.le, by ring, ?_⟩
  dsimp [y]
  rw [smul_zero, zero_add, smul_smul, mul_inv_cancel₀ hg.ne', one_smul]

/-- Normalize a nonzero point in the frozen actual convex body. -/
theorem nonzero_mem_segment_frontier {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) {x : Space n} (hx : x ∈ P) (hx0 : x ≠ 0) :
    ∃ y ∈ frontier P, x ∈ segment ℝ 0 y :=
  radial_boundary_of_compact_convex hP.1 hP.2.1 hP.2.2.2 hx hx0

/-- No flag cover premise: every nonzero body point lies in an actual proper-face pyramid. -/
theorem nonzero_mem_properFacePyramid {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) {x : Space n} (hx : x ∈ P) (hx0 : x ≠ 0) :
    ∃ F : ProperPolytopeFace P, x ∈ facePyramid F.val.val := by
  obtain ⟨y, hy, hxy⟩ := nonzero_mem_segment_frontier hP hx hx0
  obtain ⟨F, hF⟩ := frontier_mem_properFace hP hy
  exact ⟨F, segment_subset_convexHull (Set.mem_insert 0 _) (Set.mem_insert_of_mem 0 hF) hxy⟩

theorem body_subset_zero_union_properFacePyramids {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) :
    P ⊆ {0} ∪ ⋃ F : ProperPolytopeFace P, facePyramid F.val.val := by
  intro x hx
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  · obtain ⟨F, hF⟩ := nonzero_mem_properFacePyramid hP hx hx0
    exact Or.inr (Set.mem_iUnion.mpr ⟨F, hF⟩)

end
end Funk
