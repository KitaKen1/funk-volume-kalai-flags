import Funk.Targets
import Mathlib.Data.Finset.Powerset
import Mathlib.SetTheory.Cardinal.Finite

/-! A face of a generated convex hull is determined by the generators it contains.
This uses actual convex extreme subsets, including the empty and full faces.
The generators need not themselves be vertices or be affinely independent. -/

open Set

namespace Funk

noncomputable section

/-- Known face membership reconstructs the whole face from the given generators. -/
theorem face_eq_convexHull_inter {n : ℕ} (s F : Set (Space n))
    (hc : Convex ℝ F) (he : IsExtreme ℝ (convexHull ℝ s) F) :
    F = convexHull ℝ (s ∩ F) := by
  apply Set.Subset.antisymm
  · have hh : convexHull ℝ s ⊆
        {x | x ∈ convexHull ℝ s ∧ (x ∈ F → x ∈ convexHull ℝ (s ∩ F))} := by
      apply convexHull_min
      · intro x hx
        exact ⟨subset_convexHull ℝ s hx, fun hF => subset_convexHull ℝ _ ⟨hx, hF⟩⟩
      · intro x hx y hy a b ha hb hab
        refine ⟨(convex_convexHull ℝ s) hx.1 hy.1 ha hb hab, ?_⟩
        intro hz
        by_cases ha0 : a = 0
        · have hb1 : b = 1 := by linarith
          simpa [ha0, hb1] using hy.2 (by simpa [ha0, hb1] using hz)
        by_cases hb0 : b = 0
        · have ha1 : a = 1 := by linarith
          simpa [hb0, ha1] using hx.2 (by simpa [hb0, ha1] using hz)
        have hseg : a • x + b • y ∈ openSegment ℝ x y :=
          ⟨a, b, lt_of_le_of_ne ha (Ne.symm ha0), lt_of_le_of_ne hb (Ne.symm hb0), hab, rfl⟩
        exact (convex_convexHull ℝ (s ∩ F))
          (hx.2 (he.left_mem_of_mem_openSegment hx.1 hy.1 hz hseg))
          (hy.2 (he.right_mem_of_mem_openSegment hx.1 hy.1 hz hseg)) ha hb hab
    intro x hx
    exact (hh (he.subset hx)).2 hx
  · exact convexHull_min Set.inter_subset_right hc

/-- A finite subset code of the original generators; no geometric search is needed. -/
def faceVertexCode {n : ℕ} (vertices : Finset (Space n)) (F : Set (Space n)) :
    Finset (Space n) := by
  classical
  exact vertices.filter (fun x => x ∈ F)

theorem faceVertexCode_subset {n : ℕ} (vertices : Finset (Space n)) (F : Set (Space n)) :
    faceVertexCode vertices F ⊆ vertices := by
  classical
  exact Finset.filter_subset _ _

theorem coe_faceVertexCode {n : ℕ} (vertices : Finset (Space n)) (F : Set (Space n)) :
    (faceVertexCode vertices F : Set (Space n)) = (vertices : Set (Space n)) ∩ F := by
  classical
  ext x
  simp [faceVertexCode]

theorem face_eq_convexHull_code {n : ℕ} (vertices : Finset (Space n))
    (F : Set (Space n)) (hc : Convex ℝ F)
    (he : IsExtreme ℝ (convexHull ℝ (vertices : Set (Space n))) F) :
    F = convexHull ℝ (faceVertexCode vertices F : Set (Space n)) := by
  rw [coe_faceVertexCode]
  exact face_eq_convexHull_inter _ _ hc he

/-- The actual convex faces, without properness or nonemptiness restrictions. -/
abbrev PolytopeFace {n : ℕ} (P : Set (Space n)) :=
  {F : Set (Space n) // Convex ℝ F ∧ IsExtreme ℝ P F}

theorem faceVertexCode_injective {n : ℕ} (vertices : Finset (Space n)) :
    Function.Injective (fun F : PolytopeFace (convexHull ℝ (vertices : Set (Space n))) =>
      faceVertexCode vertices F.val) := by
  intro F G h
  change faceVertexCode vertices F.val = faceVertexCode vertices G.val at h
  apply Subtype.ext
  rw [face_eq_convexHull_code vertices F.val F.property.1 F.property.2,
    face_eq_convexHull_code vertices G.val G.property.1 G.property.2, h]

theorem polytopeFace_finite {n : ℕ} {P : Set (Space n)} (hP : IsFinitePolytope P) :
    Finite (PolytopeFace P) := by
  classical
  obtain ⟨vertices, rfl⟩ := hP
  let code : PolytopeFace (convexHull ℝ (vertices : Set (Space n))) →
      {s : Finset (Space n) // s ∈ vertices.powerset} :=
    fun F => ⟨faceVertexCode vertices F.val,
      Finset.mem_powerset.mpr (faceVertexCode_subset vertices F.val)⟩
  apply Finite.of_injective code
  intro F G h
  exact faceVertexCode_injective vertices (congrArg Subtype.val h)

end
end Funk
