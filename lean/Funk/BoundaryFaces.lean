import Funk.FlagInterior
import Mathlib.Analysis.LocallyConvex.Separation

/-! Every boundary point of an actual full-dimensional convex body belongs to
an actual nonempty proper exposed face. No finite-polytope premise is needed.
This supplies boundary faces, not yet full flags or flag-simplex coverage. -/

open Set Topology

namespace Funk
noncomputable section

/-- Nonempty proper geometric faces, without assuming their dimensions. -/
abbrev ProperPolytopeFace {n : ℕ} (P : Set (Space n)) :=
  {F : PolytopeFace P // F.val.Nonempty ∧ F.val ≠ P}

/-- The actual contact set of a supporting continuous linear functional. -/
def supportingContact {n : ℕ} (P : Set (Space n))
    (l : StrongDual ℝ (Space n)) (c : ℝ) : Set (Space n) := {x ∈ P | l x = c}

theorem supportingContact_isExposed {n : ℕ} {P : Set (Space n)}
    (l : StrongDual ℝ (Space n)) (hl : l ≠ 0) (c : ℝ)
    (hbound : ∀ x ∈ P, l x ≤ c) : IsExposed ℝ P (supportingContact P l c) :=
  supportingFace_isExposed (Or.inr (Or.inr ⟨l, c, hl, hbound, rfl⟩))

theorem supportingContact_subset_frontier {n : ℕ} {P : Set (Space n)}
    (l : StrongDual ℝ (Space n)) (hl : l ≠ 0) (c : ℝ)
    (hbound : ∀ x ∈ P, l x ≤ c) : supportingContact P l c ⊆ frontier P := by
  intro x hx
  exact ⟨subset_closure hx.1, fun hi =>
    (functional_lt_on_interior l hl c hbound x hi).ne hx.2⟩

theorem supportingContact_ne_top {n : ℕ} {P : Set (Space n)}
    (h0 : 0 ∈ interior P) (l : StrongDual ℝ (Space n)) (hl : l ≠ 0) (c : ℝ)
    (hbound : ∀ x ∈ P, l x ≤ c) : supportingContact P l c ≠ P := by
  intro heq
  have hm : 0 ∈ supportingContact P l c := heq.symm ▸ interior_subset h0
  exact (functional_lt_on_interior l hl c hbound 0 h0).ne hm.2

/-- Weak separation at a boundary point constructs the face containing that point. -/
theorem frontier_mem_properFace {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) {x : Space n} (hx : x ∈ frontier P) :
    ∃ F : ProperPolytopeFace P, x ∈ F.val.val := by
  obtain ⟨l, hl, hbound⟩ := geometric_hahn_banach_of_nonempty_interior_point
    hP.2.1 hx.2 ⟨0, hP.2.2.2⟩
  have he := supportingContact_isExposed l hl (l x) hbound
  have hxP : x ∈ P := hP.1.isClosed.closure_eq ▸ hx.1
  exact ⟨⟨⟨supportingContact P l (l x), he.convex hP.2.1, he.isExtreme⟩,
    ⟨x, hxP, rfl⟩, supportingContact_ne_top hP.2.2.2 l hl (l x) hbound⟩, hxP, rfl⟩

/-- Nonempty proper faces have smaller affine dimension in the actual ambient space. -/
theorem properFace_dimension_lt {n : ℕ} {P : Set (Space n)}
    (F : ProperPolytopeFace P) : Module.finrank ℝ (affineSpan ℝ F.val.val).direction < n := by
  have hle : Module.finrank ℝ (affineSpan ℝ F.val.val).direction ≤ n := by
    simpa only [Module.finrank_fin_fun] using
      (Submodule.finrank_le (affineSpan ℝ F.val.val).direction)
  have hne : Module.finrank ℝ (affineSpan ℝ F.val.val).direction ≠ n := fun h =>
    F.property.2 (face_eq_of_full_dimension F.val.property.1 F.val.property.2 F.property.1 h)
  exact lt_of_le_of_ne hle hne

/-- Inclusion plus equal affine dimensions cannot hide a larger subset of the parent body. -/
theorem face_eq_of_subset_of_dimension_eq {n : ℕ} {P F G : Set (Space n)}
    (hc : Convex ℝ F) (he : IsExtreme ℝ P F) (hn : F.Nonempty)
    (hFG : F ⊆ G) (hGP : G ⊆ P)
    (hd : Module.finrank ℝ (affineSpan ℝ F).direction =
      Module.finrank ℝ (affineSpan ℝ G).direction) : F = G := by
  have hspan : affineSpan ℝ F ≤ affineSpan ℝ G := affineSpan_mono ℝ hFG
  have heq : affineSpan ℝ F = affineSpan ℝ G :=
    AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
      (Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hspan) hd)
      (hn.mono (subset_affineSpan ℝ F)) hspan
  apply Set.Subset.antisymm hFG
  intro x hx
  rw [← face_inter_affineSpan hc he]
  exact ⟨hGP hx, heq.symm ▸ subset_affineSpan ℝ G hx⟩

/-- Genuine strict face inclusion strictly increases affine dimension. -/
theorem face_dimension_lt_of_ssubset {n : ℕ} {P : Set (Space n)}
    (F G : PolytopeFace P) (hn : F.val.Nonempty) (hFG : F.val ⊂ G.val) :
    Module.finrank ℝ (affineSpan ℝ F.val).direction <
      Module.finrank ℝ (affineSpan ℝ G.val).direction := by
  have hle := Submodule.finrank_mono
    (AffineSubspace.direction_le (affineSpan_mono ℝ hFG.subset))
  apply lt_of_le_of_ne hle
  intro hd
  exact hFG.ne (face_eq_of_subset_of_dimension_eq F.property.1 F.property.2 hn
    hFG.subset G.property.2.subset hd)

theorem properPolytopeFace_finite {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) : Finite (ProperPolytopeFace P) := by
  let : Finite (PolytopeFace P) := polytopeFace_finite hp
  infer_instance

/-- An unconditional geometric boundary cover; no cover is supplied as a hypothesis. -/
theorem frontier_subset_properFaces {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) : frontier P ⊆ ⋃ F : ProperPolytopeFace P, F.val.val := by
  intro x hx
  obtain ⟨F, hF⟩ := frontier_mem_properFace hP hx
  exact Set.mem_iUnion.mpr ⟨F, hF⟩

end
end Funk
