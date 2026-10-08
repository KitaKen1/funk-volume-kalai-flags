import Funk.RelativeFaceGeometry
import Funk.FlagSimplex

/-! Relative-boundary descent through actual geometric faces. A subface of a
face is an actual face of the original polytope. Dimension drops strictly;
codimension one is neither assumed nor proved here. -/

open Set Topology

namespace Funk
noncomputable section

/-- A coordinate-free strict interior bound, usable in every face direction space. -/
theorem dual_lt_on_interior {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : Set E} (l : StrongDual ℝ E) (hl : l ≠ 0) (c : ℝ)
    (hbound : ∀ x ∈ D, l x ≤ c) : ∀ x ∈ interior D, l x < c := by
  have him : l '' interior D ⊆ Iic c := by
    rintro _ ⟨x, hx, rfl⟩
    exact hbound x (interior_subset hx)
  have hi : l '' interior D ⊆ interior (Iic c) :=
    interior_maximal him (l.isOpenMap_of_ne_zero hl _ isOpen_interior)
  intro x hx
  simpa only [interior_Iic, mem_Iio] using hi (mem_image_of_mem l hx)

/-- Extreme subsets transport through injective affine maps. -/
theorem extreme_affine_image {E V : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup V] [Module ℝ V] (f : E →ᵃ[ℝ] V) (hf : Function.Injective f)
    {A B : Set E} (he : IsExtreme ℝ A B) : IsExtreme ℝ (f '' A) (f '' B) := by
  refine ⟨Set.image_mono he.subset, ?_⟩
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩ hseg
  rw [← image_openSegment ℝ f u v] at hseg
  obtain ⟨z, hz, hzw⟩ := hseg
  have hzw' : z = w := hf hzw
  exact ⟨u, he.left_mem_of_mem_openSegment hu hv hw (hzw' ▸ hz), rfl⟩

/-- Every relative boundary point of a nonempty compact convex set has an actual proper face. -/
theorem intrinsicFrontier_mem_properFace {n : ℕ} {C : Set (Space n)}
    (hk : IsCompact C) (hc : Convex ℝ C) (hn : C.Nonempty)
    {x : Space n} (hx : x ∈ intrinsicFrontier ℝ C) :
    ∃ F : PolytopeFace C, F.val.Nonempty ∧ F.val ≠ C ∧ x ∈ F.val := by
  obtain ⟨p, hp⟩ := hn.intrinsicInterior hc
  let p' : affineSpan ℝ C := ⟨p, subset_affineSpan ℝ C (intrinsicInterior_subset hp)⟩
  let e := relativeEmbedding C p'
  let D := relativeBody C p'
  have hcD : Convex ℝ D := relativeBody_convex hc p'
  have hkD : IsCompact D := relativeBody_isCompact hk p'
  have h0 : 0 ∈ interior D := relativeBody_zero_interior p' hp
  have hx' : x ∈ e '' frontier D := by
    rw [relativeEmbedding_frontier]
    exact hx
  obtain ⟨v, hv, rfl⟩ := hx'
  obtain ⟨l, hl, hbound⟩ := geometric_hahn_banach_of_nonempty_interior_point hcD hv.2 ⟨0, h0⟩
  let T := l.toExposed D
  have hvD : v ∈ D := hkD.isClosed.frontier_subset hv
  have hvT : v ∈ T := ⟨hvD, hbound⟩
  have heT : IsExposed ℝ D T := ContinuousLinearMap.toExposed.isExposed (l := l)
  have hneT : T ≠ D := by
    intro h
    have hzero : 0 ∈ T := h.symm ▸ interior_subset h0
    have hb0 : ∀ w ∈ D, l w ≤ l 0 := hzero.2
    exact (dual_lt_on_interior l hl (l 0) hb0 0 h0).false
  have him : e '' D = C := relativeBody_image C p'
  have hcF : Convex ℝ (e '' T) := (heT.convex hcD).affine_image e.toAffineMap
  have heF : IsExtreme ℝ C (e '' T) := by
    exact (congrArg (fun S : Set (Space n) => IsExtreme ℝ S (e '' T)) him).mp
      (extreme_affine_image e.toAffineMap e.injective heT.isExtreme)
  refine ⟨⟨e '' T, hcF, heF⟩, ⟨e v, v, hvT, rfl⟩, ?_, ⟨v, hvT, rfl⟩⟩
  intro heq
  exact hneT (e.injective.image_injective (heq.trans him.symm))

/-- Relative subfaces are faces of the original body by transitivity, with a strict rank drop. -/
theorem face_intrinsicFrontier_mem_smallerFace {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (F : PolytopeFace P) (hn : F.val.Nonempty)
    {x : Space n} (hx : x ∈ intrinsicFrontier ℝ F.val) :
    ∃ G : PolytopeFace P, G.val.Nonempty ∧ G.val ⊂ F.val ∧
      Module.finrank ℝ (affineSpan ℝ G.val).direction <
        Module.finrank ℝ (affineSpan ℝ F.val).direction ∧ x ∈ G.val := by
  obtain ⟨G, hnG, hneG, hxG⟩ := intrinsicFrontier_mem_properFace
    (polytopeFace_isCompact hp F) F.property.1 hn hx
  let H : PolytopeFace P := ⟨G.val, G.property.1, F.property.2.trans G.property.2⟩
  have hs : H.val ⊂ F.val := lt_of_le_of_ne G.property.2.subset hneG
  exact ⟨H, hnG, hs, face_dimension_lt_of_ssubset H F hnG hs, hxG⟩

/-- Each noncentral point in an actual face lies on a segment to a strictly smaller actual face. -/
theorem face_mem_segment_smallerFace {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : PolytopeFace P) (hn : F.val.Nonempty) {x : Space n}
    (hx : x ∈ F.val) (hxp : x ≠ faceInteriorPoint F) :
    ∃ G : PolytopeFace P, G.val.Nonempty ∧ G.val ⊂ F.val ∧
      Module.finrank ℝ (affineSpan ℝ G.val).direction <
        Module.finrank ℝ (affineSpan ℝ F.val).direction ∧
      ∃ y ∈ G.val, x ∈ segment ℝ (faceInteriorPoint F) y := by
  obtain ⟨y, hy, hxy⟩ := intrinsic_radial_boundary
    (polytopeFace_isCompact hp F) F.property.1
    (faceInteriorPoint_mem_intrinsicInterior hP F hn) hx hxp
  obtain ⟨G, hnG, hs, hd, hyG⟩ := face_intrinsicFrontier_mem_smallerFace hp F hn hy
  exact ⟨G, hnG, hs, hd, y, hyG, hxy⟩

end
end Funk
