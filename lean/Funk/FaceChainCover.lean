import Funk.RelativeBoundaryFaces
import Funk.FacetPyramidCover

/-! Pointwise coverage by simplices of actual strict face chains. Chains can
skip dimensions. Such short chains will be discarded by ambient nullity,
rather than transporting relative null sets through cones. -/

open Set MeasureTheory

namespace Funk
noncomputable section

def IsFaceChain {n : ℕ} {P : Set (Space n)} (s : Finset (PolytopeFace P)) : Prop :=
  (∀ F ∈ s, F.val.Nonempty) ∧
    ∀ F ∈ s, ∀ G ∈ s, F ≠ G → F.val ⊂ G.val ∨ G.val ⊂ F.val

def chainSimplex {n : ℕ} {P : Set (Space n)} (s : Finset (PolytopeFace P)) : Set (Space n) :=
  convexHull ℝ (faceInteriorPoint '' (s : Set (PolytopeFace P)))

theorem chainSimplex_mono {n : ℕ} {P : Set (Space n)}
    {s t : Finset (PolytopeFace P)} (h : s ⊆ t) : chainSimplex s ⊆ chainSimplex t :=
  convexHull_mono (Set.image_mono h)

theorem facePoint_mem_chainSimplex {n : ℕ} {P : Set (Space n)}
    {s : Finset (PolytopeFace P)} {F : PolytopeFace P} (hF : F ∈ s) :
    faceInteriorPoint F ∈ chainSimplex s :=
  subset_convexHull ℝ _ ⟨F, hF, rfl⟩

/-- Dimension descent constructs an actual finite strict face chain covering each face point. -/
theorem face_mem_chainSimplex {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : PolytopeFace P) (hn : F.val.Nonempty) {x : Space n} (hx : x ∈ F.val) :
    ∃ s : Finset (PolytopeFace P), IsFaceChain s ∧ F ∈ s ∧
      (∀ G ∈ s, G.val ⊆ F.val) ∧ x ∈ chainSimplex s := by
  classical
  suffices ∀ d : ℕ, ∀ F : PolytopeFace P,
      Module.finrank ℝ (affineSpan ℝ F.val).direction = d →
      F.val.Nonempty → ∀ x ∈ F.val,
      ∃ s : Finset (PolytopeFace P), IsFaceChain s ∧ F ∈ s ∧
        (∀ G ∈ s, G.val ⊆ F.val) ∧ x ∈ chainSimplex s from
    this _ F rfl hn x hx
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro F hd hn x hx
    by_cases hxc : x = faceInteriorPoint F
    · refine ⟨{F}, ⟨?_, ?_⟩, by simp, ?_, ?_⟩
      · intro G hG
        simpa only [Finset.mem_singleton.mp hG] using hn
      · intro G hG H hH hne
        exact False.elim (hne ((Finset.mem_singleton.mp hG).trans (Finset.mem_singleton.mp hH).symm))
      · intro G hG
        exact (Finset.mem_singleton.mp hG) ▸ Set.Subset.rfl
      · rw [hxc]
        exact facePoint_mem_chainSimplex (by simp)
    · obtain ⟨G, hnG, hsG, hdG, y, hyG, hxy⟩ := face_mem_segment_smallerFace hp hP F hn hx hxc
      obtain ⟨s, hs, hGs, hsub, hy⟩ := ih _ (hd ▸ hdG) G rfl hnG y hyG
      have hGF : ∀ H ∈ s, H.val ⊂ F.val := fun H hH => lt_of_le_of_lt (hsub H hH) hsG
      refine ⟨insert F s, ⟨?_, ?_⟩, by simp, ?_, ?_⟩
      · intro H hH
        rcases Finset.mem_insert.mp hH with rfl | hHs
        · exact hn
        · exact hs.1 H hHs
      · intro H hH K hK hne
        rcases Finset.mem_insert.mp hH with rfl | hHs
        · rcases Finset.mem_insert.mp hK with rfl | hKs
          · exact False.elim (hne rfl)
          · exact Or.inr (hGF K hKs)
        · rcases Finset.mem_insert.mp hK with rfl | hKs
          · exact Or.inl (hGF H hHs)
          · exact hs.2 H hHs K hKs hne
      · intro H hH
        rcases Finset.mem_insert.mp hH with rfl | hHs
        · exact Set.Subset.rfl
        · exact (hGF H hHs).subset
      · exact (convex_convexHull ℝ _).segment_subset
          (facePoint_mem_chainSimplex (by simp))
          (chainSimplex_mono (Finset.subset_insert F s) hy) hxy

/-- Genuine pointwise coverage; this family still includes short, dimension-skipping chains. -/
theorem body_subset_chainSimplices {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P) :
    P ⊆ ⋃ s : {s : Finset (PolytopeFace P) // IsFaceChain s}, chainSimplex s.val := by
  intro x hx
  let F : PolytopeFace P := ⟨P, hP.2.1, IsExtreme.rfl⟩
  obtain ⟨s, hs, _, _, hxs⟩ := face_mem_chainSimplex hp hP F ⟨x, hx⟩ hx
  exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, hxs⟩

/-- All actual face chains form a finite type, before imposing any length bound. -/
theorem faceChain_finite {n : ℕ} {P : Set (Space n)} (hp : IsFinitePolytope P) :
    Finite {s : Finset (PolytopeFace P) // IsFaceChain s} := by
  let : Finite (PolytopeFace P) := polytopeFace_finite hp
  infer_instance

/-- A simplex using at most n face points is ambient-null, with no relative measure transport. -/
theorem volume_chainSimplex_zero_of_card_le {n : ℕ} {P : Set (Space n)}
    (s : Finset (PolytopeFace P)) (hs : s.card ≤ n) : volume (chainSimplex s) = 0 := by
  have hA : affineSpan ℝ (faceInteriorPoint '' (s : Set (PolytopeFace P))) ≠ ⊤ :=
    affineSpan_image_ne_top_of_encard_le_finrank ℝ s.finite_toSet
      (by simpa only [Set.encard_coe_eq_coe_finsetCard, Module.finrank_fin_fun] using (show (s.card : ℕ∞) ≤ n from by exact_mod_cast hs))
      faceInteriorPoint
  exact measure_mono_null (convexHull_subset_affineSpan (𝕜 := ℝ) _)
    (Measure.addHaar_affineSubspace volume _ hA)

end
end Funk
