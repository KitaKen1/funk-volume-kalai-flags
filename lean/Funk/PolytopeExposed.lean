import Funk.PolytopeFlags
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.LocallyConvex.Separation

/-! Reconcile convex extreme faces with supporting-function faces for finite polytopes.
The relative-interior argument is valid for any finite-dimensional convex face;
the exposure construction additionally uses finite generation. -/

open Set Topology

namespace Funk
noncomputable section

/-- Removing an extreme subset from a convex set leaves a convex set. -/
theorem convex_sdiff_extreme {n : ℕ} {P F : Set (Space n)}
    (hP : Convex ℝ P) (he : IsExtreme ℝ P F) : Convex ℝ (P \ F) := by
  intro x hx y hy a b ha hb hab
  refine ⟨hP hx.1 hy.1 ha hb hab, ?_⟩
  intro hz
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    exact hy.2 (by simpa [ha0, hb1] using hz)
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    exact hx.2 (by simpa [hb0, ha1] using hz)
  exact hx.2 (he.left_mem_of_mem_openSegment hx.1 hy.1 hz
    ⟨a, b, lt_of_le_of_ne ha (Ne.symm ha0),
      lt_of_le_of_ne hb (Ne.symm hb0), hab, rfl⟩)

/-- An actual convex face is saturated inside its affine span. -/
theorem face_inter_affineSpan {n : ℕ} {P F : Set (Space n)}
    (hc : Convex ℝ F) (he : IsExtreme ℝ P F) :
    P ∩ (affineSpan ℝ F : Set (Space n)) = F := by
  obtain rfl | hF := F.eq_empty_or_nonempty
  · simp
  let : Nonempty (affineSpan ℝ F) :=
    ⟨⟨hF.choose, subset_affineSpan ℝ F hF.choose_spec⟩⟩
  obtain ⟨x, hx⟩ := hF.intrinsicInterior hc
  obtain ⟨x', hx', rfl⟩ := hx
  apply Set.Subset.antisymm
  · rintro y ⟨hyP, hyA⟩
    let y' : affineSpan ℝ F := ⟨y, hyA⟩
    obtain ⟨t, ht, hzt⟩ :=
      (AffineMap.lineMap_continuous.tendsto' _ _
        (AffineMap.lineMap_apply_zero (k := ℝ) x' y')).eventually_mem
          (mem_interior_iff_mem_nhds.mp hx') |>.exists_lt
    let z : Space n := (AffineMap.lineMap x' y' t : affineSpan ℝ F)
    have hzF : z ∈ F := hzt
    have hz : z = (1 - t) • (x' : Space n) + t • y := by
      change ((affineSpan ℝ F).subtype (AffineMap.lineMap x' y' t)) = _
      rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module]
      rfl
    have hxF : (x' : Space n) ∈ F :=
      show x' ∈ (Subtype.val ⁻¹' F : Set (affineSpan ℝ F)) from interior_subset hx'
    apply he.left_mem_of_mem_openSegment hyP (he.subset hzF) hxF
    have hd : 0 < 1 - t := by linarith
    have hn : 0 < -t := neg_pos.mpr ht
    refine ⟨-t / (1 - t), 1 / (1 - t), div_pos hn hd, div_pos zero_lt_one hd, ?_, ?_⟩
    · field_simp [ne_of_gt hd]
      ring
    · rw [hz]
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp [ne_of_gt hd]
      ring
  · exact fun _ hx => ⟨he.subset hx, subset_affineSpan ℝ F hx⟩

/-- A linear functional bounded above on an affine space is constant there. -/
theorem functional_constant_on_affine_of_upper_bound {n : ℕ}
    (A : AffineSubspace ℝ (Space n)) (f : StrongDual ℝ (Space n)) (u : ℝ)
    (hbound : ∀ z ∈ A, f z < u) {x y : Space n} (hx : x ∈ A) (hy : y ∈ A) :
    f y = f x := by
  by_contra hne
  have hd : f y - f x ≠ 0 := sub_ne_zero.mpr hne
  let t : ℝ := (u + 1 - f x) / (f y - f x)
  have hz := hbound (AffineMap.lineMap x y t) (by
    rw [AffineMap.lineMap_apply]
    exact A.smul_vsub_vadd_mem t hy hx hx)
  have heq : f (AffineMap.lineMap x y t) = u + 1 := by
    rw [AffineMap.lineMap_apply_module, map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    dsimp [t]
    field_simp [hd]
    ring
  rw [heq] at hz
  linarith

/-- Convex extreme faces of a finite polytope are exposed by a true continuous functional. -/
theorem polytopeFace_isExposed {n : ℕ} {P F : Set (Space n)}
    (hP : IsFinitePolytope P) (hc : Convex ℝ F) (he : IsExtreme ℝ P F) :
    IsExposed ℝ P F := by
  classical
  intro hF
  obtain ⟨vertices, rfl⟩ := hP
  let s : Set (Space n) := vertices
  let A := affineSpan ℝ F
  let O := convexHull ℝ (s \ F)
  have hOP : O ⊆ convexHull ℝ s \ F :=
    convexHull_min (fun z hz => ⟨subset_convexHull ℝ s hz.1, hz.2⟩)
      (convex_sdiff_extreme (convex_convexHull ℝ s) he)
  have hdisj : Disjoint (A : Set (Space n)) O := by
    apply Set.disjoint_left.mpr
    intro z hzA hzO
    have hzF : z ∈ F := by
      rw [← face_inter_affineSpan hc he]
      exact ⟨(hOP hzO).1, hzA⟩
    exact (hOP hzO).2 hzF
  obtain ⟨g, u, v, hA, huv, hO⟩ := geometric_hahn_banach_closed_compact
    A.convex A.closed_of_finiteDimensional (convex_convexHull ℝ (s \ F))
    ((vertices.finite_toSet.sdiff).isCompact_convexHull ℝ) hdisj
  obtain ⟨x, hx⟩ := hF
  have hxA : x ∈ A := subset_affineSpan ℝ F hx
  have hg : ∀ z ∈ F, g z = g x := fun z hz =>
    functional_constant_on_affine_of_upper_bound A g u hA hxA (subset_affineSpan ℝ F hz)
  let f : StrongDual ℝ (Space n) := -g
  have hf : ∀ z ∈ F, f z = f x := by
    intro z hz
    change -g z = -g x
    rw [hg z hz]
  have hs : ∀ z ∈ s, f z ≤ f x := by
    intro z hz
    by_cases hzF : z ∈ F
    · exact (hf z hzF).le
    · have hzg := hO z (subset_convexHull ℝ (s \ F) ⟨hz, hzF⟩)
      have hxg := hA x hxA
      change -g z ≤ -g x
      linarith
  have hbound : convexHull ℝ s ⊆ {z | f z ≤ f x} :=
    convexHull_min hs (convex_halfSpace_le f.toLinearMap.isLinear (f x))
  let E := f.toExposed (convexHull ℝ s)
  have hE : IsExposed ℝ (convexHull ℝ s) E :=
    ContinuousLinearMap.toExposed.isExposed (l := f)
  have hinter : s ∩ E = s ∩ F := by
    ext z
    constructor
    · rintro ⟨hz, hzE⟩
      refine ⟨hz, ?_⟩
      by_contra hzF
      have hzg := hO z (subset_convexHull ℝ (s \ F) ⟨hz, hzF⟩)
      have hxg := hA x hxA
      have hmax : f x ≤ f z := hzE.2 x (he.subset hx)
      change -g x ≤ -g z at hmax
      linarith
    · rintro ⟨hz, hzF⟩
      refine ⟨hz, subset_convexHull ℝ s hz, ?_⟩
      intro y hy
      exact (hbound hy).trans_eq (hf z hzF).symm
  have hEF : E = F := by
    rw [face_eq_convexHull_inter s E (hE.convex (convex_convexHull ℝ s)) hE.isExtreme,
      hinter, ← face_eq_convexHull_inter s F hc he]
  exact ⟨f, hEF.symm⟩

/-- Exact equivalence of the two face predicates; no symmetry or interior is required. -/
theorem finitePolytope_face_iff_exposed {n : ℕ} {P F : Set (Space n)}
    (hP : IsFinitePolytope P) :
    (Convex ℝ F ∧ IsExtreme ℝ P F) ↔ IsExposed ℝ P F := by
  constructor
  · rintro ⟨hc, he⟩
    exact polytopeFace_isExposed hP hc he
  · intro h
    obtain ⟨vertices, hvertices⟩ := hP
    have hc : Convex ℝ P := hvertices ▸ convex_convexHull ℝ (vertices : Set (Space n))
    exact ⟨h.convex hc, h.isExtreme⟩

end
end Funk
