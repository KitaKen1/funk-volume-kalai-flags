import Funk.RadialFaceCover
import Funk.CoverUpperIntegral
import Funk.FunkScaling
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! The actual facet pyramids cover the body almost everywhere.
Lower-dimensional proper-face pyramids are null, so they can be discarded for
upper integrals. Complete flag-simplex coverage and the sharp FVW bound remain.
-/

open Set MeasureTheory Topology
open scoped ENNReal

namespace Funk
noncomputable section

/-- Actual nonempty proper faces of affine dimension n-1, expressed without subtraction. -/
abbrev FacetPolytopeFace {n : ℕ} (P : Set (Space n)) :=
  {F : ProperPolytopeFace P // Module.finrank ℝ (affineSpan ℝ F.val.val).direction + 1 = n}

theorem facetPolytopeFace_finite {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) : Finite (FacetPolytopeFace P) := by
  let : Finite (ProperPolytopeFace P) := properPolytopeFace_finite hp
  infer_instance

/-- Dimension-labelled facets are maximal among the actual nonempty proper faces. -/
theorem facetPolytopeFace_maximal {n : ℕ} {P : Set (Space n)}
    (F : FacetPolytopeFace P) (G : ProperPolytopeFace P)
    (hFG : F.val.val.val ⊆ G.val.val) : F.val.val.val = G.val.val := by
  by_contra hne
  have hlt := face_dimension_lt_of_ssubset F.val.val G.val F.val.property.1
    (lt_of_le_of_ne hFG hne)
  have hG := properFace_dimension_lt G
  have hF := F.property
  omega

/-- A cone over a face gains at most one affine dimension, and otherwise has zero volume. -/
theorem volume_facePyramid_zero_of_dimension {n : ℕ} (F : Set (Space n))
    (hd : Module.finrank ℝ (affineSpan ℝ F).direction + 1 < n) : volume (facePyramid F) = 0 := by
  have hd' : Module.finrank ℝ (affineSpan ℝ (insert 0 F)).direction < n := by
    rw [direction_affineSpan] at hd ⊢
    exact lt_of_le_of_lt (finrank_vectorSpan_insert_le_set ℝ F 0) hd
  have hA : affineSpan ℝ (insert 0 F) ≠ ⊤ := by
    intro h
    rw [h, AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun] at hd'
    exact (lt_irrefl n) hd'
  exact measure_mono_null (convexHull_subset_affineSpan (𝕜 := ℝ) (insert 0 F))
    (Measure.addHaar_affineSubspace volume _ hA)

/-- Genuine facet-pyramid coverage outside a null set; no covering input is assumed. -/
theorem ae_body_subset_facetPyramids {n : ℕ} (hn : 1 ≤ n) {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P) :
    ∀ᵐ x ∂volume, x ∈ P → x ∈ ⋃ F : FacetPolytopeFace P, facePyramid F.val.val.val := by
  classical
  let : Finite (ProperPolytopeFace P) := properPolytopeFace_finite hp
  let : NeZero n := ⟨by omega⟩
  have hall : ∀ᵐ x ∂volume, ∀ F : ProperPolytopeFace P,
      Module.finrank ℝ (affineSpan ℝ F.val.val).direction + 1 < n →
        x ∉ facePyramid F.val.val := by
    apply ae_all_iff.mpr
    intro F
    by_cases hd : Module.finrank ℝ (affineSpan ℝ F.val.val).direction + 1 < n
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp
        (volume_facePyramid_zero_of_dimension F.val.val hd)] with x hx
      exact fun _ => hx
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hd h))
  filter_upwards [hall, volume.ae_ne (0 : Space n)] with x hall hx0
  intro hx
  obtain ⟨F, hF⟩ := nonzero_mem_properFacePyramid hP hx hx0
  have hd : Module.finrank ℝ (affineSpan ℝ F.val.val).direction + 1 = n := by
    have hlt := properFace_dimension_lt F
    by_contra hne
    exact hall F (by omega) hF
  exact Set.mem_iUnion.mpr ⟨⟨F, hd⟩, hF⟩

/-- An a.e. finite cover is enough even when the integrand is not known measurable. -/
theorem setLIntegral_le_sum_of_ae_cover {n : ℕ} {ι : Type*} [Fintype ι]
    (D : Set (Space n)) (S : ι → Set (Space n))
    (hcover : D ≤ᵐ[volume] ⋃ i, S i) (f : Space n → ℝ≥0∞) :
    ∫⁻ x in D, f x ≤ ∑ i, ∫⁻ x in S i, f x := by
  calc
    _ ≤ ∫⁻ x in ⋃ i, S i, f x := lintegral_mono_set' hcover
    _ ≤ _ := by simpa only [tsum_fintype] using lintegral_iUnion_le S f

/-- Actual Funk volume has an unconditional finite facet-pyramid upper integral.
This supplies primal domains; it does not evaluate their polar kernels or FVW coefficient. -/
theorem funkVolume_le_facetPyramid_integrals {n : ℕ} (hn : 1 ≤ n)
    {P : Set (Space n)} (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    {τ : ℝ} (hτ : 0 < τ) :
    let : Finite (FacetPolytopeFace P) := facetPolytopeFace_finite hp
    let : Fintype (FacetPolytopeFace P) := Fintype.ofFinite (FacetPolytopeFace P)
    funkVolume P τ ≤ ENNReal.ofReal (τ ^ n) *
      ∑ F : FacetPolytopeFace P, ∫⁻ X in facePyramid F.val.val.val,
        volume (coordinatePolar (translate P (τ • X))) := by
  let : Finite (FacetPolytopeFace P) := facetPolytopeFace_finite hp
  let : Fintype (FacetPolytopeFace P) := Fintype.ofFinite (FacetPolytopeFace P)
  rw [funkVolume_scale hP.1.measurableSet hτ]
  exact mul_le_mul_right
    (setLIntegral_le_sum_of_ae_cover P (fun F : FacetPolytopeFace P => facePyramid F.val.val.val)
      (ae_body_subset_facetPyramids hn hp hP) _) _

end
end Funk
