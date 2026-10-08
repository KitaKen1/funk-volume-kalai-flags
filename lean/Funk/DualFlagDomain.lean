import Funk.DualCoordinates
import Funk.DualFlagCover
import Funk.Radius

/-! Concrete dual-coordinate domains for every genuine primal/polar flag pair.
The domain is the image of the actual tau-scaled primal flag simplex. Its
vertices, positive coordinate bounds and radius parameter are verified.
No primal/dual face correspondence or sharp asymptotic is assumed. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

def dualFlagDomain {n : ℕ} {P : Set (Space n)} (τ : ℝ)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) : Set (Space n) :=
  dualCoordinates (flagMatrix G) '' ((fun y => τ • y) '' flagSimplex F)

theorem dualFlagDomain_isCompact {n : ℕ} {P : Set (Space n)} (τ : ℝ)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) :
    IsCompact (dualFlagDomain τ F G) :=
  ((flagSimplex_isCompact F).image (continuous_id.const_smul τ)).image
    (continuous_dualCoordinates (flagMatrix G))

theorem dualFlagDomain_measurableSet {n : ℕ} {P : Set (Space n)} (τ : ℝ)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) :
    MeasurableSet (dualFlagDomain τ F G) := (dualFlagDomain_isCompact τ F G).measurableSet

/-- Explicit known vertices identify the actual integration domain. -/
theorem dualFlagDomain_eq_convexHull {n : ℕ} {P : Set (Space n)} (τ : ℝ)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) :
    dualFlagDomain τ F G = convexHull ℝ
      (Set.range (fun i => dualCoordinates (flagMatrix G) (τ • flagPoint F i))) := by
  let A : Space n →ᵃ[ℝ] Space n := (τ • (LinearMap.id : Space n →ₗ[ℝ] Space n)).toAffineMap
  change dualCoordinates (flagMatrix G) '' (A '' convexHull ℝ (Set.range (flagPoint F))) = _
  rw [A.image_convexHull, (dualCoordinates (flagMatrix G)).image_convexHull,
    ← Set.image_comp, ← Set.range_comp]
  rfl

theorem dualFlagDomain_convex {n : ℕ} {P : Set (Space n)} (τ : ℝ)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) :
    Convex ℝ (dualFlagDomain τ F G) := by
  rw [dualFlagDomain_eq_convexHull]
  exact convex_convexHull ℝ _

theorem dualFlagDomain_vertex_component {n : ℕ} {P : Set (Space n)} (τ : ℝ)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P))
    (i : Fin (n + 1)) (j : Fin n) :
    dualCoordinates (flagMatrix G) (τ • flagPoint F i) j =
      1 - τ * dotProduct (flagMatrix G j) (flagPoint F i) := by
  rw [dualCoordinates_component, dotProduct_smul, smul_eq_mul]

theorem dualFlagDomain_top_vertex {n : ℕ} {P : Set (Space n)} (τ : ℝ)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) :
    dualCoordinates (flagMatrix G) (τ • flagPoint F (Fin.last n)) = 1 := by
  rw [flagPoint_top, smul_zero, dualCoordinates_apply, map_zero, sub_zero]

/-- Uniform positive coordinates on the actual domain, using original central symmetry. -/
theorem dualFlagDomain_coordinate_bounds {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (F : FullFlagWithTop P)
    (G : FullFlagWithTop (coordinatePolar P)) {u : Space n}
    (hu : u ∈ dualFlagDomain τ F G) (i : Fin n) : 1 - τ ≤ u i ∧ u i ≤ 1 + τ := by
  obtain ⟨x, ⟨X, hX, rfl⟩, rfl⟩ := hu
  have hXP : X ∈ P := flagSimplex_subset_polytope hP F hX
  have hq : flagMatrix G i ∈ coordinatePolar P :=
    flagPoint_mem_polytope (coordinatePolar_isSymmetricConvexBody hp hP) G i.castSucc
  have hb := hq X hXP
  have hm := hq (-X) (hP.2.2.1 X hXP)
  rw [dotProduct_neg] at hm
  rw [dualCoordinates_component, dotProduct_smul, smul_eq_mul]
  have hp' := mul_le_mul_of_nonneg_left hb hτ0
  have hm' := mul_le_mul_of_nonneg_left hm hτ0
  constructor <;> linarith

theorem dualFlagDomain_coordinates_pos {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (F : FullFlagWithTop P)
    (G : FullFlagWithTop (coordinatePolar P)) {u : Space n}
    (hu : u ∈ dualFlagDomain τ F G) (i : Fin n) : 0 < u i := by
  have hb := (dualFlagDomain_coordinate_bounds hp hP hτ0 F G hu i).1
  linarith

/-- The small parameter in FVW is exp(-R), while the actual primal dilation is radius R. -/
theorem dualFlagDomain_radius_eq {n : ℕ} {P : Set (Space n)} (R : ℝ)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) :
    dualFlagDomain (radius R) F G =
      dualCoordinates (flagMatrix G) '' ((fun y => (1 - Real.exp (-R)) • y) '' flagSimplex F) := rfl

theorem dualFlagDomain_radius_bounds {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    {R : ℝ} (hR : 0 < R) (F : FullFlagWithTop P)
    (G : FullFlagWithTop (coordinatePolar P)) {u : Space n}
    (hu : u ∈ dualFlagDomain (radius R) F G) (i : Fin n) :
    Real.exp (-R) ≤ u i ∧ u i ≤ 2 - Real.exp (-R) := by
  have hb := dualFlagDomain_coordinate_bounds hp hP (radius_pos hR).le F G hu i
  dsimp [radius] at hb
  constructor <;> linarith [hb.1, hb.2]

/-- Exact actual-domain transport, with nonzero determinant derived from polar geometry. -/
theorem flag_denominator_integral_eq_dualDomain {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P) (τ : ℝ)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) :
    (∫⁻ x in (fun y => τ • y) '' flagSimplex F,
      ENNReal.ofReal (|(flagMatrix G).det| /
        ((∏ i, (1 - dotProduct (flagMatrix G i) x)) * (n.factorial : ℝ)))) =
      ∫⁻ u in dualFlagDomain τ F G, dualProductKernel u :=
  lintegral_denominator_eq_dualCoordinates
    (flagMatrix_det_ne_zero (coordinatePolar_isSymmetricConvexBody hp hP) G)
    ((flagSimplex_isCompact F).image (continuous_id.const_smul τ)).measurableSet

end
end Funk
