import Funk.ProjectiveSimplex
import Funk.FlagSimplexCover

/-! A concrete finite cover of every actual translated polar by transformed
simplices of the original polar. This removes both covering premises from the
matrix integral upper bound. The sharp asymptotic coefficient and the
order-reversing primal/dual flag correspondence are not proved here. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

def shiftedPolarFlagMatrix {n : ℕ} {P : Set (Space n)}
    (G : FullFlagWithTop (coordinatePolar P)) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ := shiftedRowMatrix (flagMatrix G) x

theorem polarFlag_denominator_pos {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) {X : Space n} (hX : X ∈ P)
    (G : FullFlagWithTop (coordinatePolar P)) (i : Fin n) :
    0 < 1 - dotProduct (flagMatrix G i) (τ • X) :=
  polarShift_denominator_pos hτ0 hτ1 hX
    (flagPoint_mem_polytope (coordinatePolar_isSymmetricConvexBody hp hP) G i.castSucc)

/-- Every transformed simplex is genuinely contained in the actual translated polar. -/
theorem shiftedPolarFlagSimplex_subset {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) {X : Space n} (hX : X ∈ P)
    (G : FullFlagWithTop (coordinatePolar P)) :
    rowSimplex (shiftedPolarFlagMatrix G (τ • X)) ⊆ coordinatePolar (translate P (τ • X)) := by
  apply convexHull_min _ (convex_coordinatePolar _)
  rintro w (rfl | ⟨i, rfl⟩)
  · exact zero_mem_coordinatePolar _
  · exact polarShift_mem_translatedPolar
      (flagPoint_mem_polytope (coordinatePolar_isSymmetricConvexBody hp hP) G i.castSucc)
      (polarFlag_denominator_pos hp hP hτ0 hτ1 hX G i)

/-- The static polar flag cover supplies a cover for the nonsymmetric translated polar. -/
theorem translatedPolar_subset_shiftedFlagSimplices {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) {X : Space n} (hX : X ∈ P) :
    coordinatePolar (translate P (τ • X)) ⊆
      ⋃ G : FullFlagWithTop (coordinatePolar P), rowSimplex (shiftedPolarFlagMatrix G (τ • X)) := by
  intro w hw
  rw [translatedPolar_eq_polarShift_image hP hτ0 hτ1 hX] at hw
  obtain ⟨y, hy, rfl⟩ := hw
  have hp' := coordinatePolar_isFinitePolytope hp hP.2.1 hP.2.2.2
  have hP' := coordinatePolar_isSymmetricConvexBody hp hP
  obtain ⟨G, hG⟩ := Set.mem_iUnion.mp (body_subset_flagSimplices hp' hP' hy)
  apply Set.mem_iUnion.mpr
  refine ⟨G, polarShift_rowSimplex_subset (flagMatrix G) (τ • X) ?_ ?_⟩
  · intro z hz
    have hz' : z ∈ coordinatePolar P := flagSimplex_subset_polytope hP' G
      ((flagSimplex_eq_rowSimplex G).symm ▸ hz)
    exact polarShift_denominator_pos hτ0 hτ1 hX hz'
  · exact ⟨y, (flagSimplex_eq_rowSimplex G) ▸ hG, rfl⟩

theorem translatedPolar_eq_shiftedFlagSimplices {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) {X : Space n} (hX : X ∈ P) :
    coordinatePolar (translate P (τ • X)) =
      ⋃ G : FullFlagWithTop (coordinatePolar P), rowSimplex (shiftedPolarFlagMatrix G (τ • X)) :=
  Set.Subset.antisymm (translatedPolar_subset_shiftedFlagSimplices hp hP hτ0 hτ1 hX)
    (Set.iUnion_subset (shiftedPolarFlagSimplex_subset hp hP hτ0 hτ1 hX))

theorem measurable_shiftedPolarFlagMatrix {n : ℕ} {P : Set (Space n)}
    (G : FullFlagWithTop (coordinatePolar P)) :
    Measurable (fun x i j => shiftedPolarFlagMatrix G x i j) :=
  measurable_shiftedRowMatrix (flagMatrix G)

theorem volume_shiftedPolarFlagSimplex {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) {X : Space n} (hX : X ∈ P)
    (G : FullFlagWithTop (coordinatePolar P)) :
    volume (rowSimplex (shiftedPolarFlagMatrix G (τ • X))) =
      ENNReal.ofReal (|(flagMatrix G).det| /
        ((∏ i, (1 - dotProduct (flagMatrix G i) (τ • X))) * (n.factorial : ℝ))) :=
  volume_shiftedRowSimplex _ _ (polarFlag_denominator_pos hp hP hτ0 hτ1 hX G)

/-- Both actual covers and matrix measurability are proved; no such certificates are inputs. -/
theorem funkVolume_le_shiftedPolarFlag_integrals {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    let : Finite (FullFlagWithTop P) := fullFlagWithTop_finite hp hP
    let : Fintype (FullFlagWithTop P) := Fintype.ofFinite (FullFlagWithTop P)
    let : Finite (FullFlagWithTop (coordinatePolar P)) := fullFlagWithTop_finite
      (coordinatePolar_isFinitePolytope hp hP.2.1 hP.2.2.2)
      (coordinatePolar_isSymmetricConvexBody hp hP)
    let : Fintype (FullFlagWithTop (coordinatePolar P)) :=
      Fintype.ofFinite (FullFlagWithTop (coordinatePolar P))
    funkVolume P τ ≤ ∑ F : FullFlagWithTop P, ∑ G : FullFlagWithTop (coordinatePolar P),
      ∫⁻ x in (fun y => τ • y) '' flagSimplex F,
        ENNReal.ofReal (|(shiftedPolarFlagMatrix G x).det| / (n.factorial : ℝ)) := by
  let : Finite (FullFlagWithTop P) := fullFlagWithTop_finite hp hP
  let : Fintype (FullFlagWithTop P) := Fintype.ofFinite (FullFlagWithTop P)
  let : Finite (FullFlagWithTop (coordinatePolar P)) := fullFlagWithTop_finite
    (coordinatePolar_isFinitePolytope hp hP.2.1 hP.2.2.2)
    (coordinatePolar_isSymmetricConvexBody hp hP)
  let : Fintype (FullFlagWithTop (coordinatePolar P)) :=
    Fintype.ofFinite (FullFlagWithTop (coordinatePolar P))
  apply funkVolume_le_flag_rowSimplex_of_polar_cover hp hP τ shiftedPolarFlagMatrix
  · rintro _ ⟨X, hX, rfl⟩
    exact translatedPolar_subset_shiftedFlagSimplices hp hP hτ0 hτ1 hX
  · exact measurable_shiftedPolarFlagMatrix

/-- The explicit product of positive denominators bounds the original frozen integral. -/
theorem funkVolume_le_polarFlag_denominator_integrals {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    let : Finite (FullFlagWithTop P) := fullFlagWithTop_finite hp hP
    let : Fintype (FullFlagWithTop P) := Fintype.ofFinite (FullFlagWithTop P)
    let : Finite (FullFlagWithTop (coordinatePolar P)) := fullFlagWithTop_finite
      (coordinatePolar_isFinitePolytope hp hP.2.1 hP.2.2.2)
      (coordinatePolar_isSymmetricConvexBody hp hP)
    let : Fintype (FullFlagWithTop (coordinatePolar P)) :=
      Fintype.ofFinite (FullFlagWithTop (coordinatePolar P))
    funkVolume P τ ≤ ∑ F : FullFlagWithTop P, ∑ G : FullFlagWithTop (coordinatePolar P),
      ∫⁻ x in (fun y => τ • y) '' flagSimplex F,
        ENNReal.ofReal (|(flagMatrix G).det| /
          ((∏ i, (1 - dotProduct (flagMatrix G i) x)) * (n.factorial : ℝ))) := by
  let : Finite (FullFlagWithTop P) := fullFlagWithTop_finite hp hP
  let : Fintype (FullFlagWithTop P) := Fintype.ofFinite (FullFlagWithTop P)
  let : Finite (FullFlagWithTop (coordinatePolar P)) := fullFlagWithTop_finite
    (coordinatePolar_isFinitePolytope hp hP.2.1 hP.2.2.2)
    (coordinatePolar_isSymmetricConvexBody hp hP)
  let : Fintype (FullFlagWithTop (coordinatePolar P)) :=
    Fintype.ofFinite (FullFlagWithTop (coordinatePolar P))
  apply le_trans (funkVolume_le_shiftedPolarFlag_integrals hp hP hτ0 hτ1)
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro F _
  apply Finset.sum_congr rfl
  intro G _
  have hc : Continuous (fun y : Space n => τ • y) := continuous_id.const_smul τ
  apply setLIntegral_congr_fun ((flagSimplex_isCompact F).image hc).measurableSet
  rintro x ⟨X, hX, rfl⟩
  simpa only [volume_rowSimplex] using
    volume_shiftedPolarFlagSimplex hp hP hτ0 hτ1 (flagSimplex_subset_polytope hP F hX) G

end
end Funk
