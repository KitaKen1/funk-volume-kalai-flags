import Funk.CanonicalBasisFamily

/-! Redundant row constraints can be removed before the packing argument.
The symmetric convex hull of the rows controls both the real strip body and
all complex lens constraints. This does not prove simplicity of the reduced
family, nor identify which rows are extreme. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

/-- The geometric row data, forgetting labels, duplicates and convex redundancy. -/
def signedRowHull {n : ℕ} {ι : Type*} (rows : ι → Space n) : Set (Space n) :=
  convexHull ℝ (range rows ∪ range (fun j => -rows j))

def complexRowMap {n : ℕ} (Y X : Space n) : Space n →ₗ[ℝ] ℂ where
  toFun := fun row => complexRow row Y X
  map_add' := by
    intro u v
    apply Complex.ext <;> simp [complexRow, add_dotProduct]
  map_smul' := by
    intro a u
    apply Complex.ext <;> simp [complexRow, smul_dotProduct]

theorem row_mem_signedRowHull {n : ℕ} {ι : Type*} (rows : ι → Space n) (j : ι) :
    rows j ∈ signedRowHull rows :=
  subset_convexHull ℝ _ (Or.inl (mem_range_self j))

theorem neg_mem_signedRowHull {n : ℕ} {ι : Type*} (rows : ι → Space n)
    {row : Space n} (hr : row ∈ signedRowHull rows) : -row ∈ signedRowHull rows := by
  have hsub : signedRowHull rows ⊆
      (-LinearMap.id : Space n →ₗ[ℝ] Space n) ⁻¹' signedRowHull rows := by
    apply convexHull_min _ ((convex_convexHull ℝ _).linear_preimage _)
    rintro r (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact subset_convexHull ℝ _ (Or.inr (mem_range_self j))
    · change -(-rows j) ∈ signedRowHull rows
      simpa only [neg_neg] using row_mem_signedRowHull rows j
  exact hsub hr

/-- A finite convex-combination certificate for every deleted row suffices. -/
theorem signedRowHull_eq_of_mutual_mem {n : ℕ} {ι κ : Type*}
    (rows : ι → Space n) (reduced : κ → Space n)
    (hr : ∀ j, rows j ∈ signedRowHull reduced)
    (hs : ∀ j, reduced j ∈ signedRowHull rows) :
    signedRowHull rows = signedRowHull reduced := by
  apply Subset.antisymm
  · apply convexHull_min _ (convex_convexHull ℝ _)
    rintro r (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact hr j
    · exact neg_mem_signedRowHull reduced (hr j)
  · apply convexHull_min _ (convex_convexHull ℝ _)
    rintro r (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact hs j
    · exact neg_mem_signedRowHull rows (hs j)

theorem signedRowHull_eq_of_range_eq {n : ℕ} {ι κ : Type*}
    (rows : ι → Space n) (reduced : κ → Space n) (hr : range rows = range reduced) :
    signedRowHull rows = signedRowHull reduced := by
  apply signedRowHull_eq_of_mutual_mem rows reduced
  · intro j
    obtain ⟨k, hk⟩ := hr ▸ mem_range_self j
    rw [← hk]
    exact row_mem_signedRowHull reduced k
  · intro j
    obtain ⟨k, hk⟩ := hr.symm ▸ mem_range_self j
    rw [← hk]
    exact row_mem_signedRowHull rows k

theorem strip_constraint_of_mem_signedRowHull {n : ℕ} {ι : Type*}
    (rows : ι → Space n) {X row : Space n} (hX : X ∈ stripBody rows)
    (hr : row ∈ signedRowHull rows) : |dotProduct row X| ≤ 1 := by
  have hsub : signedRowHull rows ⊆
      (dotProductBilin ℝ ℝ X) ⁻¹' Icc (-1 : ℝ) 1 := by
    apply convexHull_min _ ((convex_Icc (-1 : ℝ) 1).linear_preimage _)
    rintro r (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · change -1 ≤ dotProduct X (rows j) ∧ dotProduct X (rows j) ≤ 1
      simpa only [dotProduct_comm] using abs_le.mp (hX j)
    · change -1 ≤ dotProduct X (-rows j) ∧ dotProduct X (-rows j) ≤ 1
      have hj := abs_le.mp (hX j)
      rw [dotProduct_neg, dotProduct_comm]
      constructor <;> linarith
  have h := hsub hr
  change -1 ≤ dotProduct X row ∧ dotProduct X row ≤ 1 at h
  rw [dotProduct_comm] at h
  exact abs_le.mpr h

theorem lens_constraint_of_mem_signedRowHull {n : ℕ} {ι : Type*}
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : ι → Space n)
    {X Y row : Space n} (hY : ∀ j, complexRow (rows j) Y X ∈ lensGraphBody τ)
    (hr : row ∈ signedRowHull rows) : complexRow row Y X ∈ lensGraphBody τ := by
  have hsub : signedRowHull rows ⊆ (complexRowMap Y X) ⁻¹' lensGraphBody τ := by
    apply convexHull_min _ ((lensGraphBody_convex hτ0 hτ1).linear_preimage _)
    rintro r (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact hY j
    · change complexRow (-rows j) Y X ∈ lensGraphBody τ
      have he : complexRow (-rows j) Y X = -complexRow (rows j) Y X := by
        apply Complex.ext <;> simp [complexRow, neg_dotProduct]
      rw [he]
      exact lensGraphBody_neg (hY j)
  exact hsub hr

theorem stripBody_eq_of_signedRowHull_eq {n : ℕ} {ι κ : Type*}
    (rows : ι → Space n) (reduced : κ → Space n)
    (hh : signedRowHull rows = signedRowHull reduced) :
    stripBody rows = stripBody reduced := by
  ext X
  constructor
  · intro h j
    apply strip_constraint_of_mem_signedRowHull rows h
    rw [hh]
    exact row_mem_signedRowHull reduced j
  · intro h j
    apply strip_constraint_of_mem_signedRowHull reduced h
    rw [← hh]
    exact row_mem_signedRowHull rows j

theorem lens_constraints_iff_of_signedRowHull_eq {n : ℕ} {ι κ : Type*}
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (rows : ι → Space n) (reduced : κ → Space n)
    (hh : signedRowHull rows = signedRowHull reduced) (Y X : Space n) :
    (∀ j, complexRow (rows j) Y X ∈ lensGraphBody τ) ↔
      ∀ j, complexRow (reduced j) Y X ∈ lensGraphBody τ := by
  constructor
  · intro h j
    apply lens_constraint_of_mem_signedRowHull hτ0 hτ1 rows h
    rw [hh]
    exact row_mem_signedRowHull reduced j
  · intro h j
    apply lens_constraint_of_mem_signedRowHull hτ0 hτ1 reduced h
    rw [← hh]
    exact row_mem_signedRowHull rows j

/-- Preserve the actual feasible region when the selected basis rows match.
There is no assertion that all old labeled bases should still be counted. -/
theorem basisFeasibleRegion_eq_of_signedRowHull_eq {n : ℕ} {ι κ : Type*}
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (rows : ι → Space n) (reduced : κ → Space n)
    (hh : signedRowHull rows = signedRowHull reduced)
    (s : Fin n → ι) (t : Fin n → κ) (b : Fin n → Bool)
    (hst : ∀ i, rows (s i) = reduced (t i)) :
    basisFeasibleRegion τ rows s b = basisFeasibleRegion τ reduced t b := by
  have he : (fun i => rows (s i) : Matrix (Fin n) (Fin n) ℝ) =
      (fun i => reduced (t i)) := funext hst
  ext X
  simp only [basisFeasibleRegion, mem_ofPred_eq, he,
    stripBody_eq_of_signedRowHull_eq rows reduced hh]
  exact and_congr Iff.rfl
    (lens_constraints_iff_of_signedRowHull_eq hτ0 hτ1 rows reduced hh _ X)

theorem basisBoundaryEvent_eq_of_signedRowHull_eq {n : ℕ} {ι κ : Type*}
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (rows : ι → Space n) (reduced : κ → Space n)
    (hh : signedRowHull rows = signedRowHull reduced)
    (s : Fin n → ι) (t : Fin n → κ) (b : Fin n → Bool)
    (hst : ∀ i, rows (s i) = reduced (t i)) :
    basisBoundaryEvent τ b (fun i => rows (s i)) (basisFeasibleRegion τ rows s b) =
      basisBoundaryEvent τ b (fun i => reduced (t i)) (basisFeasibleRegion τ reduced t b) := by
  rw [basisFeasibleRegion_eq_of_signedRowHull_eq hτ0 hτ1 rows reduced hh s t b hst]
  exact congr_arg (fun B => basisBoundaryEvent τ b B
    (basisFeasibleRegion τ reduced t b)) (funext hst)

/-- A proof for a reduced presentation proves the same actual Funk statement
for the original body. Simplicity and covering concern only the reduced rows. -/
theorem funkVolume_strip_target_of_reduced_canonical_cover {n m : ℕ} {ι : Type*}
    (rows : ι → Space n) (reduced : Fin m → Space n)
    (hh : signedRowHull rows = signedRowHull reduced)
    (hK : IsSymmetricConvexBody (stripBody rows))
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hsimple : ∀ᵐ X ∂volume.restrict (stripBody reduced), ∀ k ∈ canonicalBasisIndices reduced,
      X ∈ basisFeasibleRegion τ reduced k.1 k.2 → NoExtraActive τ reduced k.1 k.2 X)
    (hcover : 1 ≤ ∑ k ∈ canonicalBasisIndices reduced, lensBoundaryRows n τ
      (basisBoundaryEvent τ k.2 (fun i => reduced (k.1 i))
        (basisFeasibleRegion τ reduced k.1 k.2))) :
    funkVolume (stripBody rows) τ < ⊤ ∧
      ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) ≤
        funkVolume (stripBody rows) τ := by
  have he := stripBody_eq_of_signedRowHull_eq rows reduced hh
  rw [he] at hK ⊢
  exact funkVolume_strip_target_of_canonical_cover reduced hK hτ0 hτ1 hsimple hcover

end
end Funk
