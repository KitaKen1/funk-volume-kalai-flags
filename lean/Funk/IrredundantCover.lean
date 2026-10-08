import Funk.ExtraActiveNull
import Funk.CanonicalBasisFamily
import Funk.RowRedundancy
import Funk.IrredundantCollision

/-! Almost-everywhere simplicity is now supplied by proved geometry and
measure theory. The probability covering inequality is the remaining explicit
input to the actual finite-strip Funk lower bound. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

theorem ae_canonical_noExtraActive {n m : ℕ} (hn : 1 ≤ n) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n)
    (hirr : SignedIrredundant rows) (hK : IsCompact (stripBody rows)) :
    ∀ᵐ X ∂volume.restrict (stripBody rows), ∀ k ∈ canonicalBasisIndices rows,
      NoExtraActive τ rows k.1 k.2 X := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply ae_all_iff.mpr
  intro k
  by_cases hk : k ∈ canonicalBasisIndices rows
  · exact (ae_noExtraActive_irredundant_compact hτ0 hτ1 rows hirr hK k.1
      ((mem_canonicalBasisIndices rows k).mp hk).2 k.2).mono (fun _ h _ => h)
  · exact Filter.Eventually.of_forall (fun _ h => (hk h).elim)

/-- Every compact positive-dimensional finite strip presentation admits an
increasing hull-preserving subfamily with a.e. simple canonical bases. -/
theorem exists_ae_simple_row_presentation {n m : ℕ} (hn : 1 ≤ n) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n)
    (hK : IsCompact (stripBody rows)) :
    ∃ k ≤ m, ∃ selected : Fin k ↪o Fin m,
      SignedIrredundant (fun i => rows (selected i)) ∧
      signedRowHull (fun i => rows (selected i)) = signedRowHull rows ∧
      stripBody (fun i => rows (selected i)) = stripBody rows ∧
      ∀ᵐ X ∂volume.restrict (stripBody rows),
        ∀ c ∈ canonicalBasisIndices (fun i => rows (selected i)),
          NoExtraActive τ (fun i => rows (selected i)) c.1 c.2 X := by
  obtain ⟨k, hk, selected, hirr, hh, he⟩ := exists_signedIrredundant_presentation rows
  refine ⟨k, hk, selected, hirr, hh, he, ?_⟩
  have hs := ae_canonical_noExtraActive hn hτ0 hτ1 (fun i => rows (selected i))
    hirr (he.symm ▸ hK)
  rwa [he] at hs

/-- No unproved simplicity hypothesis remains. Covering is still a premise. -/
theorem funkVolume_strip_target_of_irredundant_cover {n m : ℕ} (hn : 1 ≤ n)
    (rows : Fin m → Space n) (hirr : SignedIrredundant rows)
    (hK : IsSymmetricConvexBody (stripBody rows)) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hcover : 1 ≤ ∑ k ∈ canonicalBasisIndices rows, lensBoundaryRows n τ
      (basisBoundaryEvent τ k.2 (fun i => rows (k.1 i)) (basisFeasibleRegion τ rows k.1 k.2))) :
    funkVolume (stripBody rows) τ < ⊤ ∧
      ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) ≤
        funkVolume (stripBody rows) τ := by
  apply funkVolume_strip_target_of_canonical_cover rows hK hτ0 hτ1 ?_ hcover
  filter_upwards [ae_canonical_noExtraActive hn hτ0 hτ1 rows hirr hK.1] with X hX
  exact fun k hk _ => hX k hk

/-- Equal signed hulls transfer the actual conclusion to the original body.
Only the reduced family's covering inequality is requested. -/
theorem funkVolume_strip_target_of_reduced_irredundant_cover {n m : ℕ} {ι : Type*}
    (hn : 1 ≤ n) (rows : ι → Space n) (reduced : Fin m → Space n)
    (hh : signedRowHull rows = signedRowHull reduced) (hirr : SignedIrredundant reduced)
    (hK : IsSymmetricConvexBody (stripBody rows)) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hcover : 1 ≤ ∑ k ∈ canonicalBasisIndices reduced, lensBoundaryRows n τ
      (basisBoundaryEvent τ k.2 (fun i => reduced (k.1 i))
        (basisFeasibleRegion τ reduced k.1 k.2))) :
    funkVolume (stripBody rows) τ < ⊤ ∧
      ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) ≤
        funkVolume (stripBody rows) τ := by
  have he := stripBody_eq_of_signedRowHull_eq rows reduced hh
  rw [he] at hK ⊢
  exact funkVolume_strip_target_of_irredundant_cover hn reduced hirr hK hτ0 hτ1 hcover

/-- A calibration where pointwise simplicity fails but a.e. simplicity holds. -/
theorem octahedralRows_ae_noExtraActive {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ∀ᵐ X ∂volume.restrict (stripBody octahedralRows),
      NoExtraActive τ octahedralRows Fin.castSucc (fun _ => true) X := by
  apply ae_noExtraActive_signedIrredundant hτ0 hτ1 octahedralRows
    octahedralRows_signedIrredundant ?_ Fin.castSucc octahedralRows_basis_det
  intro j hj
  have h := congr_fun hj 0
  fin_cases j <;> norm_num [octahedralRows] at h

end
end Funk
