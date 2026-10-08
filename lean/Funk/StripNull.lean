import Funk.FeasibleRegion
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! The height endpoints are null in the original X coordinates. This is
independent of the nonlinear extra-active-row locus. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

theorem volume_dotProduct_level_zero {n : ℕ} (row : Space n) {c : ℝ} (hc : c ≠ 0) :
    volume {X : Space n | dotProduct row X = c} = 0 := by
  let S : AffineSubspace ℝ (Space n) :=
    (affineSpan ℝ ({c} : Set ℝ)).comap (dotProductBilin ℝ ℝ row).toAffineMap
  have he : (S : Set (Space n)) = {X : Space n | dotProduct row X = c} := by
    ext X
    simp [S]
  have htop : S ≠ ⊤ := by
    intro h
    have hzero : (0 : Space n) ∈ (S : Set (Space n)) := by rw [h]; trivial
    rw [he] at hzero
    have hval : (0 : ℝ) = c := by simpa using hzero
    exact hc hval.symm
  rw [← he]
  exact Measure.addHaar_affineSubspace volume S htop

/-- Countably many strip endpoints remain a null set, even with repeated or zero rows. -/
theorem ae_strict_strip_heights {n : ℕ} {ι : Type*} [Countable ι] (rows : ι → Space n) :
    ∀ᵐ X ∂volume.restrict (stripBody rows), ∀ j, |dotProduct (rows j) X| < 1 := by
  have hne (j : ι) : ∀ᵐ X ∂(volume : Measure (Space n)),
      dotProduct (rows j) X ≠ 1 ∧ dotProduct (rows j) X ≠ -1 := by
    have hp : ∀ᵐ X ∂(volume : Measure (Space n)), dotProduct (rows j) X ≠ 1 := by
      apply ae_iff.mpr
      simpa only [not_not] using volume_dotProduct_level_zero (rows j) (by norm_num : (1 : ℝ) ≠ 0)
    have hm : ∀ᵐ X ∂(volume : Measure (Space n)), dotProduct (rows j) X ≠ -1 := by
      apply ae_iff.mpr
      simpa only [not_not] using volume_dotProduct_level_zero (rows j) (by norm_num : (-1 : ℝ) ≠ 0)
    exact hp.and hm
  have hall : ∀ᵐ X ∂(volume : Measure (Space n)), ∀ j,
      dotProduct (rows j) X ≠ 1 ∧ dotProduct (rows j) X ≠ -1 := ae_all_iff.mpr hne
  filter_upwards [ae_restrict_of_ae hall,
    ae_restrict_mem (μ := volume) (measurableSet_stripBody rows)] with X hX hmem
  intro j
  have hb := abs_le.mp (hmem j)
  rw [abs_lt]
  exact ⟨lt_of_le_of_ne hb.1 (hX j).2.symm, lt_of_le_of_ne hb.2 (hX j).1⟩

end
end Funk
