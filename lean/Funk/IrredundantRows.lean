import Funk.MinimalRowFamily

/-! Finite row presentations admit a signed-convex-irredundant subfamily in
increasing original order. Irredundancy is not NoExtraActive: distinct genuine
constraints may still be active at the same witness. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

def SignedIrredundant {n : ℕ} {ι : Type*} (rows : ι → Space n) : Prop :=
  ∀ j, rows j ∉ signedRowHull (fun k : {k : ι // k ≠ j} => rows k.val)

theorem signedIrredundant_injective {n : ℕ} {ι : Type*}
    (rows : ι → Space n) (h : SignedIrredundant rows) : Function.Injective rows := by
  intro i j hij
  by_contra hne
  apply h i
  rw [hij]
  exact row_mem_signedRowHull (fun k : {k : ι // k ≠ i} => rows k.val) ⟨j, Ne.symm hne⟩

theorem signedIrredundant_no_opposite {n : ℕ} {ι : Type*}
    (rows : ι → Space n) (h : SignedIrredundant rows) {i j : ι} (hne : i ≠ j) :
    rows i ≠ -rows j := by
  intro hij
  apply h i
  rw [hij]
  exact neg_mem_signedRowHull _
    (row_mem_signedRowHull (fun k : {k : ι // k ≠ i} => rows k.val) ⟨j, Ne.symm hne⟩)

theorem signedIrredundant_ordered_subfamily {n : ℕ} {ι : Type*} [LinearOrder ι]
    (rows : ι → Space n) (s : Finset ι)
    (hs : ∀ j ∈ s, rows j ∉ signedRowHull (rowSubfamily rows (s.erase j))) :
    SignedIrredundant (fun i => rows (s.orderEmbOfFin rfl i)) := by
  intro i hi
  apply hs (s.orderEmbOfFin rfl i) (s.orderEmbOfFin_mem rfl i)
  apply signedRowHull_mono_of_range_subset _ _ ?_ hi
  rintro _ ⟨k, rfl⟩
  refine ⟨⟨s.orderEmbOfFin rfl k.val, Finset.mem_erase.mpr ⟨?_, ?_⟩⟩, rfl⟩
  · exact fun he => k.property ((s.orderEmbOfFin rfl).injective he)
  · exact s.orderEmbOfFin_mem rfl k.val

/-- At most the original number of rows, original increasing order, identical
signed hull and body, and no remaining signed-convex-redundant row. -/
theorem exists_signedIrredundant_presentation {n m : ℕ} (rows : Fin m → Space n) :
    ∃ k ≤ m, ∃ selected : Fin k ↪o Fin m,
      SignedIrredundant (fun i => rows (selected i)) ∧
      signedRowHull (fun i => rows (selected i)) = signedRowHull rows ∧
      stripBody (fun i => rows (selected i)) = stripBody rows := by
  obtain ⟨s, _, hH, hs⟩ := exists_minimal_rowSubfamily rows Finset.univ
  have hh : signedRowHull (fun i => rows (s.orderEmbOfFin rfl i)) = signedRowHull rows :=
    (signedRowHull_ordered_subfamily rows s).trans
      (hH.trans (signedRowHull_rowSubfamily_univ rows))
  refine ⟨s.card, ?_, s.orderEmbOfFin rfl, signedIrredundant_ordered_subfamily rows s hs,
    hh, stripBody_eq_of_signedRowHull_eq _ _ hh⟩
  exact (Finset.card_le_univ s).trans_eq (Fintype.card_fin m)

/-- A zero row in a signed-irredundant family can only be its sole row.
The exceptional zero-dimensional/unbounded presentation is not ignored. -/
theorem signedIrredundant_zero_unique {n : ℕ} {ι : Type*}
    (rows : ι → Space n) (h : SignedIrredundant rows) {i : ι} (hi : rows i = 0) :
    ∀ j, j = i := by
  intro j
  by_contra hji
  apply h i
  let others := fun k : {k : ι // k ≠ i} => rows k.val
  have hr : rows j ∈ signedRowHull others := row_mem_signedRowHull others ⟨j, hji⟩
  have hn := neg_mem_signedRowHull others hr
  have hz := (convex_convexHull ℝ (range others ∪ range (fun k => -others k))) hr hn
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have he : (1 / 2 : ℝ) • rows j + (1 / 2 : ℝ) • (-rows j) = 0 := by simp
  rw [he] at hz
  rw [hi]
  exact hz

/-- Reduction of the actual finite-strip Funk target to signed-irredundant
presentations. The premise is still the mathematical theorem to be proved. -/
theorem funkVolume_strip_target_of_signedIrredundant_case {n m : ℕ}
    (rows : Fin m → Space n) (hK : IsSymmetricConvexBody (stripBody rows))
    (τ : ℝ)
    (hcase : ∀ k ≤ m, ∀ reduced : Fin k → Space n,
      SignedIrredundant reduced → IsSymmetricConvexBody (stripBody reduced) →
      funkVolume (stripBody reduced) τ < ⊤ ∧
        ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) ≤
          funkVolume (stripBody reduced) τ) :
    funkVolume (stripBody rows) τ < ⊤ ∧
      ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) ≤
        funkVolume (stripBody rows) τ := by
  obtain ⟨k, hk, selected, hirr, _, he⟩ := exists_signedIrredundant_presentation rows
  have hred := hcase k hk (fun i => rows (selected i)) hirr (he.symm ▸ hK)
  rw [he] at hred
  exact hred

end
end Funk
