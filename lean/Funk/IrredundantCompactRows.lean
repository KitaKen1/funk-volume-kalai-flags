import Funk.IrredundantRows

/-! In positive dimension a compact strip body rules out the exceptional
single zero row. The finite signed-irredundant reduction therefore supplies
nonzero, distinct, non-antipodal rows without assuming geometric simplicity. -/

open Set

namespace Funk
noncomputable section

theorem signedIrredundant_nonzero_of_compact {n : ℕ} [Nonempty (Fin n)] {ι : Type*}
    (rows : ι → Space n) (hi : SignedIrredundant rows)
    (hK : IsCompact (stripBody rows)) : ∀ j, rows j ≠ 0 := by
  intro j hj
  have hall : ∀ i, rows i = 0 := by
    intro i
    rw [signedIrredundant_zero_unique rows hi hj i, hj]
  apply hK.ne_univ
  ext X
  simp only [stripBody, mem_ofPred_eq, mem_univ, iff_true]
  intro i
  rw [hall i]
  simp

/-- A complete finite preprocessing certificate for a compact strip body.
The selection is increasing, so no permutation of retained labels is hidden. -/
theorem exists_normalized_row_presentation {n m : ℕ} (hn : 1 ≤ n)
    (rows : Fin m → Space n) (hK : IsCompact (stripBody rows)) :
    ∃ k ≤ m, ∃ selected : Fin k ↪o Fin m,
      SignedIrredundant (fun i => rows (selected i)) ∧
      Function.Injective (fun i => rows (selected i)) ∧
      (∀ i, rows (selected i) ≠ 0) ∧
      (∀ i j, i ≠ j → rows (selected i) ≠ -rows (selected j)) ∧
      signedRowHull (fun i => rows (selected i)) = signedRowHull rows ∧
      stripBody (fun i => rows (selected i)) = stripBody rows := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨k, hk, selected, hi, hh, he⟩ := exists_signedIrredundant_presentation rows
  exact ⟨k, hk, selected, hi, signedIrredundant_injective _ hi,
    signedIrredundant_nonzero_of_compact _ hi (he.symm ▸ hK),
    fun i j hij => signedIrredundant_no_opposite _ hi hij, hh, he⟩

end
end Funk
