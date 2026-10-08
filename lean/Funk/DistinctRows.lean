import Funk.RowRedundancy
import Mathlib.Data.Fintype.EquivFin

/-! Exact duplicate compression of a finite row presentation. The enumeration
is classical, not a numerical comparison of real vectors. Only identical rows
are automatically removed; signed or convex redundancy uses RowRedundancy. -/

open Set MeasureTheory

namespace Funk
noncomputable section

def distinctRowSet {n m : ℕ} (rows : Fin m → Space n) : Finset (Space n) := by
  classical
  exact Finset.univ.image rows

def distinctRows {n m : ℕ} (rows : Fin m → Space n) :
    Fin (distinctRowSet rows).card → Space n :=
  fun i => ((distinctRowSet rows).equivFin.symm i).val

def distinctRowIndex {n m : ℕ} (rows : Fin m → Space n) (j : Fin m) :
    Fin (distinctRowSet rows).card :=
  (distinctRowSet rows).equivFin ⟨rows j, by classical simp [distinctRowSet]⟩

theorem distinctRows_injective {n m : ℕ} (rows : Fin m → Space n) :
    Function.Injective (distinctRows rows) := by
  intro i j h
  apply (distinctRowSet rows).equivFin.symm.injective
  exact Subtype.ext h

theorem distinctRows_index {n m : ℕ} (rows : Fin m → Space n) (j : Fin m) :
    distinctRows rows (distinctRowIndex rows j) = rows j := by
  simp [distinctRows, distinctRowIndex]

theorem distinctRowIndex_eq_iff {n m : ℕ} (rows : Fin m → Space n) (i j : Fin m) :
    distinctRowIndex rows i = distinctRowIndex rows j ↔ rows i = rows j := by
  constructor
  · intro h
    simpa only [distinctRows_index] using congr_arg (distinctRows rows) h
  · intro h
    apply distinctRows_injective rows
    simpa only [distinctRows_index] using h

theorem range_distinctRows {n m : ℕ} (rows : Fin m → Space n) :
    range (distinctRows rows) = range rows := by
  classical
  apply Subset.antisymm
  · rintro _ ⟨i, rfl⟩
    have hi := ((distinctRowSet rows).equivFin.symm i).property
    change distinctRows rows i ∈ distinctRowSet rows at hi
    simpa only [distinctRowSet, Finset.mem_image, Finset.mem_univ, true_and,
      mem_range] using hi
  · rintro _ ⟨j, rfl⟩
    exact ⟨distinctRowIndex rows j, distinctRows_index rows j⟩

theorem distinctRowIndex_surjective {n m : ℕ} (rows : Fin m → Space n) :
    Function.Surjective (distinctRowIndex rows) := by
  intro i
  obtain ⟨j, hj⟩ := (range_distinctRows rows) ▸ mem_range_self i
  refine ⟨j, distinctRows_injective rows ?_⟩
  exact (distinctRows_index rows j).trans hj

theorem card_distinctRowSet_le {n m : ℕ} (rows : Fin m → Space n) :
    (distinctRowSet rows).card ≤ m := by
  classical
  exact (Finset.card_image_le).trans_eq (Finset.card_univ.trans (Fintype.card_fin m))

theorem signedRowHull_distinctRows {n m : ℕ} (rows : Fin m → Space n) :
    signedRowHull (distinctRows rows) = signedRowHull rows :=
  signedRowHull_eq_of_range_eq _ _ (range_distinctRows rows)

theorem stripBody_distinctRows {n m : ℕ} (rows : Fin m → Space n) :
    stripBody (distinctRows rows) = stripBody rows :=
  stripBody_eq_of_signedRowHull_eq _ _ (signedRowHull_distinctRows rows)

theorem basisFeasibleRegion_distinctRows {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n)
    (s : Fin n → Fin m) (b : Fin n → Bool) :
    basisFeasibleRegion τ (distinctRows rows) (distinctRowIndex rows ∘ s) b =
      basisFeasibleRegion τ rows s b := by
  apply basisFeasibleRegion_eq_of_signedRowHull_eq hτ0 hτ1
    _ _ (signedRowHull_distinctRows rows)
  exact fun i => distinctRows_index rows (s i)

theorem basisBoundaryEvent_distinctRows {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n)
    (s : Fin n → Fin m) (b : Fin n → Bool) :
    basisBoundaryEvent τ b (fun i => distinctRows rows (distinctRowIndex rows (s i)))
      (basisFeasibleRegion τ (distinctRows rows) (distinctRowIndex rows ∘ s) b) =
    basisBoundaryEvent τ b (fun i => rows (s i)) (basisFeasibleRegion τ rows s b) := by
  apply basisBoundaryEvent_eq_of_signedRowHull_eq hτ0 hτ1
    _ _ (signedRowHull_distinctRows rows)
  exact fun i => distinctRows_index rows (s i)

/-- Every finite presentation has a no-longer row family with no identical rows.
This is not an irredundant facet presentation or a simplicity theorem. -/
theorem exists_injective_row_presentation {n m : ℕ} (rows : Fin m → Space n) :
    ∃ k ≤ m, ∃ reduced : Fin k → Space n, Function.Injective reduced ∧
      signedRowHull reduced = signedRowHull rows ∧ stripBody reduced = stripBody rows :=
  ⟨_, card_distinctRowSet_le rows, _, distinctRows_injective rows,
    signedRowHull_distinctRows rows, stripBody_distinctRows rows⟩

/-- Simplicity stated using row values rather than the original labels.
It still excludes distinct additional active vectors, and is not automatic. -/
def NoExtraRowValue {n : ℕ} {ι : Type*} (τ : ℝ) (rows : ι → Space n)
    (s : Fin n → ι) (b : Fin n → Bool) (X : Space n) : Prop :=
  ∀ j, complexRow (rows j) (basisRealWitness τ b (fun i => rows (s i)) X) X ∈
    frontier (lensGraphBody τ) → rows j ∈ range (fun i => rows (s i))

theorem noExtraActive_iff_noExtraRowValue {n : ℕ} {ι : Type*}
    (τ : ℝ) (rows : ι → Space n) (hr : Function.Injective rows)
    (s : Fin n → ι) (b : Fin n → Bool) (X : Space n) :
    NoExtraActive τ rows s b X ↔ NoExtraRowValue τ rows s b X := by
  constructor
  · intro h j hj
    obtain ⟨i, hi⟩ := h j hj
    exact ⟨i, congr_arg rows hi⟩
  · intro h j hj
    obtain ⟨i, hi⟩ := h j hj
    exact ⟨i, hr hi⟩

/-- The compressed simplicity condition ignores only repeated labels.
No almost-everywhere claim about distinct active row values is smuggled in. -/
theorem noExtraActive_distinctRows_iff {n m : ℕ}
    (τ : ℝ) (rows : Fin m → Space n) (s : Fin n → Fin m)
    (b : Fin n → Bool) (X : Space n) :
    NoExtraActive τ (distinctRows rows) (distinctRowIndex rows ∘ s) b X ↔
      NoExtraRowValue τ rows s b X := by
  rw [noExtraActive_iff_noExtraRowValue τ _ (distinctRows_injective rows)]
  simp only [NoExtraRowValue, Function.comp_apply, distinctRows_index]
  constructor
  · intro h j hj
    simpa only [distinctRows_index] using h (distinctRowIndex rows j)
      (by simpa only [distinctRows_index] using hj)
  · intro h j hj
    obtain ⟨k, hk⟩ := (range_distinctRows rows) ▸ mem_range_self j
    rw [← hk] at hj ⊢
    exact h k hj

end
end Funk
