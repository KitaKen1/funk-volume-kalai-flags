import Funk.DistinctRows

/-! A calibration with positive, negative, half-size and repeated constraints.
The reduced presentation proves the actual Funk inequality although the old
labeled presentation fails NoExtraActive at every feasible selected witness. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

def expandedRows {n : ℕ} {ι : Type*} (rows : ι → Space n) : ι × Fin 4 → Space n :=
  fun k => if k.2 = 0 then rows k.1 else if k.2 = 1 then -rows k.1 else
    if k.2 = 2 then (1 / 2 : ℝ) • rows k.1 else rows k.1

theorem signedRowHull_expandedRows {n : ℕ} {ι : Type*} (rows : ι → Space n) :
    signedRowHull (expandedRows rows) = signedRowHull rows := by
  apply signedRowHull_eq_of_mutual_mem
  · rintro ⟨i, tag⟩
    have hr := row_mem_signedRowHull rows i
    have hn := neg_mem_signedRowHull rows hr
    fin_cases tag
    · simpa [expandedRows] using hr
    · simpa [expandedRows] using hn
    · change (1 / 2 : ℝ) • rows i ∈ signedRowHull rows
      have hc := (convex_convexHull ℝ (range rows ∪ range (fun j => -rows j))) hr hn
        (show (0 : ℝ) ≤ 3 / 4 by norm_num) (show (0 : ℝ) ≤ 1 / 4 by norm_num)
        (show (3 / 4 : ℝ) + 1 / 4 = 1 by norm_num)
      have he : (1 / 2 : ℝ) • rows i = (3 / 4 : ℝ) • rows i + (1 / 4 : ℝ) • (-rows i) := by
        ext j
        change (1 / 2 : ℝ) * rows i j = 3 / 4 * rows i j + 1 / 4 * (-rows i j)
        ring
      rw [he]
      exact hc
    · simpa [expandedRows] using hr
  · intro j
    simpa [expandedRows] using row_mem_signedRowHull (expandedRows rows) (j, 0)

theorem basisFeasibleRegion_expandedRows {n : ℕ} {ι : Type*} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : ι → Space n)
    (s : Fin n → ι) (b : Fin n → Bool) :
    basisFeasibleRegion τ (expandedRows rows) (fun i => (s i, 0)) b =
      basisFeasibleRegion τ rows s b := by
  apply basisFeasibleRegion_eq_of_signedRowHull_eq hτ0 hτ1
    _ _ (signedRowHull_expandedRows rows)
  intro i
  simp [expandedRows]

/-- Even the stronger redundant presentation may fail the old auxiliary input.
Its strip body and matched feasible events can nevertheless be reduced exactly. -/
theorem expandedRows_not_noExtraActive {n : ℕ} {ι : Type*} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : ι → Space n)
    (s : Fin n → ι) (b : Fin n → Bool)
    (hB : Matrix.det (fun i => rows (s i)) ≠ 0) {X : Space n}
    (hS : X ∈ basisFeasibleRegion τ rows s b) (i : Fin n) :
    ¬NoExtraActive τ (expandedRows rows) (fun i => (s i, 0)) b X := by
  apply noExtraActive_false_of_duplicate hτ0 hτ1 (expandedRows rows)
    (fun i => (s i, 0)) b (by simpa [expandedRows] using hB)
    (by rwa [basisFeasibleRegion_expandedRows hτ0 hτ1]) i (s i, 3)
  · rintro ⟨j, hj⟩
    have ht := congr_arg Prod.snd hj
    norm_num at ht
  · simp [expandedRows]

/-- All dimensions, every allowed radius; the redundant labeled constraints do
not obstruct the actual target once the presentation is reduced. -/
theorem expandedCube_funk_target (n : ℕ) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    funkVolume (stripBody (expandedRows (1 : Matrix (Fin n) (Fin n) ℝ))) τ < ⊤ ∧
      ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) ≤
        funkVolume (stripBody (expandedRows (1 : Matrix (Fin n) (Fin n) ℝ))) τ := by
  rw [stripBody_eq_of_signedRowHull_eq _ _
    (signedRowHull_expandedRows (1 : Matrix (Fin n) (Fin n) ℝ))]
  exact cube_funk_target_via_canonical_basis n hτ0 hτ1

/-- The previous duplicate-interval obstruction disappears after exact
compression: every remaining active row is a selected row. -/
theorem duplicateInterval_compressed_simple (τ : ℝ) (b : Fin 1 → Bool) (X : Space 1) :
    NoExtraActive τ (distinctRows duplicateIntervalRows)
      (distinctRowIndex duplicateIntervalRows ∘ (fun _ : Fin 1 => (0 : Fin 2))) b X := by
  rw [noExtraActive_distinctRows_iff]
  intro j _
  exact ⟨0, rfl⟩

end
end Funk
