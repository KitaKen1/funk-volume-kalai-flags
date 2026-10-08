import Funk.GeometricSeparation
import Mathlib.Order.Hom.Set

/-! Canonical increasing basis indices separate genuine geometric collisions
from permutations. With strict heights, two distinct canonical signed bases at
one witness force an additional active row. No nullity of that locus is assumed. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

theorem lensBranchPoint_sign_injective {τ t : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (ht : t ∈ Ioo (-1) 1) :
    Function.Injective (fun b => lensBranchPoint τ b t) := by
  have hp := lensProfile_pos hτ0 hτ1 ht
  have hm := lensProfile_pos hτ0 hτ1
    (show -t ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  intro b c he
  have hq := congr_arg (lensChordCoordinate τ) he
  cases b <;> cases c
  · rfl
  · change lensChordCoordinate τ (lensLeftPoint τ t) =
      lensChordCoordinate τ (lensRightPoint τ t) at hq
    rw [lensLeftPoint_chord, lensRightPoint_chord] at hq
    linarith
  · change lensChordCoordinate τ (lensRightPoint τ t) =
      lensChordCoordinate τ (lensLeftPoint τ t) at hq
    rw [lensLeftPoint_chord, lensRightPoint_chord] at hq
    linarith
  · rfl

theorem basisRealWitness_sign_injective {n : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.det ≠ 0) {X : Space n}
    (hX : ∀ i, |dotProduct (B i) X| < 1) :
    Function.Injective (fun b => basisRealWitness τ b B X) := by
  intro b c he
  funext i
  apply lensBranchPoint_sign_injective hτ0 hτ1 (abs_lt.mp (hX i))
  have hb := complexRow_realWitness hτ0 hτ1 b hB (fun j => (hX j).le) i
  have hc := complexRow_realWitness hτ0 hτ1 c hB (fun j => (hX j).le) i
  exact hb.symm.trans ((congr_arg (fun Y => complexRow (B i) Y X) he).trans hc)

/-- Sorting removes permutations: equal-sized increasing selections cannot be
properly nested. The codomain need not be finite. -/
theorem increasing_selection_eq_of_range_subset {n : ℕ} {ι : Type*} [LinearOrder ι]
    {s t : Fin n → ι} (hs : StrictMono s) (ht : StrictMono t)
    (hsub : range t ⊆ range s) : s = t := by
  have hex (i : Fin n) : ∃ j, s j = t i := hsub (mem_range_self i)
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro i j hij
    apply ht.injective
    rw [← hf i, ← hf j, hij]
  have hsurj := Finite.surjective_of_injective hinj
  apply hs.eq_of_range_eq ht
  apply Subset.antisymm _ hsub
  rintro _ ⟨i, rfl⟩
  obtain ⟨j, hj⟩ := hsurj i
  exact ⟨j, by rw [← hf j, hj]⟩

/-- Every active row is selected. This geometric simplicity condition is an
explicit hypothesis, not a theorem about arbitrary input polytopes. -/
def NoExtraActive {n : ℕ} {ι : Type*} (τ : ℝ) (rows : ι → Space n)
    (s : Fin n → ι) (b : Fin n → Bool) (X : Space n) : Prop :=
  ∀ j, complexRow (rows j) (basisRealWitness τ b (fun i => rows (s i)) X) X ∈
    frontier (lensGraphBody τ) → j ∈ range s

theorem selected_row_active {n : ℕ} {ι : Type*} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : ι → Space n)
    (s : Fin n → ι) (b : Fin n → Bool)
    (hB : Matrix.det (fun i => rows (s i)) ≠ 0) {X : Space n}
    (hS : X ∈ basisFeasibleRegion τ rows s b) (i : Fin n) :
    complexRow (rows (s i)) (basisRealWitness τ b (fun j => rows (s j)) X) X ∈
      frontier (lensGraphBody τ) := by
  rw [complexRow_realWitness hτ0 hτ1 b hB (fun j => hS.1 (s j)) i]
  exact lensBranchPoint_mem_frontier hτ0 hτ1 (b i)

theorem canonical_basis_eq_of_witness_eq {n : ℕ} {ι : Type*} [LinearOrder ι]
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : ι → Space n)
    (s t : Fin n → ι) (b c : Fin n → Bool)
    (hs : StrictMono s) (ht : StrictMono t)
    (hB : Matrix.det (fun i => rows (s i)) ≠ 0)
    (hC : Matrix.det (fun i => rows (t i)) ≠ 0) {X : Space n}
    (hT : X ∈ basisFeasibleRegion τ rows t c)
    (hX : ∀ j, |dotProduct (rows j) X| < 1)
    (hactive : NoExtraActive τ rows s b X)
    (he : basisRealWitness τ b (fun i => rows (s i)) X =
      basisRealWitness τ c (fun i => rows (t i)) X) : s = t ∧ b = c := by
  have hsub : range t ⊆ range s := by
    rintro _ ⟨i, rfl⟩
    apply hactive
    rw [he]
    exact selected_row_active hτ0 hτ1 rows t c hC hT i
  have hst := increasing_selection_eq_of_range_subset hs ht hsub
  refine ⟨hst, ?_⟩
  subst t
  exact basisRealWitness_sign_injective hτ0 hτ1 hB (fun i => hX (s i)) he

/-- Any remaining collision produces an explicit additional active constraint. -/
theorem canonical_collision_has_extra_active {n : ℕ} {ι : Type*} [LinearOrder ι]
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : ι → Space n)
    (s t : Fin n → ι) (b c : Fin n → Bool)
    (hs : StrictMono s) (ht : StrictMono t)
    (hB : Matrix.det (fun i => rows (s i)) ≠ 0)
    (hC : Matrix.det (fun i => rows (t i)) ≠ 0) {X : Space n}
    (hT : X ∈ basisFeasibleRegion τ rows t c)
    (hX : ∀ j, |dotProduct (rows j) X| < 1) (hne : s ≠ t ∨ b ≠ c)
    (he : basisRealWitness τ b (fun i => rows (s i)) X =
      basisRealWitness τ c (fun i => rows (t i)) X) :
    ∃ j, j ∉ range s ∧ complexRow (rows j)
      (basisRealWitness τ b (fun i => rows (s i)) X) X ∈ frontier (lensGraphBody τ) := by
  classical
  by_contra h
  have hactive : NoExtraActive τ rows s b X := by
    intro j hj
    by_contra hn
    exact h ⟨j, hn, hj⟩
  have hc := canonical_basis_eq_of_witness_eq hτ0 hτ1 rows s t b c hs ht hB hC hT hX hactive he
  exact hne.elim (fun h => h hc.1) (fun h => h hc.2)

/-- Repeated rows obstruct simplicity everywhere they are selected. They cannot
be discarded as a null exceptional locus without a preprocessing argument. -/
theorem noExtraActive_false_of_duplicate {n : ℕ} {ι : Type*} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : ι → Space n)
    (s : Fin n → ι) (b : Fin n → Bool)
    (hB : Matrix.det (fun i => rows (s i)) ≠ 0) {X : Space n}
    (hS : X ∈ basisFeasibleRegion τ rows s b) (i : Fin n) (j : ι)
    (hj : j ∉ range s) (hrow : rows j = rows (s i)) :
    ¬NoExtraActive τ rows s b X := by
  intro ha
  apply hj
  apply ha
  rw [hrow]
  exact selected_row_active hτ0 hτ1 rows s b hB hS i

/-- Two identical constraints describe the same interval, but distinct row labels. -/
def duplicateIntervalRows : Fin 2 → Space 1 := fun _ _ => 1

theorem duplicateInterval_feasible {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {X : Space 1} (hX : |X 0| ≤ 1) :
    X ∈ basisFeasibleRegion τ duplicateIntervalRows (fun _ => 0) (fun _ => true) := by
  have hb : X ∈ stripBody (fun _ : Fin 1 => duplicateIntervalRows 0) := by
    intro i
    simpa [duplicateIntervalRows, dotProduct] using hX
  have hdet : Matrix.det (fun _ : Fin 1 => duplicateIntervalRows 0) ≠ 0 := by
    exact (by norm_num : Matrix.det (!![(1 : ℝ)]) ≠ 0)
  refine ⟨?_, ?_⟩
  · intro j
    simpa [duplicateIntervalRows, dotProduct] using hX
  · intro j
    change complexRow (duplicateIntervalRows 0)
      (basisRealWitness τ (fun _ => true) (fun _ => duplicateIntervalRows 0) X) X ∈ _
    rw [complexRow_realWitness hτ0 hτ1 (fun _ => true) hdet hb 0]
    exact lensCircleImage_subset_graphBody hτ0 hτ1 (lensRightPoint_mem_circleImage τ _)

/-- A whole interval of parameters violates the naive no-extra-active assertion. -/
theorem duplicateInterval_not_noExtraActive {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {X : Space 1} (hX : |X 0| ≤ 1) :
    ¬NoExtraActive τ duplicateIntervalRows (fun _ => 0) (fun _ => true) X := by
  apply noExtraActive_false_of_duplicate hτ0 hτ1 duplicateIntervalRows
    (fun _ => 0) (fun _ => true) (by
      exact (by norm_num : Matrix.det (!![(1 : ℝ)]) ≠ 0))
    (duplicateInterval_feasible hτ0 hτ1 hX) 0 1
  · simp
  · rfl

end
end Funk
