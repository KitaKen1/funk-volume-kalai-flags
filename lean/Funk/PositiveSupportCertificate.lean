import Funk.LogOrderCertificate
import Mathlib.Data.Fin.Tuple.Sort

/-! Positive scaling is equivalent to nested positive supports, for a finite nonnegative matrix.
The sorting permutation and a geometric sequence of scales are proved to exist over the reals;
no numerical candidate or assumed scaling certificate is used. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

/-- A column's positive entries, over any finite vertex family. -/
def positiveSupport {κ : Type*} [Fintype κ] {n : ℕ}
    (V : κ → Space n) (i : Fin n) : Finset κ := by
  classical
  exact Finset.univ.filter (fun k => 0 < V k i)

/-- Finite row inequalities after a coordinate permutation. -/
def VertexOrderCertificate {κ : Type*} {n : ℕ} (V : κ → Space n)
    (σ : Equiv.Perm (Fin n)) (a : Space n) : Prop :=
  ∀ k i j, i ≤ j → a j * V k (σ j) ≤ a i * V k (σ i)

/-- A nested support chain in the proposed column order. -/
def NestedPositiveSupports {κ : Type*} [Fintype κ] {n : ℕ}
    (V : κ → Space n) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j, i ≤ j → positiveSupport V (σ j) ⊆ positiveSupport V (σ i)

/-- Pairwise comparable supports admit a single ordering. -/
def ComparablePositiveSupports {κ : Type*} [Fintype κ] {n : ℕ}
    (V : κ → Space n) : Prop :=
  ∀ i j, positiveSupport V i ⊆ positiveSupport V j ∨
    positiveSupport V j ⊆ positiveSupport V i

@[simp]
theorem mem_positiveSupport {κ : Type*} [Fintype κ] {n : ℕ}
    (V : κ → Space n) (i : Fin n) (k : κ) :
    k ∈ positiveSupport V i ↔ 0 < V k i := by
  classical
  simp [positiveSupport]

/-- A finite collection of strictly positive numbers has a positive floor, also at most one. -/
theorem finite_positive_floor {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ s, 0 < f x) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ x ∈ s, ε ≤ f x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, le_rfl, by simp⟩
  | @insert x s hx ih =>
    obtain ⟨ε, hε, hε1, hfloor⟩ := ih (fun y hy => hf y (Finset.mem_insert_of_mem hy))
    refine ⟨min ε (f x), lt_min hε (hf x (Finset.mem_insert_self _ _)),
      (min_le_left _ _).trans hε1, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hfloor y hy)

/-- One small ratio controls every positive comparison of finitely many entries. -/
theorem exists_positive_comparison_ratio {κ : Type*} [Fintype κ] {n : ℕ}
    (V : κ → Space n) (hV : ∀ k i, 0 ≤ V k i) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ k i j, 0 < V k i → ε * V k j ≤ V k i := by
  classical
  let f : κ × Fin n × Fin n → ℝ := fun p =>
    if 0 < V p.1 p.2.1 then V p.1 p.2.1 / (V p.1 p.2.2 + 1) else 1
  have hf : ∀ p, 0 < f p := by
    intro p
    dsimp [f]
    split_ifs with h
    · exact div_pos h (by linarith [hV p.1 p.2.2])
    · exact zero_lt_one
  obtain ⟨ε, hε, hε1, hfloor⟩ := finite_positive_floor Finset.univ f (fun p _ => hf p)
  refine ⟨ε, hε, hε1, ?_⟩
  intro k i j hi
  have h := hfloor (k, i, j) (Finset.mem_univ _)
  simp only [f, hi, ite_true] at h
  have hd : 0 < V k j + 1 := by linarith [hV k j]
  have hm := (le_div_iff₀ hd).mp h
  nlinarith

/-- A geometric sequence of scales certifies every row when supports are nested. -/
theorem vertexOrderCertificate_geometric {κ : Type*} [Fintype κ] {n : ℕ}
    (V : κ → Space n) (hV : ∀ k i, 0 ≤ V k i) (σ : Equiv.Perm (Fin n))
    (hs : NestedPositiveSupports V σ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hr : ∀ k i j, 0 < V k i → ε * V k j ≤ V k i) :
    VertexOrderCertificate V σ (fun i => ε ^ i.val) := by
  intro k i j hij
  rcases lt_or_eq_of_le hij with hij | rfl
  · by_cases hj : 0 < V k (σ j)
    · have hi : 0 < V k (σ i) :=
        (mem_positiveSupport V (σ i) k).mp (hs i j hij.le ((mem_positiveSupport V (σ j) k).mpr hj))
      have hp : ε ^ j.val ≤ ε ^ (i.val + 1) :=
        pow_le_pow_of_le_one hε.le hε1 (Nat.succ_le_iff.mpr hij)
      calc
        ε ^ j.val * V k (σ j) ≤ ε ^ (i.val + 1) * V k (σ j) :=
          mul_le_mul_of_nonneg_right hp (hV k (σ j))
        _ = ε ^ i.val * (ε * V k (σ j)) := by rw [pow_succ]; ring
        _ ≤ ε ^ i.val * V k (σ i) :=
          mul_le_mul_of_nonneg_left (hr k (σ i) (σ j) hi) (pow_nonneg hε.le _)
    · have hz : V k (σ j) = 0 := le_antisymm (le_of_not_gt hj) (hV k (σ j))
      rw [hz, mul_zero]
      exact mul_nonneg (pow_nonneg hε.le _) (hV k (σ i))
  · exact le_rfl

/-- Existence, rather than a supplied certificate, for any prescribed nested ordering. -/
theorem exists_vertexOrderCertificate_of_nested {κ : Type*} [Fintype κ] {n : ℕ}
    (V : κ → Space n) (hV : ∀ k i, 0 ≤ V k i) (σ : Equiv.Perm (Fin n))
    (hs : NestedPositiveSupports V σ) :
    ∃ a : Space n, (∀ i, 0 < a i) ∧ VertexOrderCertificate V σ a := by
  obtain ⟨ε, hε, hε1, hr⟩ := exists_positive_comparison_ratio V hV
  exact ⟨fun i => ε ^ i.val, fun i => pow_pos hε _,
    vertexOrderCertificate_geometric V hV σ hs hε hε1 hr⟩

/-- Any positive scaling certificate forces the same support inclusion. -/
theorem nestedPositiveSupports_of_certificate {κ : Type*} [Fintype κ] {n : ℕ}
    (V : κ → Space n) (σ : Equiv.Perm (Fin n)) (a : Space n)
    (ha : ∀ i, 0 < a i) (hc : VertexOrderCertificate V σ a) :
    NestedPositiveSupports V σ := by
  intro i j hij k hk
  have hj : 0 < V k (σ j) := (mem_positiveSupport _ _ _).mp hk
  have hprod : 0 < a i * V k (σ i) := (mul_pos (ha j) hj).trans_le (hc k i j hij)
  apply (mem_positiveSupport _ _ _).mpr
  exact (mul_pos_iff_of_pos_left (ha i)).mp hprod

/-- Exact fixed-permutation criterion, valid also for empty row/column families. -/
theorem exists_vertexOrderCertificate_iff_nested {κ : Type*} [Fintype κ] {n : ℕ}
    (V : κ → Space n) (hV : ∀ k i, 0 ≤ V k i) (σ : Equiv.Perm (Fin n)) :
    (∃ a : Space n, (∀ i, 0 < a i) ∧ VertexOrderCertificate V σ a) ↔
      NestedPositiveSupports V σ := by
  constructor
  · rintro ⟨a, ha, hc⟩
    exact nestedPositiveSupports_of_certificate V σ a ha hc
  · exact exists_vertexOrderCertificate_of_nested V hV σ

/-- Sorting support cardinalities in decreasing order supplies an actual permutation. -/
theorem nestedPositiveSupports_sort {κ : Type*} [Fintype κ] {n : ℕ}
    (V : κ → Space n) (hc : ComparablePositiveSupports V) :
    NestedPositiveSupports V (Tuple.sort (fun i =>
      OrderDual.toDual (positiveSupport V i).card)) := by
  classical
  let σ := Tuple.sort (fun i => OrderDual.toDual (positiveSupport V i).card)
  have hs : Antitone (fun i => (positiveSupport V (σ i)).card) :=
    Tuple.monotone_sort (fun i => OrderDual.toDual (positiveSupport V i).card)
  intro i j hij
  rcases hc (σ i) (σ j) with h | h
  · have he := Finset.eq_of_subset_of_card_le h (hs hij)
    exact he.symm ▸ Finset.Subset.refl _
  · exact h

/-- The candidate generator's combinatorial criterion is a proved real existence theorem. -/
theorem exists_orderCertificate_of_comparable {κ : Type*} [Fintype κ] {n : ℕ}
    (V : κ → Space n) (hV : ∀ k i, 0 ≤ V k i) (hc : ComparablePositiveSupports V) :
    ∃ σ : Equiv.Perm (Fin n), ∃ a : Space n,
      (∀ i, 0 < a i) ∧ VertexOrderCertificate V σ a := by
  exact ⟨_, exists_vertexOrderCertificate_of_nested V hV _ (nestedPositiveSupports_sort V hc)⟩

end
end Funk
