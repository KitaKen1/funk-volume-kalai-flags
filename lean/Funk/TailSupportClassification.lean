import Funk.PositiveSupportCertificate
import Mathlib.Data.Finset.Max
import Mathlib.Order.Preorder.Finite
import Mathlib.Order.Fin.Basic

/-! Ordered upper-tail supports have only one nondegenerate contact code.
If n nonempty, proper, distinct tails of Fin(n+1) increase, their cutoffs must be n-i.
This finite classification does not identify geometric dual faces. -/

open Set

namespace Funk
noncomputable section

/-- Positivity persists at later rows. -/
def PositiveTailSupports {n : ℕ} (V : Fin (n + 1) → Space n) : Prop :=
  ∀ i k l, k ≤ l → 0 < V k i → 0 < V l i

/-- The only full-length nondegenerate support code in the original column order. -/
def TriangularPositiveCode {n : ℕ} (V : Fin (n + 1) → Space n) : Prop :=
  ∀ k i, 0 < V k i ↔ n ≤ k.val + i.val

theorem positiveSupport_nonempty_of_top {n : ℕ} (V : Fin (n + 1) → Space n)
    (htop : ∀ i, 0 < V (Fin.last n) i) (i : Fin n) : (positiveSupport V i).Nonempty :=
  ⟨Fin.last n, (mem_positiveSupport V i _).mpr (htop i)⟩

/-- A known cutoff replaces a search for arbitrary column-support subsets. -/
def positiveSupportCutoff {n : ℕ} (V : Fin (n + 1) → Space n)
    (htop : ∀ i, 0 < V (Fin.last n) i) (i : Fin n) : Fin (n + 1) :=
  (positiveSupport V i).min' (positiveSupport_nonempty_of_top V htop i)

theorem positive_at_supportCutoff {n : ℕ} (V : Fin (n + 1) → Space n)
    (htop : ∀ i, 0 < V (Fin.last n) i) (i : Fin n) :
    0 < V (positiveSupportCutoff V htop i) i :=
  (mem_positiveSupport V i _).mp (Finset.min'_mem _ _)

/-- Every upper-tail column is exactly the interval above its cutoff. -/
theorem positive_iff_supportCutoff_le {n : ℕ} (V : Fin (n + 1) → Space n)
    (htop : ∀ i, 0 < V (Fin.last n) i) (htail : PositiveTailSupports V)
    (k : Fin (n + 1)) (i : Fin n) :
    0 < V k i ↔ positiveSupportCutoff V htop i ≤ k := by
  constructor
  · intro hk
    exact Finset.min'_le _ k ((mem_positiveSupport V i k).mpr hk)
  · intro hk
    exact htail i _ k hk (positive_at_supportCutoff V htop i)

theorem supportCutoff_antitone {n : ℕ} (V : Fin (n + 1) → Space n)
    (htop : ∀ i, 0 < V (Fin.last n) i)
    (hmono : ∀ i j, i ≤ j → positiveSupport V i ⊆ positiveSupport V j) :
    Antitone (positiveSupportCutoff V htop) := by
  intro i j hij
  exact Finset.min'_le _ _ (hmono i j hij (Finset.min'_mem _ _))

/-- Distinct tails have distinct cutoffs, since the cutoff determines every membership. -/
theorem supportCutoff_injective {n : ℕ} (V : Fin (n + 1) → Space n)
    (htop : ∀ i, 0 < V (Fin.last n) i) (htail : PositiveTailSupports V)
    (hinj : Function.Injective (positiveSupport V)) :
    Function.Injective (positiveSupportCutoff V htop) := by
  intro i j hij
  apply hinj
  ext k
  simp only [mem_positiveSupport, positive_iff_supportCutoff_le V htop htail, hij]

/-- Cutoff zero is precisely the all-positive column degeneration. -/
theorem supportCutoff_eq_zero_iff {n : ℕ} (V : Fin (n + 1) → Space n)
    (htop : ∀ i, 0 < V (Fin.last n) i) (htail : PositiveTailSupports V) (i : Fin n) :
    positiveSupportCutoff V htop i = 0 ↔ ∀ k, 0 < V k i := by
  constructor
  · intro h k
    exact (positive_iff_supportCutoff_le V htop htail k i).mpr (h ▸ Fin.zero_le k)
  · intro h
    have he := (positive_iff_supportCutoff_le V htop htail 0 i).mp (h 0)
    exact le_antisymm he (Fin.zero_le _)

/-- n distinct proper tails leave no unused positive cutoff: cutoff(i)=n-i. -/
theorem supportCutoff_value_eq {n : ℕ} (V : Fin (n + 1) → Space n)
    (htop : ∀ i, 0 < V (Fin.last n) i) (htail : PositiveTailSupports V)
    (hmono : ∀ i j, i ≤ j → positiveSupport V i ⊆ positiveSupport V j)
    (hinj : Function.Injective (positiveSupport V))
    (hproper : ∀ i, ¬ ∀ k, 0 < V k i) (i : Fin n) :
    (positiveSupportCutoff V htop i).val = n - i.val := by
  have hpos (j : Fin n) : 0 < (positiveSupportCutoff V htop j).val := by
    have hne : positiveSupportCutoff V htop j ≠ 0 :=
      fun h => hproper j ((supportCutoff_eq_zero_iff V htop htail j).mp h)
    have hv : (positiveSupportCutoff V htop j).val ≠ 0 := fun h => hne (Fin.ext h)
    omega
  let f : Fin n → Fin n := fun j => ⟨(positiveSupportCutoff V htop j).val - 1, by
    have := (positiveSupportCutoff V htop j).isLt
    have := hpos j
    omega⟩
  have ha : Antitone f := by
    intro j k hjk
    have h := supportCutoff_antitone V htop hmono hjk
    change (positiveSupportCutoff V htop k).val - 1 ≤ (positiveSupportCutoff V htop j).val - 1
    exact Nat.sub_le_sub_right h 1
  have hf : Function.Injective f := by
    intro j k hjk
    apply supportCutoff_injective V htop htail hinj
    apply Fin.ext
    have h := congrArg Fin.val hjk
    change (positiveSupportCutoff V htop j).val - 1 = (positiveSupportCutoff V htop k).val - 1 at h
    have := hpos j
    have := hpos k
    omega
  have hstrict := ha.strictAnti_of_injective hf
  have hm : StrictMono (fun j => (f j).rev) := Fin.rev_strictAnti.comp hstrict
  have he : (f i).rev = i := hm.apply_eq
  have hv := congrArg Fin.val he
  simp only [Fin.val_rev] at hv
  change n - ((positiveSupportCutoff V htop i).val - 1 + 1) = i.val at hv
  have hc := (positiveSupportCutoff V htop i).isLt
  have := hpos i
  omega

/-- All nondegenerate upper-tail matrices have the same triangular support code. -/
theorem triangularPositiveCode_of_distinct_proper_tails {n : ℕ}
    (V : Fin (n + 1) → Space n) (htop : ∀ i, 0 < V (Fin.last n) i)
    (htail : PositiveTailSupports V)
    (hmono : ∀ i j, i ≤ j → positiveSupport V i ⊆ positiveSupport V j)
    (hinj : Function.Injective (positiveSupport V)) (hproper : ∀ i, ¬ ∀ k, 0 < V k i) :
    TriangularPositiveCode V := by
  intro k i
  rw [positive_iff_supportCutoff_le V htop htail]
  change (positiveSupportCutoff V htop i).val ≤ k.val ↔ _
  rw [supportCutoff_value_eq V htop htail hmono hinj hproper i]
  have := i.isLt
  omega

/-- Failure of the standard code forces one of the two proved decay conditions. -/
theorem degeneration_of_not_triangularPositiveCode {n : ℕ}
    (V : Fin (n + 1) → Space n) (htop : ∀ i, 0 < V (Fin.last n) i)
    (htail : PositiveTailSupports V)
    (hmono : ∀ i j, i ≤ j → positiveSupport V i ⊆ positiveSupport V j)
    (hcode : ¬ TriangularPositiveCode V) :
    (∃ i j : Fin n, i ≠ j ∧ positiveSupport V i = positiveSupport V j) ∨
      ∃ i : Fin n, ∀ k, 0 < V k i := by
  classical
  by_contra h
  have hpair : ¬ ∃ i j : Fin n, i ≠ j ∧ positiveSupport V i = positiveSupport V j :=
    fun hp => h (Or.inl hp)
  have hproper : ∀ i, ¬ ∀ k, 0 < V k i := fun i hi => h (Or.inr ⟨i, hi⟩)
  have hinj : Function.Injective (positiveSupport V) := by
    intro i j hij
    by_contra hne
    exact hpair ⟨i, j, hne, hij⟩
  exact hcode (triangularPositiveCode_of_distinct_proper_tails V htop htail hmono hinj hproper)

end
end Funk
