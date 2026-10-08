import Funk.DistinctRows
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset

/-! A finite minimal subfamily removes all signed convex redundancy.
Minimality is classical and exact; no numerical hull-membership oracle is
implemented. Geometric simplicity of the remaining constraints is separate. -/

open Set

namespace Funk
noncomputable section

def rowSubfamily {n : ℕ} {ι : Type*} (rows : ι → Space n) (s : Finset ι) :
    s → Space n := fun j => rows j.val

theorem signedRowHull_mono_of_range_subset {n : ℕ} {ι κ : Type*}
    (rows : ι → Space n) (other : κ → Space n) (h : range rows ⊆ range other) :
    signedRowHull rows ⊆ signedRowHull other := by
  apply convexHull_min _ (convex_convexHull ℝ _)
  rintro r (⟨j, rfl⟩ | ⟨j, rfl⟩)
  · obtain ⟨k, hk⟩ := h (mem_range_self j)
    rw [← hk]
    exact row_mem_signedRowHull other k
  · obtain ⟨k, hk⟩ := h (mem_range_self j)
    change -rows j ∈ signedRowHull other
    rw [← hk]
    exact neg_mem_signedRowHull other (row_mem_signedRowHull other k)

theorem signedRowHull_rowSubfamily_mono {n : ℕ} {ι : Type*}
    (rows : ι → Space n) {s t : Finset ι} (h : s ⊆ t) :
    signedRowHull (rowSubfamily rows s) ⊆ signedRowHull (rowSubfamily rows t) := by
  apply signedRowHull_mono_of_range_subset
  rintro _ ⟨j, rfl⟩
  exact ⟨⟨j.val, h j.property⟩, rfl⟩

/-- Removing a certified redundant row preserves the entire signed convex hull. -/
theorem signedRowHull_erase_eq {n : ℕ} {ι : Type*} [DecidableEq ι]
    (rows : ι → Space n) (s : Finset ι) (j : ι)
    (hj : rows j ∈ signedRowHull (rowSubfamily rows (s.erase j))) :
    signedRowHull (rowSubfamily rows (s.erase j)) = signedRowHull (rowSubfamily rows s) := by
  apply signedRowHull_eq_of_mutual_mem
  · intro k
    exact row_mem_signedRowHull (rowSubfamily rows s)
      ⟨k.val, Finset.mem_of_mem_erase k.property⟩
  · intro k
    by_cases he : k.val = j
    · simpa only [rowSubfamily, he] using hj
    · exact row_mem_signedRowHull (rowSubfamily rows (s.erase j))
        ⟨k.val, Finset.mem_erase.mpr ⟨he, k.property⟩⟩

/-- A smallest hull-preserving subset has no individually removable signed
convex-redundant row. It may have many more than n rows. -/
theorem exists_minimal_rowSubfamily {n : ℕ} {ι : Type*} [DecidableEq ι]
    (rows : ι → Space n) (s : Finset ι) :
    ∃ t ⊆ s, signedRowHull (rowSubfamily rows t) = signedRowHull (rowSubfamily rows s) ∧
      ∀ j ∈ t, rows j ∉ signedRowHull (rowSubfamily rows (t.erase j)) := by
  classical
  let candidates := s.powerset.filter (fun t =>
    signedRowHull (rowSubfamily rows t) = signedRowHull (rowSubfamily rows s))
  have hc : s ∈ candidates := by simp [candidates]
  obtain ⟨t, ht, hmin⟩ := candidates.exists_min_image Finset.card ⟨s, hc⟩
  have ht' := Finset.mem_filter.mp ht
  refine ⟨t, Finset.mem_powerset.mp ht'.1, ht'.2, ?_⟩
  intro j hj hred
  have he := signedRowHull_erase_eq rows t j hred
  have herase : t.erase j ∈ candidates := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powerset.mpr
      (by intro x hx; exact (Finset.mem_powerset.mp ht'.1) (Finset.mem_of_mem_erase hx)), he.trans ht'.2⟩
  exact (not_le_of_gt (Finset.card_erase_lt_of_mem hj)) (hmin _ herase)

theorem signedRowHull_rowSubfamily_univ {n : ℕ} {ι : Type*} [Fintype ι]
    (rows : ι → Space n) :
    signedRowHull (rowSubfamily rows Finset.univ) = signedRowHull rows := by
  apply signedRowHull_eq_of_range_eq
  ext r
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j.val, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨⟨j, Finset.mem_univ j⟩, rfl⟩

/-- The retained labels are enumerated in their original increasing order. -/
theorem signedRowHull_ordered_subfamily {n : ℕ} {ι : Type*} [LinearOrder ι]
    (rows : ι → Space n) (s : Finset ι) :
    signedRowHull (fun i => rows (s.orderEmbOfFin rfl i)) =
      signedRowHull (rowSubfamily rows s) := by
  apply signedRowHull_eq_of_range_eq
  ext r
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨s.orderIsoOfFin rfl i, rfl⟩
  · rintro ⟨j, rfl⟩
    refine ⟨(s.orderIsoOfFin rfl).symm j, ?_⟩
    change rows ((s.orderIsoOfFin rfl ((s.orderIsoOfFin rfl).symm j)).val) = rows j.val
    rw [OrderIso.apply_symm_apply]

end
end Funk
