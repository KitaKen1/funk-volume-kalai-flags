import Funk.IrredundantRows

/-! An increasing row reduction lifts canonical signed bases injectively into
the old canonical family, preserving each matched event. The total mass can
only decrease under deletion; an old covering bound cannot be transferred in
the reverse direction from this inequality alone. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

def liftRowChoice {n k m : ℕ} (selected : Fin k ↪o Fin m)
    (c : SignedRowChoice n k) : SignedRowChoice n m := (selected ∘ c.1, c.2)

theorem liftRowChoice_injective {n k m : ℕ} (selected : Fin k ↪o Fin m) :
    Function.Injective (liftRowChoice (n := n) selected) := by
  intro c d h
  apply Prod.ext
  · funext i
    exact selected.injective (congr_fun (congr_arg Prod.fst h) i)
  · exact congr_arg (fun x : SignedRowChoice n m => x.2) h

theorem liftRowChoice_mem_canonical {n k m : ℕ} (rows : Fin m → Space n)
    (selected : Fin k ↪o Fin m) (c : SignedRowChoice n k)
    (hc : c ∈ canonicalBasisIndices (fun i => rows (selected i))) :
    liftRowChoice selected c ∈ canonicalBasisIndices rows := by
  have hc' := (mem_canonicalBasisIndices (fun i => rows (selected i)) c).mp hc
  apply (mem_canonicalBasisIndices rows (liftRowChoice selected c)).mpr
  exact ⟨selected.strictMono.comp hc'.1, hc'.2⟩

theorem basisBoundaryEvent_liftRowChoice {n k m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n)
    (selected : Fin k ↪o Fin m)
    (hh : signedRowHull (fun i => rows (selected i)) = signedRowHull rows)
    (c : SignedRowChoice n k) :
    basisBoundaryEvent τ c.2 (fun i => rows (selected (c.1 i)))
      (basisFeasibleRegion τ (fun i => rows (selected i)) c.1 c.2) =
    basisBoundaryEvent τ (liftRowChoice selected c).2
      (fun i => rows ((liftRowChoice selected c).1 i))
      (basisFeasibleRegion τ rows (liftRowChoice selected c).1 (liftRowChoice selected c).2) := by
  apply basisBoundaryEvent_eq_of_signedRowHull_eq hτ0 hτ1 _ _ hh
  exact fun _ => rfl

/-- The direction matters: reduced covering implies old covering, but not
conversely. No equality of the sums over all labeled bases is asserted. -/
theorem canonical_probability_sum_reduction_le {n k m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n)
    (selected : Fin k ↪o Fin m)
    (hh : signedRowHull (fun i => rows (selected i)) = signedRowHull rows) :
    (∑ c ∈ canonicalBasisIndices (fun i => rows (selected i)), lensBoundaryRows n τ
      (basisBoundaryEvent τ c.2 (fun i => rows (selected (c.1 i)))
        (basisFeasibleRegion τ (fun i => rows (selected i)) c.1 c.2))) ≤
    ∑ c ∈ canonicalBasisIndices rows, lensBoundaryRows n τ
      (basisBoundaryEvent τ c.2 (fun i => rows (c.1 i))
        (basisFeasibleRegion τ rows c.1 c.2)) := by
  classical
  apply Finset.sum_le_sum_of_injOn (liftRowChoice selected)
    (liftRowChoice_injective selected).injOn
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
    exact liftRowChoice_mem_canonical rows selected d hd
  · intro c _
    exact (congr_arg (lensBoundaryRows n τ)
      (basisBoundaryEvent_liftRowChoice hτ0 hτ1 rows selected hh c)).le
  · intro c _ _
    exact bot_le

end
end Funk
