import Funk.DualLogDomain
import Funk.CoordinateSliceNull

/-! A fixed bound on one coordinate difference removes one power of the radius.
The exact volume uses ordinary product Lebesgue measure and Fubini, not an assumed estimate. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

/-- All other coordinates lie in a box; one coordinate lies in a translated fixed interval. -/
def logCoordinateBand {n : ℕ} (i : Fin (n + 1)) (j : Fin n)
    (L U a b : ℝ) : Set (Space (n + 1)) :=
  {z | (∀ k, L ≤ z (i.succAbove k) ∧ z (i.succAbove k) ≤ U) ∧
    z (i.succAbove j) + a ≤ z i ∧ z i ≤ z (i.succAbove j) + b}

theorem isClosed_logCoordinateBand {n : ℕ} (i : Fin (n + 1)) (j : Fin n)
    (L U a b : ℝ) : IsClosed (logCoordinateBand i j L U a b) := by
  have he : logCoordinateBand i j L U a b =
      (⋂ k, {z : Space (n + 1) | L ≤ z (i.succAbove k) ∧ z (i.succAbove k) ≤ U}) ∩
      {z | z (i.succAbove j) + a ≤ z i} ∩ {z | z i ≤ z (i.succAbove j) + b} := by
    ext z
    simp only [logCoordinateBand, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    tauto
  rw [he]
  exact ((isClosed_iInter fun k =>
    (isClosed_le continuous_const (continuous_apply _)).inter
      (isClosed_le (continuous_apply _) continuous_const)).inter
    (isClosed_le ((continuous_apply _).add continuous_const) (continuous_apply _))).inter
    (isClosed_le (continuous_apply _) ((continuous_apply _).add continuous_const))

theorem logCoordinateBand_section {n : ℕ} (i : Fin (n + 1)) (j : Fin n)
    (L U a b : ℝ) (t : Space n) :
    {u : ℝ | i.insertNth u t ∈ logCoordinateBand i j L U a b} =
      if t ∈ Icc (fun _ => L) (fun _ => U) then Icc (t j + a) (t j + b) else ∅ := by
  by_cases ht : t ∈ Icc (fun _ => L) (fun _ => U)
  · ext u
    simp only [logCoordinateBand, Set.mem_ofPred_eq, Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove, ht, ite_true, Set.mem_Icc]
    have hb : ∀ k, L ≤ t k ∧ t k ≤ U := fun k => ⟨ht.1 k, ht.2 k⟩
    simp [hb]
  · ext u
    simp only [logCoordinateBand, Set.mem_ofPred_eq, Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove, ht, ite_false, Set.mem_empty_iff_false, iff_false]
    intro h
    exact ht ⟨fun k => (h.1 k).1, fun k => (h.1 k).2⟩

/-- The moving center does not change the section length; the other n lengths multiply. -/
theorem volume_logCoordinateBand {n : ℕ} (i : Fin (n + 1)) (j : Fin n)
    (L U a b : ℝ) :
    volume (logCoordinateBand i j L U a b) =
      ENNReal.ofReal (b - a) * ENNReal.ofReal (U - L) ^ n := by
  classical
  let e : (ℝ × Space n) ≃ᵐ Space (n + 1) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm
  have hp : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm _
  have hs := (isClosed_logCoordinateBand i j L U a b).measurableSet
  rw [← hp.map_eq, Measure.map_apply e.measurable hs, Measure.volume_eq_prod,
    Measure.prod_apply_symm (hs.preimage e.measurable)]
  have hf : (fun t : Space n => volume {u : ℝ | e (u, t) ∈ logCoordinateBand i j L U a b}) =
      (Icc (fun _ => L) (fun _ => U)).indicator (fun _ => ENNReal.ofReal (b - a)) := by
    funext t
    have he : {u : ℝ | e (u, t) ∈ logCoordinateBand i j L U a b} =
        {u : ℝ | i.insertNth u t ∈ logCoordinateBand i j L U a b} := by
      ext u
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    rw [he, logCoordinateBand_section]
    by_cases ht : t ∈ Icc (fun _ => L) (fun _ => U)
    · simp [ht, Real.volume_Icc]
    · simp [ht]
  change (∫⁻ t : Space n, volume {u : ℝ | e (u, t) ∈ logCoordinateBand i j L U a b}) = _
  rw [hf, lintegral_indicator_const measurableSet_Icc, Real.volume_Icc_pi]
  simp

end
end Funk
