import Funk.SimplexVolume
import Funk.LogCoordinates

/-! The ordinary Lebesgue volume of an ordered coordinate simplex is r^n/n!.
This supplies the second factorial for sharp reciprocal-product upper bounds.
No flag-pair containment is assumed or proved here. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

def orderedLogSimplex (n : ℕ) (r : ℝ) : Set (Space n) :=
  {z | (∀ i, 0 ≤ z i) ∧ (∀ i, z i ≤ r) ∧ Antitone z}

theorem isClosed_orderedLogSimplex (n : ℕ) (r : ℝ) :
    IsClosed (orderedLogSimplex n r) := by
  have he : orderedLogSimplex n r =
      (⋂ i, {z : Space n | 0 ≤ z i}) ∩
      (⋂ i, {z : Space n | z i ≤ r}) ∩
      (⋂ i, ⋂ j, {z : Space n | i ≤ j → z j ≤ z i}) := by
    ext z
    simp only [orderedLogSimplex, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨h0, hr, ha⟩
      exact ⟨⟨h0, hr⟩, fun i j hij => ha hij⟩
    · rintro ⟨⟨h0, hr⟩, ha⟩
      exact ⟨h0, hr, fun i j hij => ha i j hij⟩
  rw [he]
  refine ((isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_iInter fun i => isClosed_le (continuous_apply i) continuous_const)).inter ?_
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  by_cases h : i ≤ j
  · simpa [h] using isClosed_le (continuous_apply j) (continuous_apply i)
  · simp [h]

theorem orderedLogSimplex_subset_box (n : ℕ) (r : ℝ) :
    orderedLogSimplex n r ⊆ Set.Icc (0 : Space n) (fun _ => r) :=
  fun _ hz => ⟨hz.1, hz.2.1⟩

theorem orderedLogSimplex_section (n : ℕ) (r t : ℝ) :
    {y : Space n | Fin.cons t y ∈ orderedLogSimplex (n + 1) r} =
      if t ∈ Icc 0 r then orderedLogSimplex n t else ∅ := by
  split_ifs with ht
  · ext y
    constructor
    · intro hy
      refine ⟨fun i => hy.1 i.succ, ?_, ?_⟩
      · intro i
        exact hy.2.2 (Fin.zero_le i.succ)
      · intro i j hij
        exact hy.2.2 (Fin.succ_le_succ_iff.mpr hij)
    · rintro ⟨hn, hb, ha⟩
      refine ⟨?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ht.1 (fun j => hn j) i
      · intro i
        refine Fin.cases ht.2 (fun j => (hb j).trans ht.2) i
      · intro i j hij
        cases i using Fin.cases with
        | zero =>
          cases j using Fin.cases with
          | zero => exact le_rfl
          | succ j' => exact hb j'
        | succ i' =>
          cases j using Fin.cases with
          | zero => exact False.elim (by simp at hij)
          | succ j' => exact ha (Fin.succ_le_succ_iff.mp hij)
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact ht ⟨hy.1 0, hy.2.1 0⟩

theorem volume_orderedLogSimplex_succ (n : ℕ) (r : ℝ) :
    volume (orderedLogSimplex (n + 1) r) =
      ∫⁻ t in Icc 0 r, volume (orderedLogSimplex n t) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
  have hm := (isClosed_orderedLogSimplex (n + 1) r).measurableSet
  rw [← hp.measure_preimage hm.nullMeasurableSet]
  change (volume.prod volume) (e ⁻¹' orderedLogSimplex (n + 1) r) = _
  rw [Measure.prod_apply (hm.preimage e.measurable)]
  have he : ∀ t : ℝ, (Prod.mk t ⁻¹' (e ⁻¹' orderedLogSimplex (n + 1) r)) =
      if t ∈ Icc 0 r then orderedLogSimplex n t else ∅ := by
    intro t
    convert orderedLogSimplex_section n r t using 1
    ext y
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  simp_rw [he]
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro t
  by_cases ht : t ∈ Icc 0 r <;> simp [ht]

theorem ordered_simplex_slice_integral (r : ℝ) (n : ℕ) :
    (∫ t in (0 : ℝ)..r, t ^ n / (n.factorial : ℝ)) =
      r ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  rw [intervalIntegral.integral_div, integral_pow]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    zero_pow (Nat.succ_ne_zero n), sub_zero]
  rw [div_div]

theorem volume_orderedLogSimplex (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    volume (orderedLogSimplex n r) = ENNReal.ofReal (r ^ n / (n.factorial : ℝ)) := by
  induction n generalizing r with
  | zero =>
    have hs : orderedLogSimplex 0 r = Set.univ := by
      ext z
      simp [orderedLogSimplex, Antitone]
    rw [hs, Measure.volume_pi_eq_dirac]
    simp
  | succ n ih =>
    rw [volume_orderedLogSimplex_succ]
    have he : (∫⁻ t in Icc 0 r, volume (orderedLogSimplex n t)) =
        ∫⁻ t in Icc 0 r, ENNReal.ofReal (t ^ n / (n.factorial : ℝ)) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t ht
      exact ih ht.1
    rw [he]
    have hi : IntegrableOn (fun t : ℝ => t ^ n / (n.factorial : ℝ)) (Icc 0 r) :=
      (by fun_prop : Continuous (fun t : ℝ => t ^ n / (n.factorial : ℝ))).integrableOn_Icc
    have hn : 0 ≤ᵐ[volume.restrict (Icc 0 r)]
        (fun t : ℝ => t ^ n / (n.factorial : ℝ)) := by
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t ht
      exact div_nonneg (pow_nonneg ht.1 _) (Nat.cast_nonneg _)
    rw [← ofReal_integral_eq_lintegral_ofReal hi hn, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hr, ordered_simplex_slice_integral]

/-- The reciprocal kernel contributes one factorial; ordering supplies the other. -/
theorem lintegral_exp_orderedLogSimplex (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (∫⁻ u in expCoordinates '' orderedLogSimplex n r, dualProductKernel u) =
      ENNReal.ofReal (r ^ n / (n.factorial : ℝ) ^ 2) := by
  rw [lintegral_expCoordinates_kernel (isClosed_orderedLogSimplex n r).measurableSet,
    volume_orderedLogSimplex n hr, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end
end Funk
