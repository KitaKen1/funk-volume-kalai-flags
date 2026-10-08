import Funk.VertexDeterminant
import Funk.IntervalNormalization
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Convex.Combination

/-! Lebesgue measure of solid coordinate simplices. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk

noncomputable section

/-- The solid simplex; unlike `stdSimplex`, the coordinate sum is an inequality. -/
def solidSimplex (n : ℕ) (r : ℝ) : Set (Space n) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ r}

theorem isClosed_solidSimplex (n : ℕ) (r : ℝ) : IsClosed (solidSimplex n r) := by
  have heq : solidSimplex n r =
      (⋂ i, {x : Space n | 0 ≤ x i}) ∩ {x | ∑ i, x i ≤ r} := by
    ext x
    simp [solidSimplex]
  rw [heq]
  exact (isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))).inter
    (isClosed_le (by fun_prop) continuous_const)

theorem solidSimplex_eq_empty {n : ℕ} {r : ℝ} (hr : r < 0) :
    solidSimplex n r = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hs : 0 ≤ ∑ i, x i := Finset.sum_nonneg (fun i _ => hx.1 i)
  linarith [hx.2]

theorem solidSimplex_section (n : ℕ) (r t : ℝ) :
    {y : Space n | Fin.cons t y ∈ solidSimplex (n + 1) r} =
      if t ∈ Icc 0 r then solidSimplex n (r - t) else ∅ := by
  split_ifs with ht
  · ext y
    simp only [Set.mem_ofPred_eq, solidSimplex, Fin.forall_fin_succ,
      Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_succ]
    constructor
    · rintro ⟨⟨_, hy⟩, hs⟩
      exact ⟨hy, by linarith⟩
    · rintro ⟨hy, hs⟩
      exact ⟨⟨ht.1, hy⟩, by linarith⟩
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hnonneg : ∀ i, 0 ≤ y i := fun i => hy.1 i.succ
    have hsum : 0 ≤ ∑ i, y i := Finset.sum_nonneg (fun i _ => hnonneg i)
    have hzero : 0 ≤ t := hy.1 0
    have htotal : t + ∑ i, y i ≤ r := by
      simpa [Fin.sum_univ_succ] using hy.2
    exact ht ⟨hzero, by linarith⟩

theorem volume_solidSimplex_succ (n : ℕ) (r : ℝ) :
    volume (solidSimplex (n + 1) r) =
      ∫⁻ t in Icc 0 r, volume (solidSimplex n (r - t)) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
  have hm := (isClosed_solidSimplex (n + 1) r).measurableSet
  rw [← hp.measure_preimage hm.nullMeasurableSet]
  change (volume.prod volume) (e ⁻¹' solidSimplex (n + 1) r) = _
  rw [Measure.prod_apply (hm.preimage e.measurable)]
  have he : ∀ t : ℝ, (Prod.mk t ⁻¹' (e ⁻¹' solidSimplex (n + 1) r)) =
      if t ∈ Icc 0 r then solidSimplex n (r - t) else ∅ := by
    intro t
    convert solidSimplex_section n r t using 1
    ext y
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  simp_rw [he]
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro t
  by_cases ht : t ∈ Icc 0 r <;> simp [ht]

/-- The one-variable polynomial integral giving the factorial recurrence. -/
theorem simplex_slice_integral (r : ℝ) (n : ℕ) :
    (∫ t in (0 : ℝ)..r, (r - t) ^ n / (n.factorial : ℝ)) =
      r ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ n) r]
  simp only [sub_self, sub_zero]
  rw [integral_pow]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    zero_pow (Nat.succ_ne_zero n), sub_zero]
  rw [div_div]

/-- Normalization is proved for all dimensions, including the zero-dimensional base. -/
theorem volume_solidSimplex (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    volume (solidSimplex n r) = ENNReal.ofReal (r ^ n / (n.factorial : ℝ)) := by
  induction n generalizing r with
  | zero =>
    have hs : solidSimplex 0 r = Set.univ := by
      ext x
      simp [solidSimplex, hr]
    rw [hs, Measure.volume_pi_eq_dirac]
    simp
  | succ n ih =>
    rw [volume_solidSimplex_succ]
    have he : (∫⁻ t in Icc 0 r, volume (solidSimplex n (r - t))) =
        ∫⁻ t in Icc 0 r, ENNReal.ofReal ((r - t) ^ n / (n.factorial : ℝ)) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t ht
      exact ih (by linarith [ht.2])
    rw [he]
    have hi : IntegrableOn (fun t : ℝ => (r - t) ^ n / (n.factorial : ℝ)) (Icc 0 r) :=
      (by fun_prop : Continuous (fun t : ℝ => (r - t) ^ n / (n.factorial : ℝ))).integrableOn_Icc
    have hn : 0 ≤ᵐ[volume.restrict (Icc 0 r)]
        (fun t : ℝ => (r - t) ^ n / (n.factorial : ℝ)) := by
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t ht
      exact div_nonneg (pow_nonneg (by linarith [ht.2]) _) (Nat.cast_nonneg _)
    rw [← ofReal_integral_eq_lintegral_ofReal hi hn, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hr, simplex_slice_integral]

end
end Funk
