import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Nonnegative product integration and finite tensorization of densities.
The induction follows mathlib's Bochner product-Fubini construction using
`measurePreserving_piFinSuccAbove`, now for the nonnegative integral. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

set_option backward.isDefEq.respectTransparency false in
theorem lintegral_fin_prod {n : ℕ} {E : Type*}
    [MeasurableSpace E] {μ : Fin n → Measure E}
    [∀ i, SigmaFinite (μ i)] {f : Fin n → E → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := (measurePreserving_piFinSuccAbove μ 0).symm
    rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
      Fin.zero_succAbove, cast_eq, Fin.cons_zero]
    have hg : Measurable (fun x : Fin n → E => ∏ i : Fin n, f (Fin.succ i) (x i)) :=
      Finset.measurable_prod Finset.univ (fun i _ => (hf (Fin.succ i)).comp (measurable_pi_apply i))
    rw [lintegral_prod_mul (μ := μ 0) (ν := Measure.pi (fun i : Fin n => μ (Fin.succ i)))
      (hf 0).aemeasurable hg.aemeasurable]
    rw [ih (fun i => hf i.succ)]

theorem pi_withDensity_fin {n : ℕ} {E : Type*}
    [MeasurableSpace E] {μ : Fin n → Measure E}
    [∀ i, SigmaFinite (μ i)] {f : Fin n → E → ℝ≥0∞}
    [∀ i, SigmaFinite ((μ i).withDensity (f i))]
    (hf : ∀ i, Measurable (f i)) :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi,
    lintegral_fin_prod hf]
  exact Finset.prod_congr rfl (fun i _ => (withDensity_apply _ (hs i)).symm)

end
end Funk
