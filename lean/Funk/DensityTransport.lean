import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! A measure-level certificate for one-dimensional density transport.
The density times the absolute derivative is checked pointwise on the source.
No integrability assumption on a test function is needed. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

theorem map_scaled_restrict_eq_withDensity {f f' : ℝ → ℝ} {s t : Set ℝ}
    {ρ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} (hs : MeasurableSet s) (hf : Measurable f)
    (hd : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hi : InjOn f s)
    (him : f '' s = t) (hj : ∀ x ∈ s, ENNReal.ofReal |f' x| * ρ (f x) = c) :
    (c • volume.restrict s).map f = (volume.restrict t).withDensity ρ := by
  ext u hu
  rw [Measure.map_apply hf hu, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply (hf hu), withDensity_apply _ hu, Measure.restrict_restrict hu]
  have hv := lintegral_image_eq_lintegral_abs_deriv_mul ((hf hu).inter hs)
    (fun x hx => (hd x hx.2).mono inter_subset_right) (hi.mono inter_subset_right) ρ
  rw [image_preimage_inter, him] at hv
  rw [hv]
  calc
    _ = ∫⁻ _ in f ⁻¹' u ∩ s, c := by simp only [lintegral_const, Measure.restrict_apply_univ]
    _ = _ := lintegral_congr_ae (by
      filter_upwards [ae_restrict_mem ((hf hu).inter hs)] with x hx
      exact (hj x hx.2).symm)

end
end Funk
