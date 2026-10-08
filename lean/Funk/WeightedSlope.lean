import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! A one-dimensional certificate for strict positivity between zero endpoints.
The weight need not be differentiable: its positivity and the strict decrease
of the weighted derivative are enough. -/

open Set

namespace Funk

theorem pos_of_weighted_deriv_strictAnti {f f' w : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (ha : f a = 0) (hb : f b = 0)
    (hw : ∀ x ∈ Ioo a b, 0 < w x)
    (hm : StrictAntiOn (fun x => w x * f' x) (Ioo a b))
    {x : ℝ} (hx : x ∈ Ioo a b) : 0 < f x := by
  by_contra! hfx
  obtain ⟨u, hu, hdu⟩ := exists_hasDerivAt_eq_slope f f' hx.1
    (hc.mono (Icc_subset_Icc le_rfl hx.2.le))
    (fun y hy => hd y ⟨hy.1, hy.2.trans hx.2⟩)
  obtain ⟨v, hv, hdv⟩ := exists_hasDerivAt_eq_slope f f' hx.2
    (hc.mono (Icc_subset_Icc hx.1.le le_rfl))
    (fun y hy => hd y ⟨hx.1.trans hy.1, hy.2⟩)
  have hu' : u ∈ Ioo a b := ⟨hu.1, hu.2.trans hx.2⟩
  have hv' : v ∈ Ioo a b := ⟨hx.1.trans hv.1, hv.2⟩
  have hfu : f' u ≤ 0 := by
    rw [hdu, ha, sub_zero]
    exact div_nonpos_of_nonpos_of_nonneg hfx (sub_pos.mpr hx.1).le
  have hfv : 0 ≤ f' v := by
    rw [hdv, hb, zero_sub]
    exact div_nonneg (neg_nonneg.mpr hfx) (sub_pos.mpr hx.2).le
  have hwu : w u * f' u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hw u hu').le hfu
  have hwv : 0 ≤ w v * f' v := mul_nonneg (hw v hv').le hfv
  exact (not_lt_of_ge (hwu.trans hwv)) (hm hu' hv' (hu.2.trans hv.1))

end Funk
