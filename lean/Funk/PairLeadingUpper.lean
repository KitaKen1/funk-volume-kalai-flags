import Funk.FlagSupportOrder
import Mathlib.Analysis.SpecificLimits.Basic

/-! The proved fixed additive bound gives an epsilon leading upper for each actual flag pair.
No equality, distinct-pair decay, or sharp global flag count is inferred from this result. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace Funk
noncomputable section

/-- A shifted power has the same normalized leading coefficient. -/
theorem tendsto_shifted_power_ratio (n : ℕ) (C d : ℝ) :
    Tendsto (fun R : ℝ => ((R + C) / R) ^ n / d) atTop (𝓝 (1 / d)) := by
  have hratio : Tendsto (fun R : ℝ => 1 + C / R) atTop (𝓝 (1 : ℝ)) := by
    have hC : Tendsto (fun R : ℝ => C / R) atTop (𝓝 (0 : ℝ)) := by
      simpa only [div_eq_mul_inv, mul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => C) atTop (𝓝 C)).mul
          (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 (0 : ℝ)))
    simpa using tendsto_const_nhds.add hC
  have hp : Tendsto (fun R : ℝ => (1 + C / R) ^ n / d) atTop (𝓝 (1 / d)) := by
    simpa only [one_pow] using (hratio.pow n).div_const d
  apply hp.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have he : 1 + C / R = (R + C) / R := by field_simp [hR.ne']
  rw [he]

/-- Uniform eventual scalar envelope, retaining the actual two-factorial normalization. -/
theorem eventually_shifted_power_le (n : ℕ) (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, 0 < R ∧
      (R + C) ^ n / (n.factorial : ℝ) ^ 2 ≤
        (1 / (n.factorial : ℝ) ^ 2 + ε) * R ^ n := by
  have ht := tendsto_shifted_power_ratio n C ((n.factorial : ℝ) ^ 2)
  have he := ht.eventually_lt_const (show 1 / (n.factorial : ℝ) ^ 2 <
      1 / (n.factorial : ℝ) ^ 2 + ε by linarith)
  filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with R h hR
  refine ⟨hR, ?_⟩
  have hdiv : ((R + C) / R) ^ n / (n.factorial : ℝ) ^ 2 =
      ((R + C) ^ n / (n.factorial : ℝ) ^ 2) / R ^ n := by
    rw [div_pow]
    ring
  rw [hdiv] at h
  exact ((div_lt_iff₀ (pow_pos hR n)).mp h).le

/-- Every actual pair has coefficient at most 1/(n!)², with no certificate input. -/
theorem dualFlag_integral_eventually_le_leading {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, 0 < R ∧
      (∫⁻ u in dualFlagDomain (radius R) F G, dualProductKernel u) ≤
        ENNReal.ofReal ((1 / (n.factorial : ℝ) ^ 2 + ε) * R ^ n) := by
  obtain ⟨C, _, hC⟩ := exists_dualFlag_integral_ordered_upper hp hP F G
  filter_upwards [eventually_shifted_power_le n C hε] with R hR
  exact ⟨hR.1, (hC R hR.1).trans (ENNReal.ofReal_le_ofReal hR.2)⟩

/-- An explicit threshold works for every larger radius, not just one chosen sample. -/
theorem dualFlag_integral_epsilon_upper {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      (∫⁻ u in dualFlagDomain (radius R) F G, dualProductKernel u) ≤
        ENNReal.ofReal ((1 / (n.factorial : ℝ) ^ 2 + ε) * R ^ n) := by
  obtain ⟨b, hb⟩ := eventually_atTop.mp (dualFlag_integral_eventually_le_leading hp hP F G hε)
  refine ⟨max b 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro R hR
  exact (hb R ((le_max_left _ _).trans hR)).2

end
end Funk
