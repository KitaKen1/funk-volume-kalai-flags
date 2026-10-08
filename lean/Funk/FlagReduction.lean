import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-! A reduction, not a proof of the geometric Funk or Kalai conjecture.
`V` and `N` are parameters. The lower bound and upper envelope are explicit inputs.
In particular this file does not identify `N` with a polytope's actual flag count.
-/

namespace Funk

/-- An arbitrarily accurate upper envelope at some positive radius is sufficient.
Neither a limit nor a uniform threshold for all large radii is required. -/
theorem coefficient_le_of_envelopes {n : ℕ} {V : ℝ → ℝ} {c a : ℝ}
    (lower : ∀ R > 0, c * R ^ n ≤ V R)
    (upper : ∀ ε > 0, ∃ R > 0, V R ≤ (a + ε) * R ^ n) : c ≤ a := by
  by_contra h
  have hca : a < c := lt_of_not_ge h
  obtain ⟨R, hR, hbound⟩ := upper ((c - a) / 2) (by linarith)
  have h := (mul_le_mul_iff_left₀ (pow_pos hR n)).mp ((lower R hR).trans hbound)
  linarith

theorem factorial_cast_pos (n : ℕ) : 0 < (n.factorial : ℝ) := by
  exact_mod_cast Nat.factorial_pos n

/-- Conversion of normalized volume coefficients to a natural-number count. -/
theorem count_bound_of_coefficient {n N : ℕ}
    (h : (2 : ℝ) ^ n / (n.factorial : ℝ) ≤ (N : ℝ) / (n.factorial : ℝ) ^ 2) :
    2 ^ n * n.factorial ≤ N := by
  have hd := factorial_cast_pos n
  have heq : (2 : ℝ) ^ n / (n.factorial : ℝ) =
      ((2 : ℝ) ^ n * (n.factorial : ℝ)) / (n.factorial : ℝ) ^ 2 := by
    field_simp
  rw [heq] at h
  have h' := (div_le_div_iff_of_pos_right (pow_pos hd 2)).mp h
  exact_mod_cast h'

/-- Conditional endpoint for S1. The two analytic inputs remain visible in the type. -/
theorem count_bound_of_envelopes {n N : ℕ} {V : ℝ → ℝ}
    (lower : ∀ R > 0, ((2 : ℝ) ^ n / (n.factorial : ℝ)) * R ^ n ≤ V R)
    (upper : ∀ ε > 0, ∃ R > 0,
      V R ≤ ((N : ℝ) / (n.factorial : ℝ) ^ 2 + ε) * R ^ n) :
    2 ^ n * n.factorial ≤ N :=
  count_bound_of_coefficient (coefficient_le_of_envelopes lower upper)

/-- The finite inequality that avoids proving a logarithmic limit. -/
theorem radius_le_log {R : ℝ} (hR : 0 ≤ R) :
    R ≤ Real.log (2 * Real.exp R - 1) := by
  have h := Real.one_le_exp_iff.mpr hR
  have hlog := Real.log_le_log (Real.exp_pos R) (show Real.exp R ≤ 2 * Real.exp R - 1 by linarith)
  simpa only [Real.log_exp] using hlog

theorem power_lower_of_log_lower {n : ℕ} {V : ℝ → ℝ}
    (lower : ∀ R > 0,
      ((2 : ℝ) ^ n / (n.factorial : ℝ)) * (Real.log (2 * Real.exp R - 1)) ^ n ≤ V R) :
    ∀ R > 0, ((2 : ℝ) ^ n / (n.factorial : ℝ)) * R ^ n ≤ V R := by
  intro R hR
  apply le_trans _ (lower R hR)
  apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le (radius_le_log hR.le) n)
  positivity

theorem count_bound_of_log_lower_and_upper {n N : ℕ} {V : ℝ → ℝ}
    (lower : ∀ R > 0,
      ((2 : ℝ) ^ n / (n.factorial : ℝ)) * (Real.log (2 * Real.exp R - 1)) ^ n ≤ V R)
    (upper : ∀ ε > 0, ∃ R > 0,
      V R ≤ ((N : ℝ) / (n.factorial : ℝ) ^ 2 + ε) * R ^ n) :
    2 ^ n * n.factorial ≤ N :=
  count_bound_of_envelopes (power_lower_of_log_lower lower) upper

end Funk
