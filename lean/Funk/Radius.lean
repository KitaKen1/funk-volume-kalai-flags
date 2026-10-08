import Funk.FlagReduction
import Mathlib.Analysis.SpecialFunctions.Artanh

/-! Exact radius substitution, using mathlib's real inverse hyperbolic tangent.
The last theorem is a scalar reduction with explicit analytic assumptions.
-/

namespace Funk

noncomputable section

def radius (R : ℝ) : ℝ := 1 - Real.exp (-R)

theorem radius_pos {R : ℝ} (hR : 0 < R) : 0 < radius R := by
  have h : Real.exp (-R) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  dsimp [radius]
  linarith

theorem radius_lt_one (R : ℝ) : radius R < 1 := by
  have h := Real.exp_pos (-R)
  dsimp [radius]
  linarith

theorem radius_ratio (R : ℝ) :
    (1 + radius R) / (1 - radius R) = 2 * Real.exp R - 1 := by
  have h := Real.exp_ne_zero R
  dsimp [radius]
  rw [Real.exp_neg]
  field_simp
  ring

theorem four_artanh_radius {R : ℝ} (hR : 0 < R) :
    4 * Real.artanh (radius R) = 2 * Real.log (2 * Real.exp R - 1) := by
  rw [Real.artanh_eq_half_log ⟨by linarith [radius_pos hR], (radius_lt_one R).le⟩,
    radius_ratio]
  ring

theorem log_lower_of_funk_lower {n : ℕ} {W : ℝ → ℝ}
    (lower : ∀ τ, 0 < τ → τ < 1 → (4 * Real.artanh τ) ^ n / (n.factorial : ℝ) ≤ W τ) :
    ∀ R > 0, ((2 : ℝ) ^ n / (n.factorial : ℝ)) *
      (Real.log (2 * Real.exp R - 1)) ^ n ≤ W (radius R) := by
  intro R hR
  have h := lower (radius R) (radius_pos hR) (radius_lt_one R)
  rw [four_artanh_radius hR, mul_pow] at h
  convert h using 1
  ring

/-- S1, including the exact `atanh` normalization. Neither geometric input is proved here. -/
theorem count_bound_of_funk_lower_and_upper {n N : ℕ} {W : ℝ → ℝ}
    (lower : ∀ τ, 0 < τ → τ < 1 → (4 * Real.artanh τ) ^ n / (n.factorial : ℝ) ≤ W τ)
    (upper : ∀ ε > 0, ∃ R > 0,
      W (radius R) ≤ ((N : ℝ) / (n.factorial : ℝ) ^ 2 + ε) * R ^ n) :
    2 ^ n * n.factorial ≤ N :=
  count_bound_of_log_lower_and_upper (log_lower_of_funk_lower lower) upper

end
end Funk
