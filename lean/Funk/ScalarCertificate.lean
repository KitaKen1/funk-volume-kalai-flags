import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Scalar certificates for the explicit vertices of a translated polar. -/

namespace Funk

theorem signed_le_one {ε t : ℝ} (hε : ε = 1 ∨ ε = -1) (ht : |t| ≤ 1) :
    ε * t ≤ 1 := by
  obtain ⟨htl, htu⟩ := abs_le.mp ht
  rcases hε with rfl | rfl <;> linarith

theorem denominator_pos {τ ε t : ℝ} (hτ₀ : 0 ≤ τ) (hτ₁ : τ < 1)
    (hε : ε = 1 ∨ ε = -1) (ht : |t| ≤ 1) :
    0 < 1 - ε * τ * t := by
  have h := mul_le_mul_of_nonneg_left (signed_le_one hε ht) hτ₀
  nlinarith

/-- The scalar inequality behind polar containment; no independence assumption is needed. -/
theorem vertex_pairing_le_one {τ ε t u : ℝ} (hτ₀ : 0 ≤ τ) (hτ₁ : τ < 1)
    (hε : ε = 1 ∨ ε = -1) (ht : |t| ≤ 1) (hu : |u| ≤ 1) :
    (ε * u - ε * τ * t) / (1 - ε * τ * t) ≤ 1 := by
  apply (div_le_one (denominator_pos hτ₀ hτ₁ hε ht)).2
  have h := signed_le_one hε hu
  linarith

end Funk
