import Funk.LensMassBasisIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact one-coordinate powered-radius coefficient. These scalar identities
calibrate the upcoming radius-to-simplex measure transport; they do not assert
that the transport or the boundary probability covering is already proved. -/

open MeasureTheory

namespace Funk
noncomputable section

theorem lensRadial_power_weight {k : ℕ} (hk : 1 ≤ k) (r : ℝ) :
    (r^2)^(k-1) * r = r^(2*k-1) := by
  rw [← pow_mul, ← pow_succ]
  congr 1
  omega

/-- The polar radial Jacobian matches k/2 times the derivative of r^(2k). -/
theorem lensRadial_power_jacobian {k : ℕ} (hk : 1 ≤ k) (r : ℝ) :
    (k : ℝ)^2 * (r^2)^(k-1) * r =
      ((k : ℝ)/2) * ((2*k : ℕ) : ℝ) * r^(2*k-1) := by
  rw [mul_assoc, lensRadial_power_weight hk, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem lensRadial_power_hasDerivAt (k : ℕ) (r : ℝ) :
    HasDerivAt (fun x : ℝ => x^(2*k)) (((2*k : ℕ) : ℝ) * r^(2*k-1)) r := by
  exact hasDerivAt_pow (2*k) r

/-- One positive-radius factor integrates to exactly k/2. -/
theorem lensRadial_weight_integral {k : ℕ} (hk : 1 ≤ k) :
    (∫ r in (0 : ℝ)..1, (k : ℝ)^2 * r^(2*k-1)) = (k : ℝ)/2 := by
  rw [intervalIntegral.integral_const_mul, integral_pow]
  have he : 2*k-1+1 = 2*k := by omega
  have hd : ((2*k-1 : ℕ) : ℝ) + 1 = ((2*k : ℕ) : ℝ) := by exact_mod_cast he
  rw [he, hd, Nat.cast_mul, Nat.cast_ofNat]
  simp only [one_pow, zero_pow (by omega : 2*k ≠ 0), sub_zero]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  field_simp

/-- Restoring the full angular length supplies exactly the pi*k coefficient. -/
theorem lensRadial_angular_coefficient {k : ℕ} (hk : 1 ≤ k) :
    (2 * Real.pi) * (∫ r in (0 : ℝ)..1, (k : ℝ)^2 * r^(2*k-1)) = Real.pi * (k : ℝ) := by
  rw [lensRadial_weight_integral hk]
  ring

end
end Funk
