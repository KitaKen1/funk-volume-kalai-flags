import Funk.LensHeight
import Funk.ScalarCertificate
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Exact density transport for the explicit height parametrization.
Each half-circle has total mass 1/2 under angular density 1/(2π).
The two signs use reflected heights; sign and height are not assumed independent.
Identification with the actual complex boundary is proved separately in
LensBoundaryMeasure and LensBoundaryProbability.
-/

namespace Funk

noncomputable section

def branchDensity (τ ε t : ℝ) : ℝ :=
  τ / (4 * Real.artanh τ * (1 - ε * τ * t))

theorem branchDensity_pos {τ ε t : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1)
    (hε : ε = 1 ∨ ε = -1) (ht : |t| ≤ 1) : 0 < branchDensity τ ε t := by
  have ha := Real.artanh_pos ⟨hτ₀, hτ₁⟩
  have hd := denominator_pos hτ₀.le hτ₁ hε ht
  exact div_pos hτ₀ (mul_pos (mul_pos (by norm_num) ha) hd)

theorem branchDensity_reflect (τ t : ℝ) :
    branchDensity τ (-1) t = branchDensity τ 1 (-t) := by
  simp [branchDensity]

theorem hasDerivAt_tiltedHeight (τ θ : ℝ) :
    HasDerivAt (tiltedHeight τ)
      (lensRate τ * lensScale τ * Real.exp (-lensRate τ * θ) / τ) θ :=
  hasDerivAt_lensHeight τ (lensRate τ) (lensScale τ) θ

theorem tiltedHeight_density_jacobian {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1)
    (θ : ℝ) :
    branchDensity τ 1 (tiltedHeight τ θ) * deriv (tiltedHeight τ) θ =
      1 / (2 * Real.pi) := by
  have ha : Real.artanh τ ≠ 0 := (Real.artanh_pos ⟨hτ₀, hτ₁⟩).ne'
  have ht : τ ≠ 0 := hτ₀.ne'
  have hm : 1 - τ * tiltedHeight τ θ ≠ 0 :=
    (lensHeight_margin_pos ht (lensScale_pos hτ₀ hτ₁) θ).ne'
  rw [tiltedHeight_ode hτ₀]
  dsimp [branchDensity, lensRate]
  simp only [one_mul]
  field_simp
  ring

/-- Test-function change of variables for the positive branch. This follows from
the explicit ODE and the monotone substitution theorem, without a measure-level
pushforward construction or a new antiderivative. -/
theorem positiveBranch_transport {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1)
    (g : ℝ → ℝ) :
    (∫ θ in (-Real.pi / 2)..(Real.pi / 2), g (tiltedHeight τ θ) / (2 * Real.pi)) =
      ∫ t in (-1 : ℝ)..1, g t * branchDensity τ 1 t := by
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := tiltedHeight τ) (f' := deriv (tiltedHeight τ))
    (g := fun t => g t * branchDensity τ 1 t)
    (a := -Real.pi / 2) (b := Real.pi / 2)
    (fun θ _ => (hasDerivAt_tiltedHeight τ θ).continuousAt.continuousWithinAt)
    (fun θ _ => (hasDerivAt_tiltedHeight τ θ).differentiableAt.hasDerivAt)
    (fun θ _ => (lensHeight_deriv_pos hτ₀ (lensRate_pos hτ₀ hτ₁)
      (lensScale_pos hτ₀ hτ₁) θ).le)
  rw [tiltedHeight_left hτ₀ hτ₁, tiltedHeight_right hτ₀ hτ₁] at hsub
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro θ hθ
  dsimp only [Function.comp_apply]
  rw [mul_assoc, tiltedHeight_density_jacobian hτ₀ hτ₁]
  ring

theorem positiveBranch_mass {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    (∫ t in (-1 : ℝ)..1, branchDensity τ 1 t) = 1 / 2 := by
  have h := positiveBranch_transport hτ₀ hτ₁ (fun _ => 1)
  simp only [one_mul, intervalIntegral.integral_const, smul_eq_mul] at h
  rw [← h]
  field_simp
  ring

theorem negativeBranch_transport {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1)
    (g : ℝ → ℝ) :
    (∫ θ in (-Real.pi / 2)..(Real.pi / 2), g (-tiltedHeight τ θ) / (2 * Real.pi)) =
      ∫ t in (-1 : ℝ)..1, g t * branchDensity τ (-1) t := by
  rw [positiveBranch_transport hτ₀ hτ₁ (fun t => g (-t))]
  have h := intervalIntegral.integral_comp_neg
    (f := fun t => g t * branchDensity τ (-1) t) (a := (-1 : ℝ)) (b := 1)
  simp only [neg_neg] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [branchDensity_reflect, neg_neg]

theorem negativeBranch_mass {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    (∫ t in (-1 : ℝ)..1, branchDensity τ (-1) t) = 1 / 2 := by
  have h := negativeBranch_transport hτ₀ hτ₁ (fun _ => 1)
  simp only [one_mul, intervalIntegral.integral_const, smul_eq_mul] at h
  rw [← h]
  field_simp
  ring

end
end Funk
