import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Tactic

/-! The explicitly proposed height function of the tilted lens.
This verifies its ODE and monotonicity, not the existence or univalence of the
complex map having this boundary. The parameter `c` will later be √(1-τ²).
-/

namespace Funk

noncomputable section

def lensHeight (τ b c θ : ℝ) : ℝ := (1 - c * Real.exp (-b * θ)) / τ

theorem hasDerivAt_lensHeight (τ b c θ : ℝ) :
    HasDerivAt (lensHeight τ b c) (b * c * Real.exp (-b * θ) / τ) θ := by
  convert ((hasDerivAt_const θ (1 : ℝ)).sub
    ((((hasDerivAt_id θ).const_mul (-b)).exp).const_mul c)).div_const τ using 1
  · ext x
    dsimp [lensHeight]
  · dsimp
    ring

theorem lensHeight_ode {τ : ℝ} (hτ : τ ≠ 0) (b c θ : ℝ) :
    deriv (lensHeight τ b c) θ = b / τ * (1 - τ * lensHeight τ b c θ) := by
  rw [(hasDerivAt_lensHeight τ b c θ).deriv]
  dsimp [lensHeight]
  field_simp
  ring

theorem lensHeight_deriv_pos {τ b c : ℝ} (hτ : 0 < τ) (hb : 0 < b)
    (hc : 0 < c) (θ : ℝ) : 0 < deriv (lensHeight τ b c) θ := by
  rw [(hasDerivAt_lensHeight τ b c θ).deriv]
  positivity

theorem lensHeight_strictMono {τ b c : ℝ} (hτ : 0 < τ) (hb : 0 < b)
    (hc : 0 < c) : StrictMono (lensHeight τ b c) :=
  strictMono_of_deriv_pos (lensHeight_deriv_pos hτ hb hc)

theorem lensHeight_margin_pos {τ b c : ℝ} (hτ : τ ≠ 0) (hc : 0 < c) (θ : ℝ) :
    0 < 1 - τ * lensHeight τ b c θ := by
  have heq : 1 - τ * lensHeight τ b c θ = c * Real.exp (-b * θ) := by
    dsimp [lensHeight]
    field_simp
    ring
  rw [heq]
  positivity

def lensRate (τ : ℝ) : ℝ := 2 * Real.artanh τ / Real.pi

def lensScale (τ : ℝ) : ℝ := Real.sqrt (1 - τ ^ 2)

def tiltedHeight (τ : ℝ) : ℝ → ℝ := lensHeight τ (lensRate τ) (lensScale τ)

theorem lensRate_pos {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) : 0 < lensRate τ := by
  have h := Real.artanh_pos ⟨hτ₀, hτ₁⟩
  dsimp [lensRate]
  positivity

theorem lensScale_pos {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) : 0 < lensScale τ := by
  apply Real.sqrt_pos_of_pos
  nlinarith

theorem tiltedHeight_strictMono {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    StrictMono (tiltedHeight τ) :=
  lensHeight_strictMono hτ₀ (lensRate_pos hτ₀ hτ₁) (lensScale_pos hτ₀ hτ₁)

theorem tiltedHeight_ode {τ : ℝ} (hτ₀ : 0 < τ) (θ : ℝ) :
    deriv (tiltedHeight τ) θ = lensRate τ / τ * (1 - τ * tiltedHeight τ θ) :=
  lensHeight_ode hτ₀.ne' _ _ _

theorem lensScale_mul_exp_artanh {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    lensScale τ * Real.exp (Real.artanh τ) = 1 + τ := by
  have hsq : 0 ≤ 1 - τ ^ 2 := by nlinarith
  have hden : 1 - τ ≠ 0 := by linarith
  have hratio : (1 - τ ^ 2) * ((1 + τ) / (1 - τ)) = (1 + τ) ^ 2 := by
    field_simp
    ring
  rw [Real.exp_artanh ⟨by linarith, hτ₁⟩, lensScale, ← Real.sqrt_mul hsq, hratio]
  exact Real.sqrt_sq (by linarith)

theorem lensScale_mul_exp_neg_artanh {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    lensScale τ * Real.exp (-Real.artanh τ) = 1 - τ := by
  have hc := lensScale_pos hτ₀ hτ₁
  have hsquare : lensScale τ ^ 2 = 1 - τ ^ 2 := by
    exact Real.sq_sqrt (by nlinarith)
  have h := congrArg (fun x : ℝ => (1 - τ) * x) (lensScale_mul_exp_artanh hτ₀ hτ₁)
  rw [Real.exp_neg, ← div_eq_mul_inv, div_eq_iff (Real.exp_ne_zero _)]
  apply mul_left_cancel₀ hc.ne'
  nlinarith

theorem tiltedHeight_left {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    tiltedHeight τ (-Real.pi / 2) = -1 := by
  have hθ : -lensRate τ * (-Real.pi / 2) = Real.artanh τ := by
    dsimp [lensRate]
    field_simp
  dsimp [tiltedHeight, lensHeight]
  rw [hθ, lensScale_mul_exp_artanh hτ₀ hτ₁]
  field_simp
  ring

theorem tiltedHeight_right {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    tiltedHeight τ (Real.pi / 2) = 1 := by
  have hθ : -lensRate τ * (Real.pi / 2) = -Real.artanh τ := by
    dsimp [lensRate]
    field_simp
  dsimp [tiltedHeight, lensHeight]
  rw [hθ, lensScale_mul_exp_neg_artanh hτ₀ hτ₁]
  field_simp
  ring

theorem tiltedHeight_mem_Icc {τ θ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1)
    (hθ : θ ∈ Set.Icc (-Real.pi / 2) (Real.pi / 2)) :
    tiltedHeight τ θ ∈ Set.Icc (-1) 1 := by
  have hm := (tiltedHeight_strictMono hτ₀ hτ₁).monotone
  constructor
  · rw [← tiltedHeight_left hτ₀ hτ₁]
    exact hm hθ.1
  · rw [← tiltedHeight_right hτ₀ hτ₁]
    exact hm hθ.2

end
end Funk
