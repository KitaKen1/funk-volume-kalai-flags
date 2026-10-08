import Funk.LensHeight
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! The proposed complex lens series, with its actual reported coefficients.
We prove absolute and uniform convergence on the closed unit disk, continuity,
symmetry, and the coefficient/finite-sum differential identities. LensAnalytic
proves the infinite-sum ODE; univalence and boundary identification remain.
-/

open Set Filter
open scoped Topology

namespace Funk

noncomputable section

def lensCoeff (b : ℝ) (j : ℕ) : ℂ :=
  (-1 : ℂ) ^ j / (((2 * j + 1 : ℕ) : ℂ) * (((2 * j + 1 : ℕ) : ℂ) - b * Complex.I))

def lensTerm (b : ℝ) (j : ℕ) (z : ℂ) : ℂ := lensCoeff b j * z ^ (2 * j + 1)

def lensSeries (b : ℝ) (z : ℂ) : ℂ := ∑' j, lensTerm b j z

def lensPartial (b : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range N, lensTerm b j z

def lensFactor (τ : ℝ) : ℝ := 4 * lensRate τ / (Real.pi * τ)

def tiltedLens (τ : ℝ) (z : ℂ) : ℂ := (lensFactor τ : ℂ) * lensSeries (lensRate τ) z

theorem lens_denominator_ne_zero (b : ℝ) (j : ℕ) :
    ((2 * j + 1 : ℕ) : ℂ) - b * Complex.I ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp at hr
  linarith [Nat.cast_nonneg (α := ℝ) j]

theorem norm_lensCoeff_le (b : ℝ) (j : ℕ) :
    ‖lensCoeff b j‖ ≤ 1 / ((j : ℝ) + 1) ^ 2 := by
  have hj : 0 < (j : ℝ) + 1 := by positivity
  have ha : (j : ℝ) + 1 ≤ ‖((2 * j + 1 : ℕ) : ℂ)‖ := by
    rw [Complex.norm_natCast]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hb : (j : ℝ) + 1 ≤ ‖((2 * j + 1 : ℕ) : ℂ) - b * Complex.I‖ := by
    have h := Complex.re_le_norm (((2 * j + 1 : ℕ) : ℂ) - b * Complex.I)
    have heq : ((((2 * j + 1 : ℕ) : ℂ) - b * Complex.I).re) = 2 * (j : ℝ) + 1 := by simp
    rw [heq] at h
    linarith [Nat.cast_nonneg (α := ℝ) j]
  rw [lensCoeff, norm_div, norm_mul]
  simp only [norm_pow, norm_neg, norm_one, one_pow]
  apply one_div_le_one_div_of_le (sq_pos_of_pos hj)
  nlinarith [mul_le_mul ha hb hj.le (norm_nonneg _)]

theorem summable_lens_majorant : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) := by
  simpa using (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))

theorem norm_lensTerm_le (b : ℝ) (j : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖lensTerm b j z‖ ≤ 1 / ((j : ℝ) + 1) ^ 2 := by
  calc
    _ = ‖lensCoeff b j‖ * ‖z‖ ^ (2 * j + 1) := by rw [lensTerm, norm_mul, norm_pow]
    _ ≤ ‖lensCoeff b j‖ := mul_le_of_le_one_right (norm_nonneg _)
      (pow_le_one₀ (norm_nonneg _) hz)
    _ ≤ _ := norm_lensCoeff_le b j

theorem summable_norm_lensTerm (b : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Summable (fun j => ‖lensTerm b j z‖) :=
  summable_lens_majorant.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => norm_lensTerm_le b j hz)

theorem summable_lensTerm (b : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Summable (fun j => lensTerm b j z) := (summable_norm_lensTerm b hz).of_norm

theorem lensPartial_tendstoUniformlyOn (b : ℝ) :
    TendstoUniformlyOn (lensPartial b) (lensSeries b) atTop {z : ℂ | ‖z‖ ≤ 1} := by
  exact tendstoUniformlyOn_tsum_nat summable_lens_majorant (fun j _ hz => norm_lensTerm_le b j hz)

theorem lensSeries_continuousOn (b : ℝ) :
    ContinuousOn (lensSeries b) {z : ℂ | ‖z‖ ≤ 1} := by
  exact continuousOn_tsum (fun j => (continuous_const.mul (continuous_id.pow _)).continuousOn)
    summable_lens_majorant (fun j _ hz => norm_lensTerm_le b j hz)

theorem tiltedLens_continuousOn (τ : ℝ) :
    ContinuousOn (tiltedLens τ) {z : ℂ | ‖z‖ ≤ 1} :=
  continuousOn_const.mul (lensSeries_continuousOn _)

theorem lensTerm_neg (b : ℝ) (j : ℕ) (z : ℂ) : lensTerm b j (-z) = -lensTerm b j z := by
  simp [lensTerm, pow_add, pow_mul]

theorem lensSeries_neg (b : ℝ) (z : ℂ) : lensSeries b (-z) = -lensSeries b z := by
  simp only [lensSeries, lensTerm_neg, tsum_neg]

theorem tiltedLens_neg (τ : ℝ) (z : ℂ) : tiltedLens τ (-z) = -tiltedLens τ z := by
  simp [tiltedLens, lensSeries_neg]

theorem tiltedLens_zero (τ : ℝ) : tiltedLens τ 0 = 0 := by
  simp [tiltedLens, lensSeries, lensTerm]

theorem lensCoeff_ode (b : ℝ) (j : ℕ) :
    (((2 * j + 1 : ℕ) : ℂ) - b * Complex.I) * lensCoeff b j =
      (-1 : ℂ) ^ j / ((2 * j + 1 : ℕ) : ℂ) := by
  have hm : ((2 * j + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2 * j + 1 ≠ 0)
  unfold lensCoeff
  field_simp [lens_denominator_ne_zero b j]
  exact div_self (lens_denominator_ne_zero b j)

def lensTermDeriv (b : ℝ) (j : ℕ) (z : ℂ) : ℂ :=
  lensCoeff b j * ((2 * j + 1 : ℕ) : ℂ) * z ^ (2 * j)

theorem hasDerivAt_lensTerm (b : ℝ) (j : ℕ) (z : ℂ) :
    HasDerivAt (lensTerm b j) (lensTermDeriv b j z) z := by
  convert ((hasDerivAt_id z).pow (2 * j + 1)).const_mul (lensCoeff b j) using 1
  · rfl
  · simp [lensTermDeriv, mul_assoc]

theorem lensTerm_ode (b : ℝ) (j : ℕ) (z : ℂ) :
    z * lensTermDeriv b j z - (b : ℂ) * Complex.I * lensTerm b j z =
      (-1 : ℂ) ^ j * z ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℂ) := by
  calc
    _ = ((((2 * j + 1 : ℕ) : ℂ) - b * Complex.I) * lensCoeff b j) * z ^ (2 * j + 1) := by
      simp only [lensTermDeriv, lensTerm, pow_succ]
      ring
    _ = _ := by rw [lensCoeff_ode]; ring

theorem hasDerivAt_lensPartial (b : ℝ) (N : ℕ) (z : ℂ) :
    HasDerivAt (lensPartial b N) (∑ j ∈ Finset.range N, lensTermDeriv b j z) z :=
  HasDerivAt.fun_sum (fun j _ => hasDerivAt_lensTerm b j z)

theorem lensPartial_ode (b : ℝ) (N : ℕ) (z : ℂ) :
    z * deriv (lensPartial b N) z - (b : ℂ) * Complex.I * lensPartial b N z =
      ∑ j ∈ Finset.range N, (-1 : ℂ) ^ j * z ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℂ) := by
  rw [(hasDerivAt_lensPartial b N z).deriv, lensPartial,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun j _ => lensTerm_ode b j z)

end
end Funk
