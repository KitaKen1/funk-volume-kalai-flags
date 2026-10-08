import Funk.LensAnalytic

/-! A regularized derivative with an absolutely convergent series on the closed
disk. The coefficient differences decay quadratically, even though the original
derivative series need not converge at the two poles. -/

open Set Filter
open scoped Topology

namespace Funk
noncomputable section

def lensJetCoeff (b : ℝ) (j : ℕ) : ℂ :=
  (-1 : ℂ) ^ (j + 1) * (-2) /
    ((((2 * (j + 1) + 1 : ℕ) : ℂ) - b * Complex.I) *
      (((2 * j + 1 : ℕ) : ℂ) - b * Complex.I))

def lensJetTerm (b : ℝ) (j : ℕ) (z : ℂ) : ℂ :=
  lensJetCoeff b j * z ^ (2 * j + 2)

def lensJet (b : ℝ) (z : ℂ) : ℂ :=
  1 / (1 - (b : ℂ) * Complex.I) + ∑' j, lensJetTerm b j z

def tiltedLensJet (τ : ℝ) (z : ℂ) : ℂ :=
  (lensFactor τ : ℂ) * lensJet (lensRate τ) z

theorem lensJetCoeff_eq_sub (b : ℝ) (j : ℕ) :
    lensJetCoeff b j = (-1 : ℂ) ^ (j + 1) *
      (1 / (((2 * (j + 1) + 1 : ℕ) : ℂ) - b * Complex.I) -
       1 / (((2 * j + 1 : ℕ) : ℂ) - b * Complex.I)) := by
  unfold lensJetCoeff
  rw [div_sub_div _ _ (lens_denominator_ne_zero b (j + 1)) (lens_denominator_ne_zero b j)]
  have he : (1 : ℂ) * (((2 * j + 1 : ℕ) : ℂ) - b * Complex.I) -
      (((2 * (j + 1) + 1 : ℕ) : ℂ) - b * Complex.I) * 1 = -2 := by
    push_cast
    ring
  rw [he]
  ring

theorem norm_lensJetCoeff_le (b : ℝ) (j : ℕ) :
    ‖lensJetCoeff b j‖ ≤ 2 / ((j : ℝ) + 1) ^ 2 := by
  have hj : 0 < (j : ℝ) + 1 := by positivity
  have hd (k : ℕ) (hk : j ≤ k) :
      (j : ℝ) + 1 ≤ ‖((2 * k + 1 : ℕ) : ℂ) - b * Complex.I‖ := by
    have h := Complex.re_le_norm (((2 * k + 1 : ℕ) : ℂ) - b * Complex.I)
    have heq : ((((2 * k + 1 : ℕ) : ℂ) - b * Complex.I).re) = 2 * (k : ℝ) + 1 := by simp
    rw [heq] at h
    have hk' : (j : ℝ) ≤ k := by exact_mod_cast hk
    linarith [Nat.cast_nonneg (α := ℝ) k]
  rw [lensJetCoeff, norm_div, norm_mul, norm_mul]
  norm_num only [norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_ofNat]
  apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hj)
  nlinarith [mul_le_mul (hd (j + 1) (by omega)) (hd j le_rfl) hj.le (norm_nonneg _)]

theorem summable_lensJet_majorant :
    Summable (fun j : ℕ => 2 / ((j : ℝ) + 1) ^ 2) := by
  simpa only [mul_one_div] using summable_lens_majorant.mul_left 2

theorem norm_lensJetTerm_le (b : ℝ) (j : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖lensJetTerm b j z‖ ≤ 2 / ((j : ℝ) + 1) ^ 2 := by
  calc
    _ = ‖lensJetCoeff b j‖ * ‖z‖ ^ (2 * j + 2) := by
      rw [lensJetTerm, norm_mul, norm_pow]
    _ ≤ ‖lensJetCoeff b j‖ := mul_le_of_le_one_right (norm_nonneg _)
      (pow_le_one₀ (norm_nonneg _) hz)
    _ ≤ _ := norm_lensJetCoeff_le b j

theorem summable_lensJetTerm (b : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Summable (fun j => lensJetTerm b j z) :=
  (summable_lensJet_majorant.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun j => norm_lensJetTerm_le b j hz)).of_norm

theorem lensJet_continuousOn (b : ℝ) :
    ContinuousOn (lensJet b) {z : ℂ | ‖z‖ ≤ 1} := by
  apply continuousOn_const.add
  exact continuousOn_tsum (fun j => (continuous_const.mul (continuous_id.pow _)).continuousOn)
    summable_lensJet_majorant (fun j _ hz => norm_lensJetTerm_le b j hz)

theorem lensJet_differentiableOn (b : ℝ) :
    DifferentiableOn ℂ (lensJet b) {z : ℂ | ‖z‖ < 1} := by
  apply (differentiableOn_const _).add
  exact Complex.differentiableOn_tsum_of_summable_norm summable_lensJet_majorant
    (fun j => ((differentiable_const _).mul (differentiable_id.pow _)).differentiableOn)
    (isOpen_lt continuous_norm continuous_const)
    (fun j _ hz => norm_lensJetTerm_le b j hz.le)

theorem lensTermDeriv_eq (b : ℝ) (j : ℕ) (z : ℂ) :
    lensTermDeriv b j z = (-1 : ℂ) ^ j /
      (((2 * j + 1 : ℕ) : ℂ) - b * Complex.I) * z ^ (2 * j) := by
  have hm : ((2 * j + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : 2 * j + 1 ≠ 0)
  simp only [lensTermDeriv, lensCoeff]
  field_simp

theorem lensJetTerm_eq (b : ℝ) (j : ℕ) (z : ℂ) :
    lensJetTerm b j z = lensTermDeriv b (j + 1) z + z ^ 2 * lensTermDeriv b j z := by
  rw [lensJetTerm, lensJetCoeff_eq_sub, lensTermDeriv_eq, lensTermDeriv_eq]
  simp only [show 2 * (j + 1) = 2 * j + 2 by omega, pow_succ]
  ring

theorem lensJet_eq_deriv (b : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    lensJet b z = (1 + z ^ 2) * deriv (lensSeries b) z := by
  have hs : HasSum (fun j => lensTermDeriv b j z) (deriv (lensSeries b) z) := by
    simpa only [(hasDerivAt_lensTerm b _ z).deriv] using hasSum_deriv_lensTerm b hz
  have ht := (hasSum_nat_add_iff' 1).mpr hs
  have hu := ht.add (hs.mul_left (z ^ 2))
  simp only [Finset.sum_range_one, ← lensJetTerm_eq] at hu
  have he := (summable_lensJetTerm b hz.le).hasSum.unique hu
  rw [lensJet, he]
  simp [lensTermDeriv_eq]
  ring

theorem lensJet_neg (b : ℝ) (z : ℂ) : lensJet b (-z) = lensJet b z := by
  simp [lensJet, lensJetTerm, pow_add, pow_mul]

theorem lensJet_zero (b : ℝ) : lensJet b 0 = 1 / (1 - (b : ℂ) * Complex.I) := by
  simp [lensJet, lensJetTerm]

theorem tiltedLensJet_continuousOn (τ : ℝ) :
    ContinuousOn (tiltedLensJet τ) {z : ℂ | ‖z‖ ≤ 1} :=
  continuousOn_const.mul (lensJet_continuousOn _)

theorem tiltedLensJet_differentiableOn (τ : ℝ) :
    DifferentiableOn ℂ (tiltedLensJet τ) {z : ℂ | ‖z‖ < 1} :=
  (lensJet_differentiableOn _).const_mul _

theorem tiltedLensJet_eq_deriv (τ : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    tiltedLensJet τ z = (1 + z ^ 2) * deriv (tiltedLens τ) z := by
  have hd := ((lensSeries_differentiableOn (lensRate τ)).differentiableAt
    ((isOpen_lt continuous_norm continuous_const).mem_nhds hz)).hasDerivAt.const_mul
      (lensFactor τ : ℂ)
  change HasDerivAt (tiltedLens τ) _ z at hd
  rw [hd.deriv, tiltedLensJet, lensJet_eq_deriv _ hz]
  ring

theorem tiltedLensJet_neg (τ : ℝ) (z : ℂ) :
    tiltedLensJet τ (-z) = tiltedLensJet τ z := by
  simp only [tiltedLensJet, lensJet_neg]

end
end Funk
