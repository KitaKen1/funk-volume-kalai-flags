import Funk.LensPowerSublevels
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! The actual homogeneous leading polynomials for the tilted-lens power map.
The inverse slope is computed from the known explicit derivative at zero. -/

open Set Metric
open scoped BigOperators

namespace Funk
noncomputable section

/-- The actual derivative of the inverse at zero, not a supplied coefficient. -/
def lensInverseSlope (τ : ℝ) : ℂ := deriv (tiltedLensInverse τ) 0

theorem lensInverseSlope_eq_inv_deriv {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    lensInverseSlope τ = (deriv (tiltedLens τ) 0)⁻¹ := by
  simpa only [lensInverseSlope, tiltedLensInverse_zero hτ0 hτ1] using
    (hasDerivAt_tiltedLensInverse hτ0 hτ1 (lensGraphBody_zero_mem_interior hτ0 hτ1)).deriv

theorem lensInverseSlope_ne_zero {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    lensInverseSlope τ ≠ 0 := by
  rw [lensInverseSlope_eq_inv_deriv hτ0 hτ1]
  exact inv_ne_zero (tiltedLens_deriv_ne_zero hτ0 hτ1 (by norm_num))

/-- Known-answer verification: the proposed coefficient follows from the actual derivative. -/
theorem lensInverseSlope_explicit {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    lensInverseSlope τ = (1 - (lensRate τ : ℂ) * Complex.I) / (lensFactor τ : ℂ) := by
  have hd : deriv (tiltedLens τ) 0 = tiltedLensJet τ 0 := by
    simpa using (tiltedLensJet_eq_deriv τ (z := 0) (by norm_num)).symm
  rw [lensInverseSlope_eq_inv_deriv hτ0 hτ1, hd, tiltedLensJet, lensJet_zero]
  simp only [mul_one_div, inv_div]

/-- (g'(0) times the actual real row's complex linear polynomial)^k. -/
def lensLeadingPolynomial {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n) (k : ℕ)
    (j : Fin m) : MvPolynomial (Fin n) ℂ :=
  (MvPolynomial.C (lensInverseSlope τ) *
    ∑ i : Fin n, MvPolynomial.C (rows j i : ℂ) * MvPolynomial.X i) ^ k

theorem lensLeadingPolynomial_homogeneous {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n)
    (k : ℕ) (j : Fin m) : (lensLeadingPolynomial τ rows k j).IsHomogeneous k := by
  have hr : (∑ i : Fin n, MvPolynomial.C (rows j i : ℂ) * MvPolynomial.X i).IsHomogeneous 1 :=
    MvPolynomial.IsHomogeneous.sum _ _ _ (fun i _ => MvPolynomial.isHomogeneous_C_mul_X _ i)
  simpa only [lensLeadingPolynomial, one_mul] using (hr.C_mul (lensInverseSlope τ)).pow k

theorem lensLeadingPolynomial_eval {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n)
    (k : ℕ) (j : Fin m) (z : LensComplexSpace n) :
    MvPolynomial.eval (fun i => z i) (lensLeadingPolynomial τ rows k j) =
      (lensInverseSlope τ * lensComplexRow (rows j) z) ^ k := by
  simp [lensLeadingPolynomial, lensComplexRow_apply]

/-- Nonzero input has a nonzero homogeneous coordinate; no determinant is an extra premise. -/
theorem lensLeadingPolynomial_nonzero {n m : ℕ} {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (rows : Fin m → Space n) (hK : IsCompact (stripBody rows)) {k : ℕ} (hk : 0 < k)
    {z : LensComplexSpace n} (hz : z ≠ 0) :
    ∃ j, MvPolynomial.eval (fun i => z i) (lensLeadingPolynomial τ rows k j) ≠ 0 := by
  by_contra hn
  push Not at hn
  apply hz
  apply (lensComplexRows_eq_zero_iff rows hK z).mp
  intro j
  have hj := hn j
  rw [lensLeadingPolynomial_eval, pow_eq_zero_iff hk.ne'] at hj
  exact (mul_eq_zero.mp hj).resolve_left (lensInverseSlope_ne_zero hτ0 hτ1)

end
end Funk
