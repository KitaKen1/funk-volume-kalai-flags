import Funk.LensBasisParametrization

/-! Actual basis/conformal change of variables for each unsigned minor integral.
The inverse/forward derivative factors and basis determinant squares cancel,
leaving only the universal powered radial kernel on the literal pulled-back domain. -/

open Set Matrix MeasureTheory
open scoped BigOperators ENNReal

namespace Funk
noncomputable section

/-- Universal kernel after the genuine basis and conformal transformations. -/
def lensPowerRadialKernel {n : ℕ} (k : ℕ) (u : LensComplexSpace n) : ℝ :=
  (n.factorial : ℝ) * ∏ i, (k : ℝ)^2 * Complex.normSq (u i) ^ (k-1)

theorem lensPowerRadialKernel_nonneg {n : ℕ} (k : ℕ) (u : LensComplexSpace n) :
    0 ≤ lensPowerRadialKernel k u := by
  exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun _ _ =>
    mul_nonneg (sq_nonneg _) (pow_nonneg (Complex.normSq_nonneg _) _))

theorem continuous_lensPowerRadialKernel {n : ℕ} (k : ℕ) :
    Continuous (@lensPowerRadialKernel n k) := by
  unfold lensPowerRadialKernel
  fun_prop

/-- All actual Jacobian and minor factors cancel on the unit polydisk. -/
theorem lensBasisParametrization_minor_cancellation {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ)
    {s : Fin n → Fin m} (hs : s ∈ unsignedBasisIndices rows)
    {u : LensComplexSpace n} (hu : u ∈ lensOpenPolydisk n) :
    ((lensBasisParametrizationDerivative τ (Matrix.of fun i => rows (s i)) u).restrictScalars ℝ).det *
      ((n.factorial : ℝ) *
        (∏ i, lensPowerWeight τ rows k (lensBasisParametrization τ (Matrix.of fun l => rows (s l)) u) (s i)) *
          (Matrix.of fun i => rows (s i)).det ^ 2) = lensPowerRadialKernel k u := by
  classical
  let B := Matrix.of fun i => rows (s i)
  have hB : B.det ≠ 0 := ((mem_unsignedBasisIndices rows s).mp hs).2
  rw [lensBasisParametrization_real_det]
  change B⁻¹.det ^ 2 * (∏ i, Complex.normSq (deriv (tiltedLens τ) (u i))) *
    ((n.factorial : ℝ) * (∏ i, lensPowerWeight τ rows k (lensBasisParametrization τ B u) (s i)) *
      B.det ^ 2) = _
  calc
    _ = (n.factorial : ℝ) * (B⁻¹.det ^ 2 * B.det ^ 2) *
        ∏ i, lensPowerWeight τ rows k (lensBasisParametrization τ B u) (s i) *
          Complex.normSq (deriv (tiltedLens τ) (u i)) := by
      rw [Finset.prod_mul_distrib]
      ring
    _ = lensPowerRadialKernel k u := by
      rw [lensBasis_inverse_det_square_cancel hB, mul_one]
      congr 1
      exact Finset.prod_congr rfl (fun i _ => lensPowerWeight_forward_cancellation hτ0 hτ1 rows k hs hu i)

/-- Each exact minor integral becomes a universal radial-kernel integral on the actual domain. -/
theorem lensPower_minorIntegral_eq_basis_radial_integral {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ)
    {s : Fin n → Fin m} (hs : s ∈ unsignedBasisIndices rows) :
    (∫⁻ z in lensComplexDomain τ rows ∩ {z | lensPowerEnergy τ rows k z < 1},
      ENNReal.ofReal ((n.factorial : ℝ) * (∏ i, lensPowerWeight τ rows k z (s i)) *
        (Matrix.of fun i => rows (s i)).det ^ 2)) =
      ∫⁻ u in lensBasisPowerDomain τ rows k s, ENNReal.ofReal (lensPowerRadialKernel k u) := by
  have hB : (Matrix.of fun i => rows (s i)).det ≠ 0 :=
    ((mem_unsignedBasisIndices rows s).mp hs).2
  have hS := (isOpen_lensBasisPowerDomain hτ0 hτ1 rows k s).measurableSet
  have hsub : lensBasisPowerDomain τ rows k s ⊆ lensOpenPolydisk n := fun _ hu => hu.1
  rw [← lensBasisPowerDomain_image hτ0 hτ1 rows k hs]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (volume : Measure (LensComplexSpace n)) hS
    (fun _ hu => ((lensBasisParametrization_hasFDerivAt τ _ (hsub hu)).restrictScalars ℝ).hasFDerivWithinAt)
    ((lensBasisParametrization_injOn hτ0 hτ1 hB).mono hsub)]
  apply setLIntegral_congr_fun hS
  intro u hu
  dsimp only
  have hj : 0 ≤ ((lensBasisParametrizationDerivative τ (Matrix.of fun i => rows (s i)) u).restrictScalars ℝ).det := by
    rw [lensBasisParametrization_real_det]
    exact mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun _ _ => Complex.normSq_nonneg _)
  rw [abs_of_nonneg hj, ← ENNReal.ofReal_mul hj,
    lensBasisParametrization_minor_cancellation hτ0 hτ1 rows k hs hu.1]

/-- Genuine mass equality after basis/conformal transformation, for all unsigned bases. -/
theorem lensPower_massIntegral_eq_basis_radial_integrals {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ) :
    OAI.Mahler.massIntegral (lensComplexDomain τ rows) (fun j => lensPowerComponent τ rows k j) =
      ∑ s ∈ unsignedBasisIndices rows,
        ∫⁻ u in lensBasisPowerDomain τ rows k s, ENNReal.ofReal (lensPowerRadialKernel k u) := by
  classical
  rw [lensPower_massIntegral_eq_unsigned_minor_integrals hτ0 hτ1 rows k]
  exact Finset.sum_congr rfl (fun _ hs => lensPower_minorIntegral_eq_basis_radial_integral hτ0 hτ1 rows k hs)

theorem lensPower_basis_radial_integrals_lower {n m : ℕ} (hn : 1 ≤ n) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n)
    (hK : IsCompact (stripBody rows)) {k : ℕ} (hk : 1 ≤ k) :
    ENNReal.ofReal ((Real.pi * (k : ℝ))^n) ≤
      ∑ s ∈ unsignedBasisIndices rows,
        ∫⁻ u in lensBasisPowerDomain τ rows k s, ENNReal.ofReal (lensPowerRadialKernel k u) := by
  rw [← lensPower_massIntegral_eq_basis_radial_integrals hτ0 hτ1 rows k]
  exact lensPower_massIntegral_lower hn hτ0 hτ1 rows hK hk

end
end Funk
