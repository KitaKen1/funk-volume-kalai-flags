import Funk.LensPolarPower

/-! Exact powered-radius transport of the genuine mass integrals. The
transformed indicator retains the literal basis domain; no limiting boundary
probability or simplex support is assumed here. -/

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Funk
noncomputable section

/-- The actual basis domain tested at inverse powered radii, with angles retained. -/
def lensPoweredBasisIndicator {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n)
    (k : ℕ) (s : Fin n → Fin m) (q : Fin n → ℝ × ℝ) : ℝ≥0∞ :=
  (lensBasisPowerDomain τ rows k s).indicator (fun _ => 1)
    (lensPolarVector (lensPolarRoot k q))

/-- Pointwise indicator cancellation, including points outside the actual domain. -/
theorem lensPolarPower_indicator_jacobian {n : ℕ} {k : ℕ} (hk : 1 ≤ k)
    (D : Set (LensComplexSpace n)) {p : Fin n → ℝ × ℝ} (hp : p ∈ lensPolarChart n) :
    (∏ i, ENNReal.ofReal (p i).1) *
      D.indicator (fun u => ENNReal.ofReal (lensPowerRadialKernel k u)) (lensPolarVector p) =
      ENNReal.ofReal ((n.factorial : ℝ) * ((k : ℝ)/2)^n) *
        (ENNReal.ofReal ((lensPolarPowerDerivative k p).det) *
          D.indicator (fun _ => 1) (lensPolarVector p)) := by
  classical
  by_cases hd : lensPolarVector p ∈ D
  · simp only [indicator_of_mem hd, mul_one]
    exact lensPolarPower_kernel_jacobian hk hp
  · simp only [indicator_of_notMem hd, mul_zero]

/-- Joint substitution applied to an arbitrary measurable radial-kernel domain. -/
theorem lensPower_radialIntegral_eq_powered_integral {n : ℕ} {k : ℕ} (hk : 1 ≤ k)
    {D : Set (LensComplexSpace n)} (hD : MeasurableSet D) :
    (∫⁻ u in D, ENNReal.ofReal (lensPowerRadialKernel k u)) =
      ENNReal.ofReal ((n.factorial : ℝ) * ((k : ℝ)/2)^n) *
        ∫⁻ q in lensPolarChart n,
          D.indicator (fun _ => 1) (lensPolarVector (lensPolarRoot k q)) := by
  rw [lensPower_radialIntegral_eq_polar_integral k hD]
  conv_rhs => rw [lintegral_lensPolarPower_chart hk]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_congr_fun (measurableSet_lensPolarChart n)
  intro p hp
  dsimp only
  rw [lensPolarRoot_power hk hp, ← lensPolarPowerDerivative_det]
  exact lensPolarPower_indicator_jacobian hk D hp

/-- The genuine mass is the finite sum of exact powered-radius indicator integrals. -/
theorem lensPower_massIntegral_eq_powered_integrals {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) {k : ℕ} (hk : 1 ≤ k) :
    OAI.Mahler.massIntegral (lensComplexDomain τ rows) (fun j => lensPowerComponent τ rows k j) =
      ∑ s ∈ unsignedBasisIndices rows,
        ENNReal.ofReal ((n.factorial : ℝ) * ((k : ℝ)/2)^n) *
          ∫⁻ q in lensPolarChart n, lensPoweredBasisIndicator τ rows k s q := by
  classical
  rw [lensPower_massIntegral_eq_basis_radial_integrals hτ0 hτ1 rows k]
  exact Finset.sum_congr rfl (fun s _ => lensPower_radialIntegral_eq_powered_integral hk
    (isOpen_lensBasisPowerDomain hτ0 hτ1 rows k s).measurableSet)

theorem lensPower_powered_integrals_lower {n m : ℕ} (hn : 1 ≤ n) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n)
    (hK : IsCompact (stripBody rows)) {k : ℕ} (hk : 1 ≤ k) :
    ENNReal.ofReal ((Real.pi * (k : ℝ))^n) ≤
      ∑ s ∈ unsignedBasisIndices rows,
        ENNReal.ofReal ((n.factorial : ℝ) * ((k : ℝ)/2)^n) *
          ∫⁻ q in lensPolarChart n, lensPoweredBasisIndicator τ rows k s q := by
  rw [← lensPower_massIntegral_eq_powered_integrals hτ0 hτ1 rows hk]
  exact lensPower_massIntegral_lower hn hτ0 hτ1 rows hK hk

end
end Funk
