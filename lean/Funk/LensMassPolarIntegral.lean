import Funk.LensMassBasisIntegral
import OAI.Analysis.Mahler.ComplexVolume
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-! Genuine all-coordinate polar transformation of the exact basis-domain
mass integrals. Pinned Mathlib supplies the slit/null-set treatment. The powered
radius-to-simplex transformation and reverse-Fatou are separate obligations. -/

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Funk
noncomputable section

/-- Exact Euclidean complex vector reconstructed by the standard polar chart. -/
def lensPolarVector {n : ℕ} (p : Fin n → ℝ × ℝ) : LensComplexSpace n :=
  WithLp.toLp 2 (fun i => Complex.polarCoord.symm (p i))

/-- The product positive-radius/open-angle chart of the pinned polar theorem. -/
def lensPolarChart (n : ℕ) : Set (Fin n → ℝ × ℝ) :=
  Set.univ.pi (fun _ => Complex.polarCoord.target)

theorem measurableSet_lensPolarChart (n : ℕ) : MeasurableSet (lensPolarChart n) :=
  MeasurableSet.univ_pi (fun _ => Complex.polarCoord.open_target.measurableSet)

theorem lensPolarVector_normSq {n : ℕ} (p : Fin n → ℝ × ℝ) (i : Fin n) :
    Complex.normSq (lensPolarVector p i) = (p i).1 ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  change ‖Complex.polarCoord.symm (p i)‖ ^ 2 = _
  rw [Complex.norm_polarCoord_symm, sq_abs]

/-- The radial Jacobian and universal kernel, with all powers and constants retained. -/
theorem lensPolarVector_kernel {n : ℕ} (k : ℕ) (p : Fin n → ℝ × ℝ) :
    lensPowerRadialKernel k (lensPolarVector p) =
      (n.factorial : ℝ) * ∏ i, (k : ℝ)^2 * ((p i).1 ^ 2) ^ (k-1) := by
  simp only [lensPowerRadialKernel, lensPolarVector_normSq]

/-- Exact polar change of variables on any measurable Euclidean complex domain. -/
theorem lensPower_radialIntegral_eq_polar_integral {n : ℕ} (k : ℕ)
    {D : Set (LensComplexSpace n)} (hD : MeasurableSet D) :
    (∫⁻ u in D, ENNReal.ofReal (lensPowerRadialKernel k u)) =
      ∫⁻ p in lensPolarChart n, (∏ i, ENNReal.ofReal (p i).1) *
        D.indicator (fun u => ENNReal.ofReal (lensPowerRadialKernel k u)) (lensPolarVector p) := by
  let S := (@WithLp.toLp 2 (Fin n → ℂ)) ⁻¹' D
  have hS : MeasurableSet S := (MeasurableEquiv.toLp 2 (Fin n → ℂ)).measurable hD
  rw [← OAI.SymmetricMahler.setLIntegral_complex_toLp n D
    (fun u => ENNReal.ofReal (lensPowerRadialKernel k u))]
  rw [← lintegral_indicator hS]
  have h := (Complex.lintegral_comp_pi_polarCoord_symm
    (S.indicator (fun w => ENNReal.ofReal (lensPowerRadialKernel k (WithLp.toLp 2 w))))).symm
  exact h

/-- Actual mass equals the finite polar-integral sum over the original unsigned bases. -/
theorem lensPower_massIntegral_eq_polar_integrals {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ) :
    OAI.Mahler.massIntegral (lensComplexDomain τ rows) (fun j => lensPowerComponent τ rows k j) =
      ∑ s ∈ unsignedBasisIndices rows,
        ∫⁻ p in lensPolarChart n, (∏ i, ENNReal.ofReal (p i).1) *
          (lensBasisPowerDomain τ rows k s).indicator
            (fun u => ENNReal.ofReal (lensPowerRadialKernel k u)) (lensPolarVector p) := by
  classical
  rw [lensPower_massIntegral_eq_basis_radial_integrals hτ0 hτ1 rows k]
  exact Finset.sum_congr rfl (fun s _ => lensPower_radialIntegral_eq_polar_integral k
    (isOpen_lensBasisPowerDomain hτ0 hτ1 rows k s).measurableSet)

theorem lensPower_polar_integrals_lower {n m : ℕ} (hn : 1 ≤ n) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n)
    (hK : IsCompact (stripBody rows)) {k : ℕ} (hk : 1 ≤ k) :
    ENNReal.ofReal ((Real.pi * (k : ℝ))^n) ≤
      ∑ s ∈ unsignedBasisIndices rows,
        ∫⁻ p in lensPolarChart n, (∏ i, ENNReal.ofReal (p i).1) *
          (lensBasisPowerDomain τ rows k s).indicator
            (fun u => ENNReal.ofReal (lensPowerRadialKernel k u)) (lensPolarVector p) := by
  rw [← lensPower_massIntegral_eq_polar_integrals hτ0 hτ1 rows k]
  exact lensPower_massIntegral_lower hn hτ0 hτ1 rows hK hk

end
end Funk
