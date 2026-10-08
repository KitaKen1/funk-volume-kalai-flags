import Funk.PeriodicAngularMeasure
import Funk.LensPoweredProductMeasure
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Exact transport of the actual mass to the existing normalized angular law.
The radius and angle remain joint variables. Probability normalization is
supplied from the proved simplex volume, not assumed as an interface premise. -/

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Funk
noncomputable section

/-- Literal product-coordinate form of the already proved actual indicator. -/
def lensPoweredProductIndicator {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n)
    (k : ℕ) (s : Fin n → Fin m) (p : Space n × Space n) : ℝ≥0∞ :=
  lensPoweredBasisIndicator τ rows k s
    ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)).symm p)

theorem lensPolarRoot_continuous {n : ℕ} (k : ℕ) : Continuous (@lensPolarRoot n k) := by
  apply continuous_pi
  intro i
  exact ((Real.continuous_rpow_const (by positivity : 0 ≤ ((2*k : ℕ) : ℝ)⁻¹)).comp
    ((continuous_apply i).fst)).prodMk ((continuous_apply i).snd)

theorem lensPolarVector_continuous (n : ℕ) : Continuous (@lensPolarVector n) := by
  apply (EuclideanSpace.equiv (Fin n) ℂ).symm.continuous.comp
  apply continuous_pi
  intro i
  simp only [Complex.polarCoord_symm_apply]
  fun_prop

/-- The actual domain is open, hence its transported indicator is measurable. -/
theorem measurable_lensPoweredProductIndicator {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n)
    (k : ℕ) (s : Fin n → Fin m) :
    Measurable (lensPoweredProductIndicator τ rows k s) := by
  exact (measurable_const.indicator
    (isOpen_lensBasisPowerDomain hτ0 hτ1 rows k s).measurableSet).comp
    ((lensPolarVector_continuous n).measurable.comp
      ((lensPolarRoot_continuous k).measurable.comp
        (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)).symm.measurable))

/-- Polar reconstruction is the same literal circle vector used by the periodic law. -/
theorem lensPoweredProductIndicator_eq_circleMap {n m : ℕ} (τ : ℝ)
    (rows : Fin m → Space n) (k : ℕ) (s : Fin n → Fin m) (t θ : Space n) :
    lensPoweredProductIndicator τ rows k s (t,θ) =
      (lensBasisPowerDomain τ rows k s).indicator (fun _ => 1)
        (WithLp.toLp 2 (fun i => circleMap 0 (t i ^ (((2*k : ℕ) : ℝ)⁻¹)) (θ i))) := by
  change (lensBasisPowerDomain τ rows k s).indicator (fun _ => 1)
    (WithLp.toLp 2 (fun i => Complex.polarCoord.symm
      ((t i ^ (((2*k : ℕ) : ℝ)⁻¹)), θ i))) = _
  apply congrArg ((lensBasisPowerDomain τ rows k s).indicator (fun _ => (1 : ℝ≥0∞)))
  apply congrArg (WithLp.toLp 2)
  funext i
  apply Complex.ext <;>
    simp [Complex.polarCoord_symm_apply, circleMap_zero_re, circleMap_zero_im,
      -Complex.ofReal_cos, -Complex.ofReal_sin]

/-- The two angular laws agree for the actual indicator at every fixed powered radius. -/
theorem lensPoweredProductIndicator_angular_integral_eq {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n)
    (k : ℕ) (s : Fin n → Fin m) (t : Space n) :
    (∫⁻ θ, lensPoweredProductIndicator τ rows k s (t,θ) ∂lensStandardAngularRows n) =
      ∫⁻ θ, lensPoweredProductIndicator τ rows k s (t,θ) ∂lensAngularRows n := by
  simp_rw [lensPoweredProductIndicator_eq_circleMap]
  exact lintegral_lensStandardAngularRows_circleMap
    (fun i => t i ^ (((2*k : ℕ) : ℝ)⁻¹))
    ((measurable_const.indicator
      (isOpen_lensBasisPowerDomain hτ0 hτ1 rows k s).measurableSet).comp
        (MeasurableEquiv.toLp 2 (Fin n → ℂ)).measurable)

/-- Finite tensorization of the exact standard-angle normalization factor. -/
theorem lensStandardAngularRows_eq_smul (n : ℕ) :
    lensStandardAngularRows n = ENNReal.ofReal ((1/(2*Real.pi))^n) •
      volume.restrict (lensStandardAngleCube n) := by
  classical
  unfold lensStandardAngularRows
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs)]
  simp only [lensStandardAngular, Measure.smul_apply, smul_eq_mul]
  simp_rw [Measure.restrict_apply (hs _)]
  rw [lensStandardAngleCube, ← Set.pi_inter_distrib, volume_pi_pi, Finset.prod_mul_distrib]
  rw [ENNReal.ofReal_pow (by positivity : 0 ≤ 1/(2*Real.pi))]
  simp

/-- Unnormalized polar angle volume equals (2π)^n times the standard probability law. -/
theorem volume_restrict_lensStandardAngleCube (n : ℕ) :
    volume.restrict (lensStandardAngleCube n) =
      ENNReal.ofReal ((2*Real.pi)^n) • lensStandardAngularRows n := by
  rw [lensStandardAngularRows_eq_smul, smul_smul,
    ← ENNReal.ofReal_mul (by positivity)]
  have he : (2*Real.pi)^n * (1/(2*Real.pi))^n = 1 := by
    rw [← mul_pow]
    rw [one_div, mul_inv_cancel₀ (ne_of_gt Real.two_pi_pos), one_pow]
  rw [he, ENNReal.ofReal_one, one_smul]

/-- The actual integral on the polar product domain uses exactly the existing angular law. -/
theorem lensPoweredProductIndicator_integral_eq_angular {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n)
    (k : ℕ) (s : Fin n → Fin m) :
    (∫⁻ p in positivePoweredSimplex n ×ˢ lensStandardAngleCube n,
      lensPoweredProductIndicator τ rows k s p) =
      ENNReal.ofReal ((2*Real.pi)^n) *
        ∫⁻ t in positivePoweredSimplex n,
          ∫⁻ θ, lensPoweredProductIndicator τ rows k s (t,θ) ∂lensAngularRows n := by
  change (∫⁻ p in positivePoweredSimplex n ×ˢ lensStandardAngleCube n,
    lensPoweredProductIndicator τ rows k s p ∂volume.prod volume) = _
  rw [setLIntegral_prod _ (measurable_lensPoweredProductIndicator hτ0 hτ1 rows k s).aemeasurable,
    volume_restrict_lensStandardAngleCube]
  simp_rw [lintegral_smul_measure,
    lensPoweredProductIndicator_angular_integral_eq hτ0 hτ1 rows k s]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Exact n!(πk)^n coefficient after transporting the existing angular probability. -/
theorem lensPoweredAngular_coefficient (n k : ℕ) :
    ENNReal.ofReal ((n.factorial : ℝ) * ((k : ℝ)/2)^n) *
      ENNReal.ofReal ((2*Real.pi)^n) =
        ENNReal.ofReal ((Real.pi*(k : ℝ))^n) * ENNReal.ofReal (n.factorial : ℝ) := by
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [mul_assoc, ← mul_pow,
    show (k : ℝ)/2 * (2*Real.pi) = Real.pi*(k : ℝ) by ring, mul_comm]

/-- Genuine mass, exact existing angular probability, and the positive simplex. -/
theorem lensPower_massIntegral_eq_existing_angular_integrals {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) {k : ℕ} (hk : 1 ≤ k) :
    OAI.Mahler.massIntegral (lensComplexDomain τ rows) (fun j => lensPowerComponent τ rows k j) =
      ∑ s ∈ unsignedBasisIndices rows,
        ENNReal.ofReal ((Real.pi*(k : ℝ))^n) * ENNReal.ofReal (n.factorial : ℝ) *
          ∫⁻ t in positivePoweredSimplex n,
            ∫⁻ θ, lensPoweredProductIndicator τ rows k s (t,θ) ∂lensAngularRows n := by
  classical
  rw [lensPower_massIntegral_eq_powered_product_integrals hτ0 hτ1 rows hk]
  apply Finset.sum_congr rfl
  intro s _
  change _ * (∫⁻ p in positivePoweredSimplex n ×ˢ lensStandardAngleCube n,
    lensPoweredProductIndicator τ rows k s p) = _
  rw [lensPoweredProductIndicator_integral_eq_angular hτ0 hτ1 rows k s,
    ← mul_assoc, lensPoweredAngular_coefficient]

end
end Funk
