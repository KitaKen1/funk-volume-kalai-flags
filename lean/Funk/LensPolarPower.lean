import Funk.LensMassPolarIntegral
import Funk.LensRadialCoefficient
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Genuine joint powered-radius transformation on the existing polar chart.
Angles are unchanged. The radial Jacobian and its inverse are proved for every
positive k; no measure-transport or coefficient premise is supplied. -/

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Funk
noncomputable section

def lensPolarPowerPair (k : ℕ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1^(2*k), p.2)

def lensPolarRootPair (k : ℕ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 ^ (((2*k : ℕ) : ℝ)⁻¹), p.2)

def lensPolarPowerPairDerivative (k : ℕ) (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.toSpanSingleton ℝ (((2*k : ℕ) : ℝ) * p.1^(2*k-1))).prodMap
    (ContinuousLinearMap.id ℝ ℝ)

theorem lensPolarPowerPair_hasFDerivAt (k : ℕ) (p : ℝ × ℝ) :
    HasFDerivAt (lensPolarPowerPair k) (lensPolarPowerPairDerivative k p) p := by
  change HasFDerivAt (Prod.map (fun x : ℝ => x^(2*k)) (id : ℝ → ℝ)) _ p
  exact (lensRadial_power_hasDerivAt k p.1).hasFDerivAt.prodMap p (hasFDerivAt_id p.2)

theorem lensPolarPowerPairDerivative_det (k : ℕ) (p : ℝ × ℝ) :
    (lensPolarPowerPairDerivative k p).det = ((2*k : ℕ) : ℝ) * p.1^(2*k-1) := by
  change LinearMap.det ((ContinuousLinearMap.toSpanSingleton ℝ
    (((2*k : ℕ) : ℝ) * p.1^(2*k-1))).toLinearMap.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) = _
  rw [LinearMap.det_prodMap]
  change (ContinuousLinearMap.toSpanSingleton ℝ
    (((2*k : ℕ) : ℝ) * p.1^(2*k-1))).det * (1 : ℝ →ₗ[ℝ] ℝ).det = _
  rw [ContinuousLinearMap.det_toSpanSingleton]
  simp

def lensPolarPower {n : ℕ} (k : ℕ) (p : Fin n → ℝ × ℝ) : Fin n → ℝ × ℝ :=
  fun i => lensPolarPowerPair k (p i)

def lensPolarRoot {n : ℕ} (k : ℕ) (p : Fin n → ℝ × ℝ) : Fin n → ℝ × ℝ :=
  fun i => lensPolarRootPair k (p i)

def lensPolarPowerDerivative {n : ℕ} (k : ℕ) (p : Fin n → ℝ × ℝ) :
    (Fin n → ℝ × ℝ) →L[ℝ] Fin n → ℝ × ℝ :=
  ContinuousLinearMap.pi (fun i => (lensPolarPowerPairDerivative k (p i)).comp
    (ContinuousLinearMap.proj i))

theorem lensPolarPower_hasFDerivAt {n : ℕ} (k : ℕ) (p : Fin n → ℝ × ℝ) :
    HasFDerivAt (lensPolarPower k) (lensPolarPowerDerivative k p) p := by
  rw [lensPolarPowerDerivative, hasFDerivAt_pi]
  exact fun i => (lensPolarPowerPair_hasFDerivAt k (p i)).comp p (hasFDerivAt_apply i p)

theorem lensPolarPowerDerivative_det {n : ℕ} (k : ℕ) (p : Fin n → ℝ × ℝ) :
    (lensPolarPowerDerivative k p).det = ∏ i, ((2*k : ℕ) : ℝ) * (p i).1^(2*k-1) := by
  simp only [lensPolarPowerDerivative, ContinuousLinearMap.det_pi,
    lensPolarPowerPairDerivative_det]

theorem lensPolarPower_mapsTo {n : ℕ} (k : ℕ) :
    MapsTo (lensPolarPower k) (lensPolarChart n) (lensPolarChart n) := by
  intro p hp i hi
  change 0 < (p i).1^(2*k) ∧ (p i).2 ∈ Ioo (-Real.pi) Real.pi
  exact ⟨pow_pos (hp i hi).1 _, (hp i hi).2⟩

theorem lensPolarRoot_mapsTo {n : ℕ} (k : ℕ) :
    MapsTo (lensPolarRoot k) (lensPolarChart n) (lensPolarChart n) := by
  intro p hp i hi
  exact ⟨Real.rpow_pos_of_pos (hp i hi).1 _, (hp i hi).2⟩

theorem lensPolarRoot_power {n : ℕ} {k : ℕ} (hk : 1 ≤ k)
    {p : Fin n → ℝ × ℝ} (hp : p ∈ lensPolarChart n) :
    lensPolarRoot k (lensPolarPower k p) = p := by
  funext i
  apply Prod.ext
  · exact Real.pow_rpow_inv_natCast (hp i (mem_univ i)).1.le (by omega : 2*k ≠ 0)
  · rfl

theorem lensPolarPower_root {n : ℕ} {k : ℕ} (hk : 1 ≤ k)
    {p : Fin n → ℝ × ℝ} (hp : p ∈ lensPolarChart n) :
    lensPolarPower k (lensPolarRoot k p) = p := by
  funext i
  apply Prod.ext
  · exact Real.rpow_inv_natCast_pow (hp i (mem_univ i)).1.le (by omega : 2*k ≠ 0)
  · rfl

theorem lensPolarPower_injOn {n : ℕ} {k : ℕ} (hk : 1 ≤ k) :
    InjOn (lensPolarPower k) (lensPolarChart n) := by
  intro p hp q hq he
  calc p = lensPolarRoot k (lensPolarPower k p) := (lensPolarRoot_power hk hp).symm
       _ = lensPolarRoot k (lensPolarPower k q) := congrArg (lensPolarRoot k) he
       _ = q := lensPolarRoot_power hk hq

theorem lensPolarPower_image_chart {n : ℕ} {k : ℕ} (hk : 1 ≤ k) :
    lensPolarPower k '' lensPolarChart n = lensPolarChart n := by
  apply Subset.antisymm (lensPolarPower_mapsTo k).image_subset
  intro p hp
  exact ⟨lensPolarRoot k p, lensPolarRoot_mapsTo k hp, lensPolarPower_root hk hp⟩

theorem lensPolarPowerDerivative_det_nonneg {n : ℕ} (k : ℕ)
    {p : Fin n → ℝ × ℝ} (hp : p ∈ lensPolarChart n) :
    0 ≤ (lensPolarPowerDerivative k p).det := by
  rw [lensPolarPowerDerivative_det]
  exact Finset.prod_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _)
    (pow_nonneg (hp i (mem_univ i)).1.le _)

/-- Joint substitution, with angles retained and arbitrary nonnegative integrand. -/
theorem lintegral_lensPolarPower_chart {n : ℕ} {k : ℕ} (hk : 1 ≤ k)
    (g : (Fin n → ℝ × ℝ) → ℝ≥0∞) :
    (∫⁻ q in lensPolarChart n, g q) =
      ∫⁻ p in lensPolarChart n, ENNReal.ofReal (∏ i, ((2*k : ℕ) : ℝ) * (p i).1^(2*k-1)) *
        g (lensPolarPower k p) := by
  conv_lhs => rw [← lensPolarPower_image_chart hk]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (volume : Measure (Fin n → ℝ × ℝ)) (measurableSet_lensPolarChart n)
    (fun p _ => (lensPolarPower_hasFDerivAt k p).hasFDerivWithinAt) (lensPolarPower_injOn hk)]
  apply setLIntegral_congr_fun (measurableSet_lensPolarChart n)
  intro p hp
  dsimp only
  rw [abs_of_nonneg (lensPolarPowerDerivative_det_nonneg k hp), lensPolarPowerDerivative_det]

/-- Exact cancellation of the polar mass kernel and the joint powered-radius Jacobian. -/
theorem lensPolarPower_kernel_jacobian {n : ℕ} {k : ℕ} (hk : 1 ≤ k)
    {p : Fin n → ℝ × ℝ} (hp : p ∈ lensPolarChart n) :
    (∏ i, ENNReal.ofReal (p i).1) * ENNReal.ofReal (lensPowerRadialKernel k (lensPolarVector p)) =
      ENNReal.ofReal ((n.factorial : ℝ) * ((k : ℝ)/2)^n) *
        ENNReal.ofReal ((lensPolarPowerDerivative k p).det) := by
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (hp i (mem_univ i)).1.le),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => (hp i (mem_univ i)).1.le),
    ← ENNReal.ofReal_mul (by positivity), lensPolarVector_kernel, lensPolarPowerDerivative_det]
  congr 1
  calc
    _ = (n.factorial : ℝ) * ∏ i, (k : ℝ)^2 * ((p i).1^2)^(k-1) * (p i).1 := by
      rw [show (∏ i, (k : ℝ)^2 * ((p i).1^2)^(k-1) * (p i).1) =
          (∏ i, (k : ℝ)^2 * ((p i).1^2)^(k-1)) * ∏ i, (p i).1 from
          Finset.prod_mul_distrib]
      ring
    _ = (n.factorial : ℝ) * ∏ i, ((k : ℝ)/2) * (((2*k : ℕ) : ℝ) * (p i).1^(2*k-1)) := by
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      simpa only [mul_assoc] using lensRadial_power_jacobian hk (p i).1
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      ring

end
end Funk
