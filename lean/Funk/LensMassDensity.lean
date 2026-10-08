import Funk.LensPowerGram
import Funk.LensMassLower
import OAI.Analysis.Mahler.MassTarget

/-! Exact identification of the upstream mass density with the determinant of
our genuine lens derivative. The factorial and conjugate-index transpose are
retained. This is not yet a minor-sum or boundary-probability upper estimate. -/

open Set Matrix MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

theorem lensPower_upstream_jacobian_eq {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ)
    {z : LensComplexSpace n} (hz : z ∈ lensComplexDomain τ rows) :
    OAI.Mahler.jacobian (fun j => lensPowerComponent τ rows k j) z
      (fun i => EuclideanSpace.single i (1 : ℂ)) = lensPowerJacobian τ rows k z := by
  ext j i
  exact (lensPowerJacobian_eq_fderiv hτ0 hτ1 rows k hz j i).symm

theorem lensPower_upstream_sourceHessian_eq {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ)
    {z : LensComplexSpace n} (hz : z ∈ lensComplexDomain τ rows) :
    OAI.Mahler.sourceHessian (OAI.Mahler.energy (fun j => lensPowerComponent τ rows k j)) z
      (fun i => EuclideanSpace.single i (1 : ℂ)) =
      ((lensWeightedGram rows (lensPowerWeight τ rows k z)).map (algebraMap ℝ ℂ)).transpose := by
  unfold OAI.Mahler.sourceHessian
  rw [OAI.Mahler.complexHessian_energy_eq_gram _
    (fun j => (lensPowerComponent_analyticOnNhd hτ0 hτ1 rows k j) z hz),
    lensPower_upstream_jacobian_eq hτ0 hτ1 rows k hz, lensPowerJacobian_gram]

/-- The literal mass density is n! times the real weighted Gram determinant. -/
theorem lensPower_massDensity_eq_factorial_gram {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ)
    {z : LensComplexSpace n} (hz : z ∈ lensComplexDomain τ rows) :
    OAI.Mahler.massDensity (fun j => lensPowerComponent τ rows k j) z =
      (n.factorial : ℝ) * (lensWeightedGram rows (lensPowerWeight τ rows k z)).det := by
  unfold OAI.Mahler.massDensity
  rw [lensPower_upstream_sourceHessian_eq hτ0 hτ1 rows k hz, Matrix.det_transpose]
  have hd : ((lensWeightedGram rows (lensPowerWeight τ rows k z)).map
      (algebraMap ℝ ℂ)).det = ((lensWeightedGram rows (lensPowerWeight τ rows k z)).det : ℂ) :=
    (RingHom.map_det (algebraMap ℝ ℂ) (lensWeightedGram rows (lensPowerWeight τ rows k z))).symm
  rw [hd, Complex.ofReal_re]

theorem lensPower_massDensity_nonneg {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ)
    {z : LensComplexSpace n} (hz : z ∈ lensComplexDomain τ rows) :
    0 ≤ OAI.Mahler.massDensity (fun j => lensPowerComponent τ rows k j) z := by
  rw [lensPower_massDensity_eq_factorial_gram hτ0 hτ1 rows k hz]
  exact mul_nonneg (Nat.cast_nonneg _) (lensWeightedGram_det_nonneg rows
    (lensPowerWeight_nonneg τ rows k z))

/-- Equality holds on the exact sublevel; no density identity outside U is needed. -/
theorem lensPower_massIntegral_eq_gram_integral {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ) :
    OAI.Mahler.massIntegral (lensComplexDomain τ rows)
      (fun j => lensPowerComponent τ rows k j) =
      ∫⁻ z in lensComplexDomain τ rows ∩
        {z | OAI.Mahler.tau (fun j => lensPowerComponent τ rows k j) z < 1},
        ENNReal.ofReal ((n.factorial : ℝ) *
          (lensWeightedGram rows (lensPowerWeight τ rows k z)).det) := by
  unfold OAI.Mahler.massIntegral
  apply setLIntegral_congr_fun
  · have ht : OAI.Mahler.tau (fun j => lensPowerComponent τ rows k j) =
        lensPowerEnergy τ rows k := funext (lensPower_upstream_tau_eq τ rows k)
    rw [ht]
    exact ((lensPowerEnergy_continuousOn hτ0 hτ1 rows k).isOpen_inter_preimage
      (isOpen_lensComplexDomain τ rows) isOpen_Iio).measurableSet
  · intro z hz
    exact congrArg ENNReal.ofReal (lensPower_massDensity_eq_factorial_gram hτ0 hτ1 rows k hz.1)

/-- The actual weighted-Gram integral has the exact full mass lower bound. -/
theorem lensPower_gramIntegral_lower {n m : ℕ} (hn : 1 ≤ n) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n)
    (hK : IsCompact (stripBody rows)) {k : ℕ} (hk : 1 ≤ k) :
    ENNReal.ofReal ((Real.pi * (k : ℝ))^n) ≤
      ∫⁻ z in lensComplexDomain τ rows ∩ {z | lensPowerEnergy τ rows k z < 1},
        ENNReal.ofReal ((n.factorial : ℝ) *
          (lensWeightedGram rows (lensPowerWeight τ rows k z)).det) := by
  have h := lensPower_massIntegral_lower hn hτ0 hτ1 rows hK hk
  rw [lensPower_massIntegral_eq_gram_integral hτ0 hτ1 rows k] at h
  simpa only [lensPower_upstream_tau_eq] using h

end
end Funk
