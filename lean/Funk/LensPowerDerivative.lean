import Funk.LensPowerRegular
import Mathlib.Analysis.Matrix.PosDef

/-! The literal holomorphic derivative and coordinate Jacobian of the actual
Euclidean lens power map. All k, g and g-prime factors are retained. -/

open Set Complex Matrix
open scoped BigOperators

namespace Funk
noncomputable section

/-- The scalar factor in the derivative of the kth inverse-coordinate power. -/
def lensPowerRowFactor {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n) (k : ℕ)
    (z : LensComplexSpace n) (j : Fin m) : ℂ :=
  (k : ℂ) * tiltedLensInverse τ (lensComplexRow (rows j) z) ^ (k-1) *
    deriv (tiltedLensInverse τ) (lensComplexRow (rows j) z)

theorem lensPowerComponent_hasFDerivAt {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ) (j : Fin m)
    {z : LensComplexSpace n} (hz : z ∈ lensComplexDomain τ rows) :
    HasFDerivAt (lensPowerComponent τ rows k j)
      (lensPowerRowFactor τ rows k z j • lensComplexRow (rows j)) z := by
  have hg : HasDerivAt (tiltedLensInverse τ)
      (deriv (tiltedLensInverse τ) (lensComplexRow (rows j) z))
      (lensComplexRow (rows j) z) :=
    (hasDerivAt_tiltedLensInverse hτ0 hτ1 (hz j)).differentiableAt.hasDerivAt
  have hd := (hg.pow k).hasFDerivAt.comp z (lensComplexRow (rows j)).hasFDerivAt
  have hc : (ContinuousLinearMap.toSpanSingleton ℂ (lensPowerRowFactor τ rows k z j)).comp
      (lensComplexRow (rows j)) = lensPowerRowFactor τ rows k z j • lensComplexRow (rows j) := by
    ext v
    simp [smul_eq_mul, mul_comm]
  change HasFDerivAt (fun x => tiltedLensInverse τ (lensComplexRow (rows j) x)^k)
    (lensPowerRowFactor τ rows k z j • lensComplexRow (rows j)) z
  rw [← hc]
  simpa only [Function.comp_def, Pi.pow_apply, lensPowerRowFactor] using hd

/-- The actual Euclidean vector derivative, with the same codomain norm. -/
def lensPowerDerivative {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n) (k : ℕ)
    (z : LensComplexSpace n) : LensComplexSpace n →L[ℂ] LensComplexSpace m :=
  (EuclideanSpace.equiv (Fin m) ℂ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j => lensPowerRowFactor τ rows k z j • lensComplexRow (rows j))

theorem lensPowerMap_hasFDerivAt {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ)
    {z : LensComplexSpace n} (hz : z ∈ lensComplexDomain τ rows) :
    HasFDerivAt (lensPowerMap τ rows k) (lensPowerDerivative τ rows k z) z := by
  exact (EuclideanSpace.equiv (Fin m) ℂ).symm.toContinuousLinearMap.hasFDerivAt.comp z
    (hasFDerivAt_pi.mpr fun j => lensPowerComponent_hasFDerivAt hτ0 hτ1 rows k j hz)

/-- Coordinate matrix of the genuine complex derivative. -/
def lensPowerJacobian {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n) (k : ℕ)
    (z : LensComplexSpace n) : Matrix (Fin m) (Fin n) ℂ :=
  fun j i => lensPowerRowFactor τ rows k z j * (rows j i : ℂ)

theorem lensComplexRow_single {n : ℕ} (row : Space n) (i : Fin n) :
    lensComplexRow row (EuclideanSpace.single i (1 : ℂ)) = (row i : ℂ) := by
  simp [lensComplexRow_apply]

theorem lensPowerDerivative_single {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n)
    (k : ℕ) (z : LensComplexSpace n) (j : Fin m) (i : Fin n) :
    lensPowerDerivative τ rows k z (EuclideanSpace.single i (1 : ℂ)) j =
      lensPowerJacobian τ rows k z j i := by
  change (lensPowerRowFactor τ rows k z j • lensComplexRow (rows j))
    (EuclideanSpace.single i (1 : ℂ)) = lensPowerJacobian τ rows k z j i
  simp only [_root_.smul_apply, smul_eq_mul, lensComplexRow_single, lensPowerJacobian]

/-- The matrix is computed from fderiv, not a separately supplied Jacobian. -/
theorem lensPowerJacobian_eq_fderiv {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ)
    {z : LensComplexSpace n} (hz : z ∈ lensComplexDomain τ rows) (j : Fin m) (i : Fin n) :
    lensPowerJacobian τ rows k z j i =
      fderiv ℂ (lensPowerComponent τ rows k j) z (EuclideanSpace.single i (1 : ℂ)) := by
  rw [(lensPowerComponent_hasFDerivAt hτ0 hτ1 rows k j hz).fderiv]
  simp only [_root_.smul_apply, smul_eq_mul, lensComplexRow_single, lensPowerJacobian]

/-- Exact nonnegative derivative weight, in natural rather than real exponents. -/
def lensPowerWeight {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n) (k : ℕ)
    (z : LensComplexSpace n) (j : Fin m) : ℝ := normSq (lensPowerRowFactor τ rows k z j)

theorem lensPowerWeight_nonneg {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n) (k : ℕ)
    (z : LensComplexSpace n) (j : Fin m) : 0 ≤ lensPowerWeight τ rows k z j := normSq_nonneg _

theorem lensPowerWeight_explicit {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n) (k : ℕ)
    (z : LensComplexSpace n) (j : Fin m) :
    lensPowerWeight τ rows k z j = (k : ℝ)^2 *
      normSq (tiltedLensInverse τ (lensComplexRow (rows j) z)) ^ (k-1) *
      normSq (deriv (tiltedLensInverse τ) (lensComplexRow (rows j) z)) := by
  simp only [lensPowerWeight, lensPowerRowFactor, normSq_mul, normSq_natCast, map_pow, pow_two]

theorem lensPowerWeight_eq_inv_forward_deriv {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ)
    {z : LensComplexSpace n} (hz : z ∈ lensComplexDomain τ rows) (j : Fin m) :
    lensPowerWeight τ rows k z j = (k : ℝ)^2 *
      normSq (tiltedLensInverse τ (lensComplexRow (rows j) z)) ^ (k-1) *
      normSq ((deriv (tiltedLens τ) (tiltedLensInverse τ (lensComplexRow (rows j) z)))⁻¹) := by
  rw [lensPowerWeight_explicit, (hasDerivAt_tiltedLensInverse hτ0 hτ1 (hz j)).deriv]

end
end Funk
