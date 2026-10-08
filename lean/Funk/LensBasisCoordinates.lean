import Funk.LensMassMinorIntegral
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Complex

/-! The actual complexification of a real basis matrix, with exact Euclidean
real Jacobian and inverse. The determinant factor is the square of the real
determinant, with no volume-normalization surrogate. -/

open Set Matrix MeasureTheory
open scoped BigOperators ENNReal

namespace Funk
noncomputable section

/-- Euclidean complex coordinates for an arbitrary square complex matrix. -/
def lensMatrixMap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    LensComplexSpace n →L[ℂ] LensComplexSpace n :=
  (EuclideanSpace.equiv (Fin n) ℂ).symm.toContinuousLinearMap.comp
    ((Matrix.toLin' A).toContinuousLinearMap.comp
      (EuclideanSpace.equiv (Fin n) ℂ).toContinuousLinearMap)

theorem lensMatrixMap_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z : LensComplexSpace n) (i : Fin n) : lensMatrixMap A z i = ∑ j, A i j * z j := rfl

theorem lensMatrixMap_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (lensMatrixMap A).det = A.det := by
  change LinearMap.det (((EuclideanSpace.equiv (Fin n) ℂ).symm :
      (Fin n → ℂ) →ₗ[ℂ] LensComplexSpace n).comp
        ((Matrix.toLin' A).comp (EuclideanSpace.equiv (Fin n) ℂ).toLinearMap)) = _
  simpa only [LinearMap.det_toLin', ContinuousLinearEquiv.toLinearEquiv_symm,
    LinearEquiv.symm_symm] using LinearMap.det_conj (Matrix.toLin' A)
    (EuclideanSpace.equiv (Fin n) ℂ).symm.toLinearEquiv

/-- Restricting a complex derivative to real scalars gives its norm-square determinant. -/
theorem lensMatrixMap_real_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ((lensMatrixMap A).restrictScalars ℝ).det = Complex.normSq A.det := by
  change ((lensMatrixMap A).toLinearMap.restrictScalars ℝ).det = _
  rw [LinearMap.det_restrictScalars, ← ContinuousLinearMap.det, lensMatrixMap_det,
    Algebra.norm_complex_apply]

/-- Complexification of the real row basis, in the exact mass-space convention. -/
def lensBasisMap {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    LensComplexSpace n →L[ℂ] LensComplexSpace n :=
  lensMatrixMap (B.map (algebraMap ℝ ℂ))

theorem lensBasisMap_apply {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (z : LensComplexSpace n) (i : Fin n) :
    lensBasisMap B z i = lensComplexRow (B i) z := by
  rw [lensBasisMap, lensMatrixMap_apply, lensComplexRow_apply]
  rfl

theorem lensBasisMap_re {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (z : LensComplexSpace n) (i : Fin n) :
    (lensBasisMap B z i).re = basisMap B (fun j => (z j).re) i := by
  rw [lensBasisMap_apply, lensComplexRow_re]
  rfl

theorem lensBasisMap_im {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (z : LensComplexSpace n) (i : Fin n) :
    (lensBasisMap B z i).im = basisMap B (fun j => (z j).im) i := by
  rw [lensBasisMap_apply, lensComplexRow_im]
  rfl

theorem lensBasisMap_real_det {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    ((lensBasisMap B).restrictScalars ℝ).det = B.det ^ 2 := by
  rw [lensBasisMap, lensMatrixMap_real_det]
  have hd : (B.map (algebraMap ℝ ℂ)).det = (B.det : ℂ) :=
    (RingHom.map_det (algebraMap ℝ ℂ) B).symm
  rw [hd, Complex.normSq_ofReal]
  ring

theorem lensBasisMap_inverse_left {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.det ≠ 0) (z : LensComplexSpace n) : lensBasisMap B⁻¹ (lensBasisMap B z) = z := by
  ext i
  apply Complex.ext
  · simpa only [lensBasisMap_re] using congrFun (basisMap_inverse_left hB (fun j => (z j).re)) i
  · simpa only [lensBasisMap_im] using congrFun (basisMap_inverse_left hB (fun j => (z j).im)) i

theorem lensBasisMap_inverse_right {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.det ≠ 0) (z : LensComplexSpace n) : lensBasisMap B (lensBasisMap B⁻¹ z) = z := by
  ext i
  apply Complex.ext
  · simpa only [lensBasisMap_re] using congrFun (basisMap_inverse_right hB (fun j => (z j).re)) i
  · simpa only [lensBasisMap_im] using congrFun (basisMap_inverse_right hB (fun j => (z j).im)) i

theorem lensBasisMap_injective {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.det ≠ 0) : Function.Injective (lensBasisMap B) :=
  Function.HasLeftInverse.injective ⟨lensBasisMap B⁻¹, lensBasisMap_inverse_left hB⟩

theorem measurableSet_lensBasisMap_image {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.det ≠ 0) {S : Set (LensComplexSpace n)} (hS : MeasurableSet S) :
    MeasurableSet (lensBasisMap B '' S) :=
  measurable_image_of_fderivWithin hS
    (fun _ _ => ((lensBasisMap B).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt)
    (lensBasisMap_injective hB).injOn

/-- Exact real-volume change of variables for every measurable actual-domain subset. -/
theorem lintegral_lensBasisMap_image {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.det ≠ 0) {S : Set (LensComplexSpace n)} (hS : MeasurableSet S)
    (g : LensComplexSpace n → ℝ≥0∞) :
    ∫⁻ w in lensBasisMap B '' S, g w =
      ∫⁻ z in S, ENNReal.ofReal (B.det ^ 2) * g (lensBasisMap B z) := by
  simpa only [lensBasisMap_real_det, abs_of_nonneg (sq_nonneg B.det),
    ContinuousLinearMap.coe_restrictScalars'] using
    lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure (LensComplexSpace n)) hS
      (fun _ _ => ((lensBasisMap B).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt)
      (lensBasisMap_injective hB).injOn g

/-- The inverse Euclidean interpolant has the same real and imaginary witnesses. -/
theorem lensBasisMap_inverse_boundaryWitness {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (w : LensComplexSpace n) :
    (fun i => (lensBasisMap B⁻¹ w i).re) = boundaryRealWitness B (fun i => w i) ∧
    (fun i => (lensBasisMap B⁻¹ w i).im) = boundaryImagWitness B (fun i => w i) := by
  exact ⟨funext (lensBasisMap_re B⁻¹ w), funext (lensBasisMap_im B⁻¹ w)⟩

end
end Funk
