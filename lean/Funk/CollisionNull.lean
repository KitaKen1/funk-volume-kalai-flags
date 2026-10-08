import Funk.CollisionCurvature
import Funk.CoordinateSliceNull
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! The actual collision residual is null on the strict-height domain whenever
its row coefficients have two nonzero entries. This uses regular real zeros
and coordinate Fubini, with no analytic boundary extension. -/

open Set Matrix MeasureTheory

namespace Funk
noncomputable section

def collisionHeightDomain {n : ℕ} (coeff : Space n) : Set (Space n) :=
  {t | (∀ k, t k ∈ Ioo (-1) 1) ∧ dotProduct coeff t ∈ Ioo (-1) 1}

theorem measurableSet_collisionHeightDomain {n : ℕ} (coeff : Space n) :
    MeasurableSet (collisionHeightDomain coeff) := by
  have h1 : MeasurableSet {t : Space n | ∀ k, t k ∈ Ioo (-1) 1} := by
    rw [ofPred_forall]
    exact MeasurableSet.iInter (fun k => measurableSet_Ioo.preimage (measurable_pi_apply k))
  apply h1.inter
  apply measurableSet_Ioo.preimage
  unfold dotProduct
  fun_prop

theorem measurable_lensBranchProfileSlope (τ : ℝ) (b : Bool) :
    Measurable (lensBranchProfileSlope τ b) := by
  cases b
  · exact (measurable_deriv (lensProfile τ)).comp measurable_neg
  · exact measurable_deriv (lensProfile τ)

theorem measurable_branchCollisionSlope {n : ℕ} (τ : ℝ) (b : Fin n → Bool)
    (σ : Bool) (coeff : Space n) (i : Fin n) :
    Measurable (branchCollisionSlope τ b σ coeff i) := by
  unfold branchCollisionSlope
  apply Measurable.const_mul
  apply Measurable.sub
  · exact (measurable_lensBranchProfileSlope τ (b i)).comp (measurable_pi_apply i)
  · apply (measurable_lensBranchProfileSlope τ σ).comp
    unfold dotProduct
    fun_prop

/-- Nullity is proved for the actual residual over all dimensions and parameters. -/
theorem volume_collision_residual_zero {n : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (b : Fin n → Bool) (σ : Bool)
    (coeff : Space n) (i j : Fin n) (hij : i ≠ j)
    (hi : coeff i ≠ 0) (hj : coeff j ≠ 0) :
    volume {t ∈ collisionHeightDomain coeff | branchCollisionResidual τ b σ coeff t = 0} = 0 := by
  apply volume_zero_of_transverse_coordinate_derivatives
    (branchCollisionResidual τ b σ coeff) (branchCollisionSlope τ b σ coeff i)
    (measurable_branchCollisionResidual τ b σ coeff)
    (measurable_branchCollisionSlope τ b σ coeff i)
    (collisionHeightDomain coeff) (measurableSet_collisionHeightDomain coeff) i j
  · intro t ht
    exact hasDerivAt_branchCollisionResidual_update hτ0 hτ1 b σ coeff t i (ht.1 i) ht.2
  · intro t ht
    refine ⟨_, hasDerivAt_branchCollisionSlope_update hτ0 hτ1 b σ coeff t i j hij ht.2, ?_⟩
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hi) hj)
      (lensBranchProfileCurvature_ne_zero hτ0 hτ1 σ ht.2)

theorem volume_basisMap_preimage_null {n : ℕ}
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.det ≠ 0) {s : Set (Space n)}
    (hs : volume s = 0) : volume (basisMap B ⁻¹' s) = 0 := by
  have hdet : (basisMap B).det ≠ 0 := by simpa only [basisMap_det] using hB
  exact (Measure.ContinuousLinearMap.quasiMeasurePreserving volume (basisMap B) hdet).preimage_null hs

end
end Funk
