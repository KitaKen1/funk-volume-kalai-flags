import Funk.LensBasisCoordinates

/-! Coordinatewise application of the actual tilted lens on the unit polydisk.
The real Jacobian is the product of norm-square complex derivatives. -/

open Set Matrix MeasureTheory Metric
open scoped BigOperators ENNReal

namespace Funk
noncomputable section

def lensOpenPolydisk (n : ℕ) : Set (LensComplexSpace n) :=
  {u | ∀ i, u i ∈ ball (0 : ℂ) 1}

theorem isOpen_lensOpenPolydisk (n : ℕ) : IsOpen (lensOpenPolydisk n) := by
  unfold lensOpenPolydisk
  rw [ofPred_forall]
  exact isOpen_iInter_of_finite (fun i => isOpen_ball.preimage (EuclideanSpace.proj i).continuous)

/-- Actual forward conformal map, coordinate by coordinate. -/
def lensCoordinateForward {n : ℕ} (τ : ℝ) (u : LensComplexSpace n) : LensComplexSpace n :=
  WithLp.toLp 2 (fun i => tiltedLens τ (u i))

def lensCoordinateForwardDerivative {n : ℕ} (τ : ℝ) (u : LensComplexSpace n) :
    LensComplexSpace n →L[ℂ] LensComplexSpace n :=
  lensMatrixMap (diagonal (fun i => deriv (tiltedLens τ) (u i)))

theorem lensCoordinateForwardDerivative_apply {n : ℕ} (τ : ℝ)
    (u v : LensComplexSpace n) (i : Fin n) :
    lensCoordinateForwardDerivative τ u v i = deriv (tiltedLens τ) (u i) * v i := by
  rw [lensCoordinateForwardDerivative, lensMatrixMap_apply]
  simp [Matrix.diagonal_apply]

set_option backward.isDefEq.respectTransparency false in
theorem lensCoordinateForward_hasFDerivAt {n : ℕ} (τ : ℝ)
    {u : LensComplexSpace n} (hu : u ∈ lensOpenPolydisk n) :
    HasFDerivAt (lensCoordinateForward τ) (lensCoordinateForwardDerivative τ u) u := by
  have hF (i : Fin n) : HasDerivAt (tiltedLens τ) (deriv (tiltedLens τ) (u i)) (u i) :=
    ((tiltedLens_diffContOnCl τ).differentiableOn.differentiableAt
      (isOpen_ball.mem_nhds (hu i))).hasDerivAt
  have hc (i : Fin n) : HasFDerivAt (fun v : LensComplexSpace n => tiltedLens τ (v i))
      ((ContinuousLinearMap.toSpanSingleton ℂ (deriv (tiltedLens τ) (u i))).comp
        (EuclideanSpace.proj i)) u := by
    have hp : HasFDerivAt (𝕜 := ℂ) (fun v : LensComplexSpace n => v i)
        (EuclideanSpace.proj (𝕜 := ℂ) i) u := by
      simpa only [EuclideanSpace.coe_proj] using
        (EuclideanSpace.proj (𝕜 := ℂ) i).hasFDerivAt (x := u)
    have hd := (hF i).hasFDerivAt.comp u hp
    simpa only [Function.comp_def] using hd
  have hpi := hasFDerivAt_pi.mpr hc
  have h := (EuclideanSpace.equiv (Fin n) ℂ).symm.toContinuousLinearMap.hasFDerivAt.comp u hpi
  have hD : lensCoordinateForwardDerivative τ u =
      (EuclideanSpace.equiv (Fin n) ℂ).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi fun i =>
          (ContinuousLinearMap.toSpanSingleton ℂ (deriv (tiltedLens τ) (u i))).comp
            (EuclideanSpace.proj i)) := by
    ext v i
    rw [lensCoordinateForwardDerivative_apply]
    change deriv (tiltedLens τ) (u i) * v i = v i * deriv (tiltedLens τ) (u i)
    exact mul_comm _ _
  rw [hD]
  exact h

theorem lensCoordinateForward_continuousOn {n : ℕ} (τ : ℝ) :
    ContinuousOn (lensCoordinateForward τ) (lensOpenPolydisk n) :=
  fun _ hu => (lensCoordinateForward_hasFDerivAt τ hu).continuousAt.continuousWithinAt

theorem lensCoordinateForward_real_det {n : ℕ} (τ : ℝ) (u : LensComplexSpace n) :
    ((lensCoordinateForwardDerivative τ u).restrictScalars ℝ).det =
      ∏ i, Complex.normSq (deriv (tiltedLens τ) (u i)) := by
  rw [lensCoordinateForwardDerivative, lensMatrixMap_real_det, Matrix.det_diagonal, map_prod]

theorem lensCoordinateForward_injOn {n : ℕ} {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    InjOn (lensCoordinateForward τ) (lensOpenPolydisk n) := by
  intro u hu v hv he
  ext i
  apply tiltedLens_injOn_ball hτ0 hτ1 (hu i) (hv i)
  exact congrArg (fun z : LensComplexSpace n => z i) he

/-- Exact nonnegative integral transformation on any measurable polydisk subset. -/
theorem lintegral_lensCoordinateForward_image {n : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) {S : Set (LensComplexSpace n)} (hS : MeasurableSet S)
    (hsub : S ⊆ lensOpenPolydisk n) (g : LensComplexSpace n → ℝ≥0∞) :
    ∫⁻ w in lensCoordinateForward τ '' S, g w =
      ∫⁻ u in S, ENNReal.ofReal (∏ i, Complex.normSq (deriv (tiltedLens τ) (u i))) *
        g (lensCoordinateForward τ u) := by
  simpa only [lensCoordinateForward_real_det,
    abs_of_nonneg (Finset.prod_nonneg fun _ _ => Complex.normSq_nonneg _)] using
    lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure (LensComplexSpace n)) hS
      (fun _ hu => ((lensCoordinateForward_hasFDerivAt τ (hsub hu)).restrictScalars ℝ).hasFDerivWithinAt)
      ((lensCoordinateForward_injOn hτ0 hτ1).mono hsub) g

end
end Funk
