import Funk.LensConformalCoordinates

/-! Actual basis/conformal parametrization of the energy sublevel. The chosen
basis is an existing unsignedBasisIndices member. Domain equality, Jacobian
and cancellation are mathematical obligations proved here, not input premises. -/

open Set Matrix MeasureTheory Metric
open scoped BigOperators ENNReal

namespace Funk
noncomputable section

def lensBasisParametrization {n : ℕ} (τ : ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (u : LensComplexSpace n) : LensComplexSpace n :=
  lensBasisMap B⁻¹ (lensCoordinateForward τ u)

def lensBasisParametrizationDerivative {n : ℕ} (τ : ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (u : LensComplexSpace n) : LensComplexSpace n →L[ℂ] LensComplexSpace n :=
  (lensBasisMap B⁻¹).comp (lensCoordinateForwardDerivative τ u)

theorem lensBasisParametrization_hasFDerivAt {n : ℕ} (τ : ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) {u : LensComplexSpace n} (hu : u ∈ lensOpenPolydisk n) :
    HasFDerivAt (lensBasisParametrization τ B) (lensBasisParametrizationDerivative τ B u) u :=
  (lensBasisMap B⁻¹).hasFDerivAt.comp u (lensCoordinateForward_hasFDerivAt τ hu)

theorem lensBasisParametrization_continuousOn {n : ℕ} (τ : ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    ContinuousOn (lensBasisParametrization τ B) (lensOpenPolydisk n) :=
  (lensBasisMap B⁻¹).continuous.comp_continuousOn (lensCoordinateForward_continuousOn τ)

theorem lensBasisParametrization_real_det {n : ℕ} (τ : ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (u : LensComplexSpace n) :
    ((lensBasisParametrizationDerivative τ B u).restrictScalars ℝ).det =
      B⁻¹.det ^ 2 * ∏ i, Complex.normSq (deriv (tiltedLens τ) (u i)) := by
  change (((lensBasisMap B⁻¹).toLinearMap.comp
    (lensCoordinateForwardDerivative τ u).toLinearMap).restrictScalars ℝ).det = _
  rw [LinearMap.restrictScalars_comp, LinearMap.det_comp]
  change ((lensBasisMap B⁻¹).restrictScalars ℝ).det *
    ((lensCoordinateForwardDerivative τ u).restrictScalars ℝ).det = _
  rw [lensBasisMap_real_det, lensCoordinateForward_real_det]

theorem lensBasisParametrization_selected_row {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.det ≠ 0) (τ : ℝ) (u : LensComplexSpace n) (i : Fin n) :
    lensComplexRow (B i) (lensBasisParametrization τ B u) = tiltedLens τ (u i) := by
  rw [← lensBasisMap_apply, lensBasisParametrization, lensBasisMap_inverse_right hB]
  rfl

theorem lensBasisParametrization_injOn {n : ℕ} {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.det ≠ 0) :
    InjOn (lensBasisParametrization τ B) (lensOpenPolydisk n) := by
  intro u hu v hv he
  apply lensCoordinateForward_injOn hτ0 hτ1 hu hv
  have hi : Function.Injective (lensBasisMap B⁻¹) :=
    Function.HasLeftInverse.injective ⟨lensBasisMap B, lensBasisMap_inverse_right hB⟩
  exact hi he

/-- Literal pulled-back actual sublevel, with the unit polydisk retained. -/
def lensBasisPowerDomain {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n) (k : ℕ)
    (s : Fin n → Fin m) : Set (LensComplexSpace n) :=
  lensOpenPolydisk n ∩ (lensBasisParametrization τ (Matrix.of fun i => rows (s i))) ⁻¹'
    (lensComplexDomain τ rows ∩ {z | lensPowerEnergy τ rows k z < 1})

theorem isOpen_lensBasisPowerDomain {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ) (s : Fin n → Fin m) :
    IsOpen (lensBasisPowerDomain τ rows k s) :=
  (lensBasisParametrization_continuousOn τ _).isOpen_inter_preimage (isOpen_lensOpenPolydisk n)
    ((lensPowerEnergy_continuousOn hτ0 hτ1 rows k).isOpen_inter_preimage
      (isOpen_lensComplexDomain τ rows) isOpen_Iio)

/-- Exact image of the actual pulled-back domain, without a geometric cover premise. -/
theorem lensBasisPowerDomain_image {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ)
    {s : Fin n → Fin m} (hs : s ∈ unsignedBasisIndices rows) :
    lensBasisParametrization τ (Matrix.of fun i => rows (s i)) '' lensBasisPowerDomain τ rows k s =
      lensComplexDomain τ rows ∩ {z | lensPowerEnergy τ rows k z < 1} := by
  let B := Matrix.of fun i => rows (s i)
  have hB : B.det ≠ 0 := ((mem_unsignedBasisIndices rows s).mp hs).2
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hu.2
  · intro hz
    let u : LensComplexSpace n := WithLp.toLp 2
      (fun i => tiltedLensInverse τ (lensComplexRow (rows (s i)) z))
    have hu : u ∈ lensOpenPolydisk n := fun i => tiltedLensInverse_mem_ball hτ0 hτ1 (hz.1 (s i))
    have hF : lensCoordinateForward τ u = lensBasisMap B z := by
      ext i
      exact (tiltedLensInverse_right hτ0 hτ1 (hz.1 (s i))).trans
        (lensBasisMap_apply B z i).symm
    have he : lensBasisParametrization τ B u = z := by
      rw [lensBasisParametrization, hF, lensBasisMap_inverse_left hB]
    exact ⟨u, ⟨hu, by
      change lensBasisParametrization τ B u ∈
        lensComplexDomain τ rows ∩ {z | lensPowerEnergy τ rows k z < 1}
      rw [he]
      exact hz⟩, he⟩

/-- Each inverse-coordinate weight cancels its actual forward conformal Jacobian. -/
theorem lensPowerWeight_forward_cancellation {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ)
    {s : Fin n → Fin m} (hs : s ∈ unsignedBasisIndices rows)
    {u : LensComplexSpace n} (hu : u ∈ lensOpenPolydisk n) (i : Fin n) :
    lensPowerWeight τ rows k (lensBasisParametrization τ (Matrix.of fun l => rows (s l)) u) (s i) *
      Complex.normSq (deriv (tiltedLens τ) (u i)) =
      (k : ℝ)^2 * Complex.normSq (u i) ^ (k-1) := by
  have hB := ((mem_unsignedBasisIndices rows s).mp hs).2
  have hr := lensBasisParametrization_selected_row hB τ u i
  change lensComplexRow (rows (s i))
    (lensBasisParametrization τ (Matrix.of fun l => rows (s l)) u) = tiltedLens τ (u i) at hr
  have hin : tiltedLens τ (u i) ∈ interior (lensGraphBody τ) :=
    tiltedLens_mapsTo_ball_interior hτ0 hτ1 (hu i)
  rw [lensPowerWeight_explicit, hr, tiltedLensInverse_left hτ0 hτ1 (hu i),
    (hasDerivAt_tiltedLensInverse hτ0 hτ1 hin).deriv,
    tiltedLensInverse_left hτ0 hτ1 (hu i), map_inv₀]
  have hd : Complex.normSq (deriv (tiltedLens τ) (u i)) ≠ 0 :=
    Complex.normSq_eq_zero.not.mpr (tiltedLens_deriv_ne_zero hτ0 hτ1 (mem_ball_zero_iff.mp (hu i)))
  field_simp

/-- Exact cancellation of the real basis determinant and its inverse. -/
theorem lensBasis_inverse_det_square_cancel {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.det ≠ 0) : B⁻¹.det ^ 2 * B.det ^ 2 = 1 := by
  rw [Matrix.det_nonsing_inv]
  rw [Ring.inverse_eq_inv]
  field_simp

end
end Funk
