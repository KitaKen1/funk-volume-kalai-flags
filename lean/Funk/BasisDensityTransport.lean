import Funk.RowDensityMeasure
import Mathlib.MeasureTheory.Function.Jacobian

/-! Basis matrices transport genuine geometric boundary probabilities to
integrals of actual polar-simplex volumes. A measurable feasibility region is
an explicit input; no unproved feasibility or packing statement is hidden. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

def basisMap {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : Space n →L[ℝ] Space n :=
  (Matrix.toLin' B).toContinuousLinearMap

theorem basisMap_apply {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (X : Space n) (i : Fin n) :
    basisMap B X i = dotProduct (B i) X := rfl

theorem basisMap_det {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    (basisMap B).det = B.det := by
  rw [basisMap, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin']

theorem basisMap_injective {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.det ≠ 0) :
    Function.Injective (basisMap B) := by
  change Function.Injective B.mulVec
  exact Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det B).mpr
    (isUnit_iff_ne_zero.mpr hB))

theorem measurableSet_basisMap_image {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.det ≠ 0) {s : Set (Space n)} (hs : MeasurableSet s) :
    MeasurableSet (basisMap B '' s) :=
  measurable_image_of_fderivWithin hs
    (fun _ _ => (basisMap B).hasFDerivAt.hasFDerivWithinAt) (basisMap_injective hB).injOn

theorem lintegral_basisMap_image {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.det ≠ 0) {s : Set (Space n)} (hs : MeasurableSet s) (g : Space n → ℝ≥0∞) :
    ∫⁻ t in basisMap B '' s, g t =
      ∫⁻ X in s, ENNReal.ofReal |B.det| * g (basisMap B X) := by
  simpa only [basisMap_det] using lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (volume : Measure (Space n)) hs
    (fun _ _ => (basisMap B).hasFDerivAt.hasFDerivWithinAt) (basisMap_injective hB).injOn g

theorem basisMap_image_subset_cube {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    {s : Set (Space n)} (hs : s ⊆ stripBody B) :
    basisMap B '' s ⊆ coordinateCube n := by
  rintro _ ⟨X, hX, rfl⟩
  exact (mem_coordinateCube _).mpr (hs hX)

/-- A geometric event on actual sampled boundary points. -/
def basisBoundaryEvent {n : ℕ} (τ : ℝ) (b : Fin n → Bool)
    (B : Matrix (Fin n) (Fin n) ℝ) (s : Set (Space n)) : Set (Fin n → ℂ) :=
  lensBoundaryRowCoordinates n τ ⁻¹' (rowSignSet b ∩ rowHeights ⁻¹' (basisMap B '' s))

theorem measurableSet_basisBoundaryEvent {n : ℕ} (τ : ℝ) (b : Fin n → Bool)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.det ≠ 0)
    {s : Set (Space n)} (hs : MeasurableSet s) :
    MeasurableSet (basisBoundaryEvent τ b B s) :=
  (measurable_lensBoundaryRowCoordinates n τ)
    ((measurableSet_rowSignSet b).inter
      ((measurable_rowHeights n) (measurableSet_basisMap_image hB hs)))

theorem basisBoundaryEvent_probability_density {n : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (b : Fin n → Bool)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.det ≠ 0)
    {s : Set (Space n)} (hs : MeasurableSet s) (hsub : s ⊆ stripBody B) :
    lensBoundaryRows n τ (basisBoundaryEvent τ b B s) =
      ∫⁻ X in s, ENNReal.ofReal |B.det| * rowDensity n τ b (basisMap B X) := by
  rw [basisBoundaryEvent, lensBoundaryRows_region hτ0 hτ1 b (measurableSet_basisMap_image hB hs),
    inter_eq_left.mpr (basisMap_image_subset_cube B hsub), lintegral_basisMap_image hB hs]

def basisVolumeFactor (n : ℕ) (τ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((τ / (4 * Real.artanh τ)) ^ n * (n.factorial : ℝ))

theorem basisVolumeFactor_pos (n : ℕ) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    0 < basisVolumeFactor n τ := by
  apply ENNReal.ofReal_pos.mpr
  exact mul_pos (pow_pos (div_pos hτ0 (mul_pos (by norm_num)
    (Real.artanh_pos ⟨hτ0, hτ1⟩))) _) (by exact_mod_cast n.factorial_pos)

theorem density_mul_det_eq_simplex_volume {n : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (b : Fin n → Bool)
    (B : Matrix (Fin n) (Fin n) ℝ) {X : Space n} (hX : X ∈ stripBody B) :
    ENNReal.ofReal |B.det| * rowDensity n τ b (basisMap B X) =
      basisVolumeFactor n τ * volume (rowSimplex (vertexMatrix τ (fun i => branchSign (b i)) B X)) := by
  have ha : 0 < Real.artanh τ := Real.artanh_pos ⟨hτ0, hτ1⟩
  have hp (i : Fin n) : 0 ≤ branchDensity τ (branchSign (b i)) (dotProduct (B i) X) :=
    (branchDensity_pos hτ0 hτ1 (branchSign_cases _) (hX i)).le
  simp only [rowDensity, basisMap_apply]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => hp i),
    ← ENNReal.ofReal_mul (abs_nonneg _), mul_comm,
    density_product_mul_abs_det hτ0.le hτ1 (fun i => branchSign_cases (b i)) hX,
    volume_rowSimplex, basisVolumeFactor, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

theorem measurable_vertexSimplex_volume {n : ℕ} (τ : ℝ) (b : Fin n → Bool)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    Measurable (fun X => volume (rowSimplex (vertexMatrix τ (fun i => branchSign (b i)) B X))) := by
  simp only [volume_rowSimplex, det_vertexMatrix]
  unfold dotProduct
  fun_prop

/-- Exact probability/volume identity, for every measurable feasible subregion. -/
theorem basisBoundaryEvent_probability_volume {n : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (b : Fin n → Bool)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.det ≠ 0)
    {s : Set (Space n)} (hs : MeasurableSet s) (hsub : s ⊆ stripBody B) :
    lensBoundaryRows n τ (basisBoundaryEvent τ b B s) =
      basisVolumeFactor n τ * ∫⁻ X in s,
        volume (rowSimplex (vertexMatrix τ (fun i => branchSign (b i)) B X)) := by
  rw [basisBoundaryEvent_probability_density hτ0 hτ1 b hB hs hsub,
    ← lintegral_const_mul _ (measurable_vertexSimplex_volume τ b B)]
  apply setLIntegral_congr_fun hs
  intro X hX
  exact density_mul_det_eq_simplex_volume hτ0 hτ1 b B (hsub hX)

end
end Funk
