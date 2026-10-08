import Funk.Polar
import Funk.BranchDensity
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The determinant part of the proposed simplex-volume formula.
This file concerns actual matrices of the certified vertices. Convex-hull
volume is connected in SimplexCertificate, and geometric event integration
is connected in BasisDensityTransport.
-/

namespace Funk

noncomputable section

def vertexMatrix {n : ℕ} (τ : ℝ) (signs : Fin n → ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (X : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i => polarVertex τ (signs i) (B i) X

theorem vertexMatrix_eq_diagonal_mul {n : ℕ} (τ : ℝ) (signs : Fin n → ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (X : Space n) :
    vertexMatrix τ signs B X =
      Matrix.diagonal (fun i => signs i / (1 - signs i * τ * dotProduct (B i) X)) * B := by
  ext i j
  simp [vertexMatrix, polarVertex, Matrix.diagonal_mul]

theorem det_vertexMatrix {n : ℕ} (τ : ℝ) (signs : Fin n → ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (X : Space n) :
    (vertexMatrix τ signs B X).det =
      (∏ i, signs i / (1 - signs i * τ * dotProduct (B i) X)) * B.det := by
  rw [vertexMatrix_eq_diagonal_mul, Matrix.det_mul, Matrix.det_diagonal]

theorem denominator_product_pos {n : ℕ} {τ : ℝ} {signs : Fin n → ℝ}
    {B : Matrix (Fin n) (Fin n) ℝ} {X : Space n}
    (hτ₀ : 0 ≤ τ) (hτ₁ : τ < 1) (hs : ∀ i, signs i = 1 ∨ signs i = -1)
    (hX : X ∈ stripBody B) :
    0 < ∏ i, (1 - signs i * τ * dotProduct (B i) X) :=
  Finset.prod_pos (fun i _ => denominator_pos hτ₀ hτ₁ (hs i) (hX i))

theorem abs_det_vertexMatrix {n : ℕ} {τ : ℝ} {signs : Fin n → ℝ}
    {B : Matrix (Fin n) (Fin n) ℝ} {X : Space n}
    (hτ₀ : 0 ≤ τ) (hτ₁ : τ < 1) (hs : ∀ i, signs i = 1 ∨ signs i = -1)
    (hX : X ∈ stripBody B) :
    |(vertexMatrix τ signs B X).det| =
      |B.det| / (∏ i, (1 - signs i * τ * dotProduct (B i) X)) := by
  have habs (i : Fin n) : |signs i / (1 - signs i * τ * dotProduct (B i) X)| =
      1 / (1 - signs i * τ * dotProduct (B i) X) := by
    rw [abs_div, abs_of_pos (denominator_pos hτ₀ hτ₁ (hs i) (hX i))]
    rcases hs i with hi | hi <;> rw [hi] <;> norm_num
  rw [det_vertexMatrix, abs_mul, Finset.abs_prod]
  simp_rw [habs]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const_one]
  ring

theorem det_vertexMatrix_ne_zero {n : ℕ} {τ : ℝ} {signs : Fin n → ℝ}
    {B : Matrix (Fin n) (Fin n) ℝ} {X : Space n}
    (hτ₀ : 0 ≤ τ) (hτ₁ : τ < 1) (hs : ∀ i, signs i = 1 ∨ signs i = -1)
    (hX : X ∈ stripBody B) (hB : B.det ≠ 0) : (vertexMatrix τ signs B X).det ≠ 0 := by
  apply abs_pos.mp
  rw [abs_det_vertexMatrix hτ₀ hτ₁ hs hX]
  exact div_pos (abs_pos.mpr hB) (denominator_product_pos hτ₀ hτ₁ hs hX)

/-- The joint-density denominators match the determinant denominators exactly.
The actual boundary probability and multivariate change of variables are
connected in BasisDensityTransport. General simplex non-overlap remains
an explicit hypothesis in BasisPackingIntegral. -/
theorem density_product_mul_abs_det {n : ℕ} {τ : ℝ} {signs : Fin n → ℝ}
    {B : Matrix (Fin n) (Fin n) ℝ} {X : Space n}
    (hτ₀ : 0 ≤ τ) (hτ₁ : τ < 1) (hs : ∀ i, signs i = 1 ∨ signs i = -1)
    (hX : X ∈ stripBody B) :
    (∏ i, branchDensity τ (signs i) (dotProduct (B i) X)) * |B.det| =
      (τ / (4 * Real.artanh τ)) ^ n * |(vertexMatrix τ signs B X).det| := by
  rw [abs_det_vertexMatrix hτ₀ hτ₁ hs hX]
  have heq (i : Fin n) : branchDensity τ (signs i) (dotProduct (B i) X) =
      (τ / (4 * Real.artanh τ)) / (1 - signs i * τ * dotProduct (B i) X) := by
    simp [branchDensity, div_div]
  simp_rw [heq]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

end
end Funk
