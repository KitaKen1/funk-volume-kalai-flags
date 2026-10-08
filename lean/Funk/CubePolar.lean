import Funk.SignedDiagonalPacking

/-! A genuine all-dimensional use of the packing certificates, for the cube.
This is a pointwise lower bound on translated polar volume. It is not yet a
Funk integral theorem or a result for general centrally symmetric polytopes. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk

noncomputable section

def coordinateCube (n : ℕ) : Set (Space n) :=
  stripBody (1 : Matrix (Fin n) (Fin n) ℝ)

theorem mem_coordinateCube {n : ℕ} (X : Space n) :
    X ∈ coordinateCube n ↔ ∀ i, |X i| ≤ 1 := by
  simp [coordinateCube, stripBody, dotProduct, Matrix.one_apply]

def cubeVertexLengths {n : ℕ} (τ : ℝ) (X : Space n) (i : Fin n) (b : Bool) : ℝ :=
  1 / (1 - branchSign b * τ * X i)

theorem cubeVertexLengths_pos {n : ℕ} {τ : ℝ} {X : Space n}
    (hτ₀ : 0 ≤ τ) (hτ₁ : τ < 1) (hX : X ∈ coordinateCube n) (i : Fin n) (b : Bool) :
    0 < cubeVertexLengths τ X i b := by
  exact one_div_pos.mpr (denominator_pos hτ₀ hτ₁ (branchSign_cases b)
    ((mem_coordinateCube X).mp hX i))

theorem signedDiagonal_cube_eq_vertexMatrix {n : ℕ} (τ : ℝ) (X : Space n)
    (b : Fin n → Bool) :
    signedDiagonal (cubeVertexLengths τ X) b =
      vertexMatrix τ (fun i => branchSign (b i)) (1 : Matrix (Fin n) (Fin n) ℝ) X := by
  rw [vertexMatrix_eq_diagonal_mul, Matrix.mul_one]
  ext i j
  simp [signedDiagonal, cubeVertexLengths, dotProduct, Matrix.one_apply, div_eq_mul_inv]

/-- All sign choices are included; their non-overlap has been proved by separators. -/
theorem cube_polar_volume_lower {n : ℕ} {τ : ℝ} {X : Space n}
    (hτ₀ : 0 ≤ τ) (hτ₁ : τ < 1) (hX : X ∈ coordinateCube n) :
    ENNReal.ofReal ((∏ i, (1 / (1 - τ * X i) + 1 / (1 + τ * X i))) /
      (n.factorial : ℝ)) ≤ volume (coordinatePolar (translate (coordinateCube n) (τ • X))) := by
  have h := signedDiagonal_product_bound (cubeVertexLengths τ X)
    (fun i b => (cubeVertexLengths_pos hτ₀ hτ₁ hX i b).le)
    (coordinatePolar (translate (coordinateCube n) (τ • X))) (fun b => by
      rw [signedDiagonal_cube_eq_vertexMatrix]
      exact feasibleHull_subset_polar hτ₀ hτ₁ hX id (fun i => branchSign (b i))
        (fun i => branchSign_cases (b i)))
  convert h using 2
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp [cubeVertexLengths, branchSign, add_comm]

/-- At the centre this supplies the expected cross-polytope volume as a lower bound. -/
theorem cube_polar_volume_lower_at_zero (n : ℕ) :
    ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ)) ≤
      volume (coordinatePolar (coordinateCube n)) := by
  have h := cube_polar_volume_lower (n := n) (τ := 0) (X := 0)
    (by norm_num) (by norm_num) ((mem_coordinateCube 0).mpr (by simp))
  simpa [translate, show (1 : ℝ) + 1 = 2 by norm_num] using h

end
end Funk
