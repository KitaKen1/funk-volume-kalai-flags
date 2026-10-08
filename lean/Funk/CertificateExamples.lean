import Funk.LinearCertificate
import Funk.VertexDeterminant

/-! A concrete rational certificate, verified by the kernel without `native_decide`.
The half-space intersection need not be bounded for this local fact.
-/

namespace Funk

theorem rational_triangle_certificate :
    (![1 / 3, 2 / 3] : Space 2) ∈
      coordinatePolar {x : Space 2 | x 0 ≤ 1 ∧ x 1 ≤ 1} := by
  have h := linearCertificate_mem_polar
    (![![1, 0], ![0, 1]] : Fin 2 → Space 2)
    (![1, 1] : Fin 2 → ℝ) (![1 / 3, 2 / 3] : Fin 2 → ℝ)
    (![1 / 3, 2 / 3] : Space 2)
    (by intro i; fin_cases i <;> norm_num)
    (by ext i; fin_cases i <;> norm_num [Fin.sum_univ_two])
    (by norm_num [Fin.sum_univ_two])
  intro x hx
  apply h x
  intro i
  fin_cases i
  · simpa [dotProduct, Fin.sum_univ_two] using hx.1
  · simpa [dotProduct, Fin.sum_univ_two] using hx.2

/-- A noncentral, mixed-sign certificate: denominators are 3/4 and 7/6,
so the signed determinant is -8/7 and its absolute value is 8/7. -/
theorem rational_vertex_determinant_example :
    |(vertexMatrix (1 / 2) ![1, -1] (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (![1 / 2, 1 / 3] : Space 2)).det| = 8 / 7 := by
  norm_num [vertexMatrix, polarVertex, Matrix.det_fin_two, dotProduct, Fin.sum_univ_two]

end Funk
