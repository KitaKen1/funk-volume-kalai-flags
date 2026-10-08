import Funk.ProjectivePolar
import Funk.SimplexCertificate
import Mathlib.Analysis.Convex.Combination

/-! Known projective vertices are verified by positive barycentric weights.
Only a one-sided convex-hull image inclusion is needed for an upper bound;
no projective change-of-variables theorem is assumed. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

/-- Reweight barycentric coefficients by their positive projective denominators. -/
theorem polarShift_mem_convexHull_image {n : ℕ} {s : Set (Space n)} {x y : Space n}
    (hs : ∀ z ∈ s, 0 < 1 - dotProduct z x)
    (hy : y ∈ convexHull ℝ s) (hd : 0 < 1 - dotProduct y x) :
    polarShift x y ∈ convexHull ℝ (polarShift x '' s) := by
  classical
  obtain ⟨ι, hι, a, z, ha, hsum, hz, he⟩ := mem_convexHull_iff_exists_fintype.mp hy
  let := hι
  let d : ι → ℝ := fun i => 1 - dotProduct (z i) x
  let D : ℝ := 1 - dotProduct y x
  have hp (i : ι) : 0 < d i := hs (z i) (hz i)
  have hD : 0 < D := hd
  have hdot : ∑ i, a i * dotProduct (z i) x = dotProduct y x := by
    rw [← he, sum_dotProduct]
    simp only [smul_dotProduct, smul_eq_mul]
  have hden : ∑ i, a i * d i = D := by
    simp only [d, mul_sub, mul_one, Finset.sum_sub_distrib, hsum, hdot, D]
  apply mem_convexHull_of_exists_fintype (fun i => a i * d i / D)
    (fun i => polarShift x (z i))
  · intro i
    exact div_nonneg (mul_nonneg (ha i) (hp i).le) hD.le
  · rw [← Finset.sum_div, hden]
    exact div_self (ne_of_gt hD)
  · intro i
    exact Set.mem_image_of_mem _ (hz i)
  · have hi (i : ι) : (a i * d i / D) • polarShift x (z i) =
        (1 / D) • (a i • z i) := by
      simp only [polarShift, smul_smul]
      change ((a i * d i / D) * (1 / d i)) • z i = ((1 / D) * a i) • z i
      congr 1
      field_simp [ne_of_gt (hp i), ne_of_gt hD]
    simp_rw [hi]
    rw [← Finset.smul_sum, he]
    rfl

def shiftedRowMatrix {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ := fun i => polarShift x (Q i)

theorem polarShift_rowSimplex_subset {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (x : Space n)
    (hd : ∀ y ∈ rowSimplex Q, 0 < 1 - dotProduct y x) :
    polarShift x '' rowSimplex Q ⊆ rowSimplex (shiftedRowMatrix Q x) := by
  rintro _ ⟨y, hy, rfl⟩
  have hs : ∀ z ∈ insert 0 (Set.range Q), 0 < 1 - dotProduct z x :=
    fun z hz => hd z (subset_convexHull ℝ _ hz)
  have h := polarShift_mem_convexHull_image hs hy (hd y hy)
  apply convexHull_mono _ h
  rintro _ ⟨z, rfl | ⟨i, rfl⟩, rfl⟩
  · rw [polarShift_zero]
    exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ ⟨i, rfl⟩

theorem shiftedRowMatrix_eq_diagonal_mul {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (x : Space n) :
    shiftedRowMatrix Q x = Matrix.diagonal (fun i => 1 / (1 - dotProduct (Q i) x)) * Q := by
  ext i j
  simp [shiftedRowMatrix, polarShift, Matrix.diagonal_mul]

theorem det_shiftedRowMatrix {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (x : Space n) :
    (shiftedRowMatrix Q x).det =
      (∏ i, 1 / (1 - dotProduct (Q i) x)) * Q.det := by
  rw [shiftedRowMatrix_eq_diagonal_mul, Matrix.det_mul, Matrix.det_diagonal]

theorem abs_det_shiftedRowMatrix {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (x : Space n)
    (hd : ∀ i, 0 < 1 - dotProduct (Q i) x) :
    |(shiftedRowMatrix Q x).det| = |Q.det| / ∏ i, (1 - dotProduct (Q i) x) := by
  rw [det_shiftedRowMatrix, abs_mul, Finset.abs_prod]
  simp_rw [abs_div, abs_one, abs_of_pos (hd _)]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const_one]
  ring

theorem volume_shiftedRowSimplex {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (x : Space n)
    (hd : ∀ i, 0 < 1 - dotProduct (Q i) x) :
    volume (rowSimplex (shiftedRowMatrix Q x)) =
      ENNReal.ofReal (|Q.det| / ((∏ i, (1 - dotProduct (Q i) x)) * (n.factorial : ℝ))) := by
  rw [volume_rowSimplex, abs_det_shiftedRowMatrix Q x hd, div_div]

/-- The totalized inverse is measurable even outside the region of positive denominators. -/
theorem measurable_shiftedRowMatrix {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) :
    Measurable (fun x i j => shiftedRowMatrix Q x i j) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  have hd : Measurable (fun x : Space n => 1 - dotProduct (Q i) x) :=
    (continuous_const.sub (continuous_const.dotProduct continuous_id)).measurable
  exact (measurable_const.div hd).mul measurable_const

end
end Funk
