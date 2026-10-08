import Funk.SimplexVolume
import Funk.CertificateExamples

/-! The known vertices are a certificate for a genuine simplex in the polar.
All volumes are the original product Lebesgue measure. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk

noncomputable section

theorem convex_solidSimplex (n : ℕ) (r : ℝ) : Convex ℝ (solidSimplex n r) := by
  intro x hx y hy a b ha hb hab
  change (∀ i, 0 ≤ a * x i + b * y i) ∧ ∑ i, (a * x i + b * y i) ≤ r
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hax := mul_le_mul_of_nonneg_left hx.2 ha
    have hby := mul_le_mul_of_nonneg_left hy.2 hb
    calc
      _ ≤ a * r + b * r := add_le_add hax hby
      _ = r := by rw [← add_mul, hab, one_mul]

theorem solidSimplex_eq_convexHull (n : ℕ) :
    solidSimplex n 1 = convexHull ℝ (insert 0 (Set.range (fun i : Fin n => Pi.single i (1 : ℝ)))) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    let w : Fin (n + 1) → ℝ := Fin.cons (1 - ∑ i, x i) x
    let z : Fin (n + 1) → Space n := Fin.cons 0 (fun i => Pi.single i 1)
    have hw : ∀ j ∈ (Finset.univ : Finset (Fin (n + 1))), 0 ≤ w j := by
      intro j _
      refine Fin.cases ?_ (fun i => ?_) j
      · exact sub_nonneg.mpr hx.2
      · exact hx.1 i
    have hsum : ∑ j, w j = 1 := by
      simp [w, Fin.sum_univ_succ]
    have hz : ∀ j ∈ (Finset.univ : Finset (Fin (n + 1))),
        z j ∈ convexHull ℝ (insert 0 (Set.range (fun i : Fin n => Pi.single i (1 : ℝ)))) := by
      intro j _
      apply subset_convexHull
      refine Fin.cases ?_ (fun i => ?_) j
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ ⟨i, rfl⟩
    have hc := (convex_convexHull ℝ _).sum_mem hw hsum hz
    have he : (∑ j, w j • z j) = x := by
      ext i
      simp [w, z, Fin.sum_univ_succ, Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    rwa [he] at hc
  · apply convexHull_min
    · intro x hx
      rcases hx with hx | ⟨i, rfl⟩
      · subst x
        simp [solidSimplex]
      · constructor
        · intro j
          simp only [Pi.single_apply]
          split_ifs <;> norm_num
        · simp
    · exact convex_solidSimplex n 1

/-- Rows are vertices; hence the linear map uses the transpose of the row matrix. -/
def rowSimplex {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) : Set (Space n) :=
  convexHull ℝ (insert 0 (Set.range V))

theorem rowSimplex_eq_linear_image {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) :
    rowSimplex V = (Matrix.toLin' V.transpose) '' solidSimplex n 1 := by
  rw [solidSimplex_eq_convexHull, LinearMap.image_convexHull]
  unfold rowSimplex
  congr 1
  rw [Set.image_insert_eq, map_zero, ← Set.range_comp]
  congr 2
  funext i
  ext j
  simp [Matrix.toLin'_apply]

/-- Actual convex-hull volume, including singular matrices and dimension zero. -/
theorem volume_rowSimplex {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) :
    volume (rowSimplex V) = ENNReal.ofReal (|V.det| / (n.factorial : ℝ)) := by
  rw [rowSimplex_eq_linear_image, Measure.addHaar_image_linearMap,
    LinearMap.det_toLin', Matrix.det_transpose, volume_solidSimplex n (by norm_num)]
  simp only [one_pow]
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  ring

/-- The determinant denominator now computes Lebesgue volume, not a surrogate. -/
theorem volume_vertexSimplex {n : ℕ} {τ : ℝ} {signs : Fin n → ℝ}
    {B : Matrix (Fin n) (Fin n) ℝ} {X : Space n}
    (hτ₀ : 0 ≤ τ) (hτ₁ : τ < 1) (hs : ∀ i, signs i = 1 ∨ signs i = -1)
    (hX : X ∈ stripBody B) :
    volume (rowSimplex (vertexMatrix τ signs B X)) =
      ENNReal.ofReal (|B.det| / ((n.factorial : ℝ) *
        ∏ i, (1 - signs i * τ * dotProduct (B i) X))) := by
  rw [volume_rowSimplex, abs_det_vertexMatrix hτ₀ hτ₁ hs hX]
  congr 1
  ring

/-- A concrete mixed-sign two-dimensional certificate has area 4/7. -/
theorem rational_vertex_area_example :
    volume (rowSimplex (vertexMatrix (1 / 2) ![1, -1]
      (1 : Matrix (Fin 2) (Fin 2) ℝ) (![1 / 2, 1 / 3] : Space 2))) =
        ENNReal.ofReal (4 / 7) := by
  rw [volume_rowSimplex, rational_vertex_determinant_example]
  norm_num

/-- Any selected simplex gives a lower bound for the actual polar volume.
Summing such bounds still requires a separate non-overlap argument. -/
theorem vertexSimplex_bound_polar {n : ℕ} {ι : Type*} {rows : ι → Space n}
    {τ : ℝ} {X : Space n} (hτ₀ : 0 ≤ τ) (hτ₁ : τ < 1)
    (hX : X ∈ stripBody rows) (selected : Fin n → ι) (signs : Fin n → ℝ)
    (hs : ∀ i, signs i = 1 ∨ signs i = -1) :
    ENNReal.ofReal (|Matrix.det (fun i => rows (selected i) : Matrix (Fin n) (Fin n) ℝ)| /
      ((n.factorial : ℝ) * ∏ i, (1 - signs i * τ * dotProduct (rows (selected i)) X))) ≤
        volume (coordinatePolar (translate (stripBody rows) (τ • X))) := by
  have hselected : X ∈ stripBody (fun i => rows (selected i)) := fun i => hX (selected i)
  rw [← volume_vertexSimplex hτ₀ hτ₁ hs hselected]
  exact measure_mono (feasibleHull_subset_polar hτ₀ hτ₁ hX selected signs hs)

end
end Funk
