import Funk.IrredundantRows

/-! Signed-convex irredundancy excludes all proportional pairs, not only equal
or opposite rows. In basis coordinates, a genuine extra row must therefore
involve at least two nonzero coefficients. -/

open Set Matrix

namespace Funk
noncomputable section

theorem smul_mem_signedRowHull {n : ℕ} {ι : Type*} (rows : ι → Space n)
    {v : Space n} (hv : v ∈ signedRowHull rows) {c : ℝ} (hc : |c| ≤ 1) :
    c • v ∈ signedRowHull rows := by
  have hn := neg_mem_signedRowHull rows hv
  have h := (convex_convexHull ℝ (range rows ∪ range (fun i => -rows i))) hv hn
    (show 0 ≤ (1 + c) / 2 by have := (abs_le.mp hc).1; linarith)
    (show 0 ≤ (1 - c) / 2 by have := (abs_le.mp hc).2; linarith)
    (show (1 + c) / 2 + (1 - c) / 2 = 1 by ring)
  have he : ((1 + c) / 2) • v + ((1 - c) / 2) • (-v) = c • v := by
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring
  rwa [he] at h

theorem signedIrredundant_no_proportional {n : ℕ} {ι : Type*}
    (rows : ι → Space n) (h : SignedIrredundant rows) {i j : ι}
    (hne : i ≠ j) (c : ℝ) : rows i ≠ c • rows j := by
  intro he
  by_cases hc : |c| ≤ 1
  · apply h i
    rw [he]
    exact smul_mem_signedRowHull _
      (row_mem_signedRowHull (fun k : {k : ι // k ≠ i} => rows k.val)
        ⟨j, Ne.symm hne⟩) hc
  · have hc1 : 1 < |c| := lt_of_not_ge hc
    have hc0 : c ≠ 0 := by intro hz; norm_num [hz] at hc1
    have hinv : |c⁻¹| ≤ 1 := by
      rw [abs_inv]
      exact inv_le_one_of_one_le₀ hc1.le
    apply h j
    have hj : rows j = c⁻¹ • rows i := by rw [he, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [hj]
    exact smul_mem_signedRowHull _
      (row_mem_signedRowHull (fun k : {k : ι // k ≠ j} => rows k.val) ⟨i, hne⟩) hinv

/-- The exact coefficients a B⁻¹, over arbitrary real rows. -/
def rowBasisCoefficients {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (a : Space n) : Space n :=
  a ᵥ* B⁻¹

theorem rowBasisCoefficients_reconstruct {n : ℕ}
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.det ≠ 0) (a : Space n) :
    rowBasisCoefficients B a ᵥ* B = a := by
  rw [rowBasisCoefficients, Matrix.vecMul_vecMul,
    Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hB), Matrix.vecMul_one]

theorem rowBasisCoefficients_dot {n : ℕ}
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.det ≠ 0) (a X : Space n) :
    dotProduct (rowBasisCoefficients B a) (basisMap B X) = dotProduct a X := by
  change dotProduct _ (B.mulVec X) = _
  rw [Matrix.dotProduct_mulVec, rowBasisCoefficients_reconstruct hB]

/-- Every coordinate axis would give a proportional selected row and is excluded. -/
theorem extra_row_coefficients_not_single {n : ℕ} {ι : Type*}
    (rows : ι → Space n) (hirr : SignedIrredundant rows) (s : Fin n → ι)
    (hB : Matrix.det (fun k => rows (s k)) ≠ 0) {j : ι} (hj : j ∉ range s)
    (i : Fin n) (c : ℝ) :
    rowBasisCoefficients (fun k => rows (s k)) (rows j) ≠ Pi.single i c := by
  intro he
  have hr := rowBasisCoefficients_reconstruct hB (rows j)
  rw [he] at hr
  have hv := Matrix.single_vecMul (fun k => rows (s k) : Matrix (Fin n) (Fin n) ℝ) i c
  exact signedIrredundant_no_proportional rows hirr
    (fun h => hj ⟨i, h.symm⟩) c (hr.symm.trans hv)

/-- No one-dimensional exceptional case remains for a genuine extra row. -/
theorem extra_row_coefficients_two_nonzero {n : ℕ} {ι : Type*}
    (rows : ι → Space n) (hirr : SignedIrredundant rows) (s : Fin n → ι)
    (hB : Matrix.det (fun k => rows (s k)) ≠ 0) {j : ι} (hj : j ∉ range s)
    (hj0 : rows j ≠ 0) :
    ∃ i k : Fin n, i ≠ k ∧
      rowBasisCoefficients (fun l => rows (s l)) (rows j) i ≠ 0 ∧
      rowBasisCoefficients (fun l => rows (s l)) (rows j) k ≠ 0 := by
  classical
  let v := rowBasisCoefficients (fun l => rows (s l)) (rows j)
  have hv : v ≠ 0 := by
    intro hz
    have hr := rowBasisCoefficients_reconstruct hB (rows j)
    change v ᵥ* (fun l => rows (s l)) = rows j at hr
    rw [hz] at hr
    exact hj0 (hr.symm.trans (Matrix.zero_vecMul _))
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! hn
    exact hv (funext hn)
  by_contra! hn
  have he : v = Pi.single i (v i) := by
    ext k
    by_cases hk : k = i
    · subst k; simp
    · have hz : v k = 0 := by
        exact hn i k (Ne.symm hk) hi
      simp [hk, hz]
  exact extra_row_coefficients_not_single rows hirr s hB hj i (v i) he

end
end Funk
