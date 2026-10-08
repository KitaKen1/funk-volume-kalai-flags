import Funk.SeparationCertificate
import Funk.BranchProbability

/-! A family for which separation certificates can actually be constructed:
axis simplices in distinct signed orthants. All dimensions are covered.
This calibrates the packing checker; it is not the arbitrary polytope case. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk

noncomputable section

def signedDiagonal {n : ℕ} (a : Fin n → Bool → ℝ) (b : Fin n → Bool) :
    Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i => branchSign (b i) * a i (b i))

/-- The first coordinate whose signs differ supplies a separator. -/
theorem signedDiagonal_separator {n : ℕ} (a : Fin n → Bool → ℝ)
    (ha : ∀ i b, 0 ≤ a i b) {b c : Fin n → Bool} (hbc : b ≠ c) :
    ∃ f : Space n →ₗ[ℝ] ℝ, f ≠ 0 ∧
      (∀ j, 0 ≤ f (signedDiagonal a b j)) ∧
      (∀ j, f (signedDiagonal a c j) ≤ 0) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, b i ≠ c i := not_forall.mp (fun h => hbc (funext h))
  let f : Space n →ₗ[ℝ] ℝ := branchSign (b i) • LinearMap.proj i
  refine ⟨f, ?_, ?_, ?_⟩
  · intro hf
    have he := LinearMap.congr_fun hf (Pi.single i 1)
    cases hb : b i <;> simp [f, branchSign, hb] at he
  · intro j
    by_cases hji : j = i
    · subst j
      cases hb : b i <;> simpa [f, signedDiagonal, branchSign, hb] using ha i (b i)
    · simp [f, signedDiagonal, hji]
  · intro j
    by_cases hji : j = i
    · subst j
      cases hb : b i <;> cases hc : c i
      · exact False.elim (hi (hb.trans hc.symm))
      · simpa [f, signedDiagonal, branchSign, hb, hc] using neg_nonpos.mpr (ha i true)
      · simpa [f, signedDiagonal, branchSign, hb, hc] using neg_nonpos.mpr (ha i false)
      · exact False.elim (hi (hb.trans hc.symm))
    · simp [f, signedDiagonal, hji]

theorem signedDiagonal_pairwise_aedisjoint {n : ℕ} (a : Fin n → Bool → ℝ)
    (ha : ∀ i b, 0 ≤ a i b) :
    Pairwise (fun b c : Fin n → Bool =>
      AEDisjoint volume (rowSimplex (signedDiagonal a b)) (rowSimplex (signedDiagonal a c))) := by
  intro b c hbc
  obtain ⟨f, hf, hb, hc⟩ := signedDiagonal_separator a ha hbc
  exact rowSimplex_aedisjoint_of_separator _ _ f hf hb hc

/-- No unproved non-overlap hypothesis remains for this specific family. -/
theorem signedDiagonal_sum_volume_le {n : ℕ} (a : Fin n → Bool → ℝ)
    (ha : ∀ i b, 0 ≤ a i b) (K : Set (Space n))
    (hsub : ∀ b, rowSimplex (signedDiagonal a b) ⊆ K) :
    ∑ b : Fin n → Bool, ENNReal.ofReal (|(signedDiagonal a b).det| / (n.factorial : ℝ)) ≤
      volume K := by
  apply rowSimplex_sum_le_of_separators Finset.univ (signedDiagonal a) K
  · intro b _ c _ hbc
    exact signedDiagonal_separator a ha hbc
  · intro b _
    exact hsub b

theorem abs_det_signedDiagonal {n : ℕ} (a : Fin n → Bool → ℝ)
    (ha : ∀ i b, 0 ≤ a i b) (b : Fin n → Bool) :
    |(signedDiagonal a b).det| = ∏ i, a i (b i) := by
  rw [signedDiagonal, Matrix.det_diagonal, Finset.abs_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [abs_mul, abs_of_nonneg (ha i (b i))]
  cases b i <;> simp [branchSign]

/-- Exponentially many sign choices factor into a product of two-term sums. -/
theorem sum_abs_det_signedDiagonal {n : ℕ} (a : Fin n → Bool → ℝ)
    (ha : ∀ i b, 0 ≤ a i b) :
    (∑ b : Fin n → Bool, |(signedDiagonal a b).det| / (n.factorial : ℝ)) =
      (∏ i, (a i false + a i true)) / (n.factorial : ℝ) := by
  simp_rw [abs_det_signedDiagonal a ha]
  rw [← Finset.sum_div, ← Fintype.prod_sum]
  simp only [Fintype.sum_bool]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  ring

theorem signedDiagonal_product_bound {n : ℕ} (a : Fin n → Bool → ℝ)
    (ha : ∀ i b, 0 ≤ a i b) (K : Set (Space n))
    (hsub : ∀ b, rowSimplex (signedDiagonal a b) ⊆ K) :
    ENNReal.ofReal ((∏ i, (a i false + a i true)) / (n.factorial : ℝ)) ≤ volume K := by
  have h := signedDiagonal_sum_volume_le a ha K hsub
  rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ =>
    div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)), sum_abs_det_signedDiagonal a ha] at h
  exact h

end
end Funk
