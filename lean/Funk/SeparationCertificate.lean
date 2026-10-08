import Funk.SimplexPacking

/-! Linear separation certificates reduce measure-theoretic non-overlap to
finite inequalities at the known vertices. Certificates still have to be
constructed for the intended geometric family. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk

noncomputable section

theorem linear_separator_aedisjoint {n : ℕ} {S T : Set (Space n)}
    (f : Space n →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (hS : ∀ x ∈ S, 0 ≤ f x) (hT : ∀ x ∈ T, f x ≤ 0) :
    AEDisjoint volume S T := by
  apply measure_mono_null (t := (f.ker : Set (Space n)))
  · intro x hx
    exact le_antisymm (hT x hx.2) (hS x hx.1)
  · exact Measure.addHaar_submodule volume f.ker (fun h => hf (LinearMap.ker_eq_top.mp h))

theorem linear_nonneg_rowSimplex {n : ℕ} (f : Space n →ₗ[ℝ] ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) (hV : ∀ i, 0 ≤ f (V i)) :
    ∀ x ∈ rowSimplex V, 0 ≤ f x := by
  apply convexHull_min _ ((convex_Ici (0 : ℝ)).linear_preimage f)
  rintro x (rfl | ⟨i, rfl⟩)
  · simp
  · exact hV i

theorem linear_nonpos_rowSimplex {n : ℕ} (f : Space n →ₗ[ℝ] ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) (hV : ∀ i, f (V i) ≤ 0) :
    ∀ x ∈ rowSimplex V, f x ≤ 0 := by
  apply convexHull_min _ ((convex_Iic (0 : ℝ)).linear_preimage f)
  rintro x (rfl | ⟨i, rfl⟩)
  · simp
  · exact hV i

theorem rowSimplex_aedisjoint_of_separator {n : ℕ}
    (V W : Matrix (Fin n) (Fin n) ℝ) (f : Space n →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (hV : ∀ i, 0 ≤ f (V i)) (hW : ∀ i, f (W i) ≤ 0) :
    AEDisjoint volume (rowSimplex V) (rowSimplex W) :=
  linear_separator_aedisjoint f hf (linear_nonneg_rowSimplex f V hV)
    (linear_nonpos_rowSimplex f W hW)

/-- Only finitely many vertex evaluations need to be checked for each pair. -/
theorem rowSimplex_sum_le_of_separators {n : ℕ} {ι : Type*} (indices : Finset ι)
    (V : ι → Matrix (Fin n) (Fin n) ℝ) (K : Set (Space n))
    (hsep : ∀ k ∈ indices, ∀ l ∈ indices, k ≠ l →
      ∃ f : Space n →ₗ[ℝ] ℝ, f ≠ 0 ∧ (∀ i, 0 ≤ f (V k i)) ∧ (∀ i, f (V l i) ≤ 0))
    (hsub : ∀ k ∈ indices, rowSimplex (V k) ⊆ K) :
    ∑ k ∈ indices, ENNReal.ofReal (|(V k).det| / (n.factorial : ℝ)) ≤ volume K := by
  have hd : (indices : Set ι).Pairwise (fun k l => AEDisjoint volume (rowSimplex (V k)) (rowSimplex (V l))) := by
    intro k hk l hl hkl
    obtain ⟨f, hf, hfk, hfl⟩ := hsep k hk l hl hkl
    exact rowSimplex_aedisjoint_of_separator _ _ f hf hfk hfl
  have he := measure_biUnion_finset₀ hd
    (fun k _ => (convex_rowSimplex (V k)).nullMeasurableSet volume)
  simp only [volume_rowSimplex] at he
  rw [← he]
  apply measure_mono
  intro x hx
  obtain ⟨k, hk, hx⟩ := Set.mem_iUnion₂.mp hx
  exact hsub k hk hx

/-- A small exact certificate: opposite quadrants have a zero-measure intersection. -/
theorem opposite_triangles_aedisjoint :
    AEDisjoint volume (rowSimplex (1 : Matrix (Fin 2) (Fin 2) ℝ))
      (rowSimplex (-1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  apply rowSimplex_aedisjoint_of_separator _ _ (LinearMap.proj 0)
  · intro h
    have he := LinearMap.congr_fun h (![1, 0] : Space 2)
    norm_num at he
  · intro i
    fin_cases i <;> norm_num [Matrix.one_apply]
  · intro i
    fin_cases i <;> norm_num [Matrix.one_apply]

end
end Funk
