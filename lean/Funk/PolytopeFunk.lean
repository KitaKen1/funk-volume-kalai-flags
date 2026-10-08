import Funk.PolytopeStrips

/-! A single normalized finite strip presentation works for all 0 < tau < 1.
The only remaining analytic/combinatorial input to the polytope Funk target
is the actual probability covering inequality on that presentation. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

theorem finitePolytope_exists_uniform_simple_strips {n : ℕ} (hn : 1 ≤ n)
    {P : Set (Space n)} (hP : IsFinitePolytope P) (hK : IsSymmetricConvexBody P) :
    ∃ m : ℕ, ∃ rows : Fin m → Space n,
      P = stripBody rows ∧ SignedIrredundant rows ∧
      ∀ τ : ℝ, 0 < τ → τ < 1 →
        ∀ᵐ X ∂volume.restrict P, ∀ c ∈ canonicalBasisIndices rows,
          NoExtraActive τ rows c.1 c.2 X := by
  obtain ⟨m, rows, he⟩ := finitePolytope_exists_strip_presentation hP hK
  obtain ⟨k, _, selected, hirr, _, hbody⟩ := exists_signedIrredundant_presentation rows
  have hnew : P = stripBody (fun i => rows (selected i)) := he.trans hbody.symm
  refine ⟨k, fun i => rows (selected i), hnew, hirr, ?_⟩
  intro τ hτ0 hτ1
  rw [hnew]
  exact ae_canonical_noExtraActive hn hτ0 hτ1 _ hirr (hnew ▸ hK.1)

/-- This is a conditional bridge, not a proof of the general probability cover. -/
theorem funkVolume_polytope_target_of_irredundant_covers {n : ℕ} (hn : 1 ≤ n)
    {P : Set (Space n)} (hP : IsFinitePolytope P) (hK : IsSymmetricConvexBody P)
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hcover : ∀ (m : ℕ) (rows : Fin m → Space n), P = stripBody rows →
      SignedIrredundant rows →
      1 ≤ ∑ k ∈ canonicalBasisIndices rows, lensBoundaryRows n τ
        (basisBoundaryEvent τ k.2 (fun i => rows (k.1 i))
          (basisFeasibleRegion τ rows k.1 k.2))) :
    funkVolume P τ < ⊤ ∧
      ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) ≤ funkVolume P τ := by
  obtain ⟨m, rows, he, hirr, _⟩ := finitePolytope_exists_uniform_simple_strips hn hP hK
  have hc := hcover m rows he hirr
  rw [he]
  exact funkVolume_strip_target_of_irredundant_cover hn rows hirr (he ▸ hK) hτ0 hτ1 hc

end
end Funk
