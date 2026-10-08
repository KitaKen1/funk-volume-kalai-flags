import Funk.FunkComparison
import Funk.PolytopeApproximation
import Funk.PolytopeFunk

/-! Transfer the actual polytope Funk bound to arbitrary symmetric convex bodies.
Only order comparison and continuity of the scalar bound are needed. The final
cover premise is explicit: these conditional bridges do not prove that premise. -/

open Set MeasureTheory
open scoped ENNReal Topology

namespace Funk
noncomputable section

theorem continuousAt_funkLowerBound (n : ℕ) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ContinuousAt (fun σ : ℝ =>
      ENNReal.ofReal ((4 * Real.artanh σ) ^ n / (n.factorial : ℝ))) τ := by
  have hq : ContinuousAt (fun σ : ℝ => (1 + σ) / (1 - σ)) τ :=
    (continuousAt_const.add continuousAt_id).div
      (continuousAt_const.sub continuousAt_id) (by linarith)
  have hpos : 0 < (1 + τ) / (1 - τ) := div_pos (by linarith) (by linarith)
  have ha : ContinuousAt Real.artanh τ := by
    exact hq.sqrt.log (Real.sqrt_pos.mpr hpos).ne'
  exact ENNReal.continuous_ofReal.continuousAt.comp
    (((continuousAt_const.mul ha).pow n).div_const _)

/-- General-body lower bounds follow from all finite-polytope lower bounds. -/
theorem funkVolume_convex_lower_of_polytope_lower {n : ℕ} {K : Set (Space n)}
    (hK : IsSymmetricConvexBody K) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hpoly : ∀ P : Set (Space n), IsFinitePolytope P → IsSymmetricConvexBody P →
      ∀ σ : ℝ, 0 < σ → σ < 1 →
        ENNReal.ofReal ((4 * Real.artanh σ) ^ n / (n.factorial : ℝ)) ≤ funkVolume P σ) :
    ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) ≤ funkVolume K τ := by
  apply ContinuousWithinAt.closure_le (s := Ioo 0 τ)
    (by rw [closure_Ioo hτ0.ne]; exact ⟨hτ0.le, le_rfl⟩)
    (continuousAt_funkLowerBound n hτ0 hτ1).continuousWithinAt continuousWithinAt_const
  intro σ hσ
  have hc : 1 < τ / σ := (one_lt_div hσ.1).mpr hσ.2
  obtain ⟨P, hp, hbody, hKP, hPK⟩ := exists_symmetric_polytope_outer_sandwich hK hc
  exact (hpoly P hp hbody σ hσ.1 (hσ.2.trans hτ1)).trans
    (funkVolume_le_of_outer_sandwich hσ.1 hKP hPK)

/-- The conclusion is the frozen goal; the polytope lower-bound input is still required. -/
theorem funkLowerBoundGoal_of_polytope_lower
    (hpoly : ∀ (n : ℕ), 1 ≤ n → ∀ P : Set (Space n),
      IsFinitePolytope P → IsSymmetricConvexBody P → ∀ τ : ℝ, 0 < τ → τ < 1 →
        ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) ≤ funkVolume P τ) :
    FunkLowerBoundGoal := by
  intro n hn K hK τ hτ0 hτ1
  exact ⟨funkVolume_symmetricConvexBody_finite hK hτ0 hτ1,
    funkVolume_convex_lower_of_polytope_lower hK hτ0 hτ1 (hpoly n hn)⟩

/-- A single missing family of probability covers now suffices for the full Funk goal.
No approximation, finite representation, or a.e. simplicity premise is added. -/
theorem funkLowerBoundGoal_of_irredundant_covers
    (hcover : ∀ (n : ℕ), 1 ≤ n → ∀ (m : ℕ) (rows : Fin m → Space n),
      SignedIrredundant rows → IsSymmetricConvexBody (stripBody rows) →
      ∀ τ : ℝ, 0 < τ → τ < 1 →
        1 ≤ ∑ k ∈ canonicalBasisIndices rows, lensBoundaryRows n τ
          (basisBoundaryEvent τ k.2 (fun i => rows (k.1 i))
            (basisFeasibleRegion τ rows k.1 k.2))) : FunkLowerBoundGoal := by
  apply funkLowerBoundGoal_of_polytope_lower
  intro n hn P hp hK τ hτ0 hτ1
  apply (funkVolume_polytope_target_of_irredundant_covers hn hp hK hτ0 hτ1 _).2
  intro m rows he hirr
  exact hcover n hn m rows hirr (he ▸ hK) τ hτ0 hτ1

end
end Funk
