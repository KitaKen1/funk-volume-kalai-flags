import Funk.PublicationStatements

/-! Open/closed convex-body convention in the geometric volume statement.
Polar inequalities extend through closure, and contracted convex-body boundaries
are Lebesgue null. Thus the literal open-body integral equals the frozen closed
body integral; no metric-ball or volume parameter is supplied as an assumption. -/

open Set MeasureTheory
open scoped ENNReal Pointwise

namespace Funk
noncomputable section

/-- Pairing inequalities are closed, so closing the primal body does not change its polar. -/
theorem translated_coordinatePolar_closure {n : ℕ} (K : Set (Space n)) (x : Space n) :
    coordinatePolar (translate (closure K) x) = coordinatePolar (translate K x) := by
  ext y
  constructor
  · intro h
    exact coordinatePolar_antitone (Set.image_mono subset_closure) h
  · intro h _ hv
    rcases hv with ⟨z, hz, rfl⟩
    have hc : IsClosed {z : Space n | dotProduct y (z - x) ≤ 1} := by
      apply isClosed_le _ continuous_const
      unfold dotProduct
      fun_prop
    have hs : K ⊆ {z : Space n | dotProduct y (z - x) ≤ 1} :=
      fun w hw => h _ ⟨w, hw, rfl⟩
    exact closure_minimal hs hc hz

/-- A genuine convex body's interior and closed body give the same translated polar. -/
theorem translated_coordinatePolar_interior {n : ℕ} {K : Set (Space n)}
    (hK : IsSymmetricConvexBody K) (x : Space n) :
    coordinatePolar (translate K x) = coordinatePolar (translate (interior K) x) := by
  have hc : closure (interior K) = K := by
    rw [hK.2.1.closure_interior_eq_closure_of_nonempty_interior ⟨0, hK.2.2.2⟩,
      hK.1.isClosed.closure_eq]
  simpa only [hc] using translated_coordinatePolar_closure (interior K) x

/-- The open-body product-Lebesgue integral has exactly the frozen value. -/
theorem funkVolume_open_body_eq {n : ℕ} {K : Set (Space n)}
    (hK : IsSymmetricConvexBody K) {τ : ℝ} (hτ : τ ≠ 0) :
    (∫⁻ x in ((fun y : Space n => τ • y) '' interior K),
      volume (coordinatePolar (translate (interior K) x))) = funkVolume K τ := by
  have hdom : ((fun y : Space n => τ • y) '' interior K) =
      interior ((fun y : Space n => τ • y) '' K) := by
    simpa only [← image_smul] using (interior_smul₀ hτ K).symm
  have hv : Convex ℝ ((fun y : Space n => τ • y) '' K) :=
    hK.2.1.linear_image (LinearMap.lsmul ℝ (Space n) τ)
  have ha := interior_ae_eq_of_null_frontier (hv.addHaar_frontier volume)
  rw [← hdom] at ha
  simp_rw [← translated_coordinatePolar_interior hK]
  unfold funkVolume
  rw [Measure.restrict_congr_set ha]

end
end Funk
