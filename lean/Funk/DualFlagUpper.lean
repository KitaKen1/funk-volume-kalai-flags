import Funk.DualFlagDomain

/-! The frozen Funk integral is bounded by reciprocal-product integrals on
concrete dual-coordinate simplices, without a covering, Jacobian or flag
correspondence premise. The sharp leading coefficient remains a separate goal. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

/-- Every actual flag-pair contribution is bounded by the original Funk volume. -/
theorem dualFlag_integral_le_funkVolume {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) :
    (∫⁻ u in dualFlagDomain τ F G, dualProductKernel u) ≤ funkVolume P τ := by
  rw [← flag_denominator_integral_eq_dualDomain hp hP τ F G]
  calc
    _ = ∫⁻ x in (fun y => τ • y) '' flagSimplex F,
        volume (rowSimplex (shiftedPolarFlagMatrix G x)) := by
      apply setLIntegral_congr_fun
        ((flagSimplex_isCompact F).image (continuous_id.const_smul τ)).measurableSet
      rintro x ⟨X, hX, rfl⟩
      exact (volume_shiftedPolarFlagSimplex hp hP hτ0 hτ1
        (flagSimplex_subset_polytope hP F hX) G).symm
    _ ≤ ∫⁻ x in (fun y => τ • y) '' flagSimplex F,
        volume (coordinatePolar (translate P x)) := by
      apply setLIntegral_mono'
        ((flagSimplex_isCompact F).image (continuous_id.const_smul τ)).measurableSet
      rintro x ⟨X, hX, rfl⟩
      exact measure_mono (shiftedPolarFlagSimplex_subset hp hP hτ0 hτ1
        (flagSimplex_subset_polytope hP F hX) G)
    _ ≤ funkVolume P τ :=
      lintegral_mono_set (Set.image_mono (flagSimplex_subset_polytope hP F))

theorem dualFlag_integral_finite {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) :
    (∫⁻ u in dualFlagDomain τ F G, dualProductKernel u) < ⊤ :=
  lt_of_le_of_lt (dualFlag_integral_le_funkVolume hp hP hτ0 hτ1 F G)
    (funkVolume_convex_finite hP.1 hP.2.1 hP.2.2.2 hτ0 hτ1)

/-- Concrete dual-coordinate upper bound, under the original geometric assumptions only. -/
theorem funkVolume_le_dualFlag_integrals {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    let : Finite (FullFlagWithTop P) := fullFlagWithTop_finite hp hP
    let : Fintype (FullFlagWithTop P) := Fintype.ofFinite (FullFlagWithTop P)
    let : Finite (FullFlagWithTop (coordinatePolar P)) := fullFlagWithTop_finite
      (coordinatePolar_isFinitePolytope hp hP.2.1 hP.2.2.2)
      (coordinatePolar_isSymmetricConvexBody hp hP)
    let : Fintype (FullFlagWithTop (coordinatePolar P)) :=
      Fintype.ofFinite (FullFlagWithTop (coordinatePolar P))
    funkVolume P τ ≤ ∑ F : FullFlagWithTop P, ∑ G : FullFlagWithTop (coordinatePolar P),
      ∫⁻ u in dualFlagDomain τ F G, dualProductKernel u := by
  let : Finite (FullFlagWithTop P) := fullFlagWithTop_finite hp hP
  let : Fintype (FullFlagWithTop P) := Fintype.ofFinite (FullFlagWithTop P)
  let : Finite (FullFlagWithTop (coordinatePolar P)) := fullFlagWithTop_finite
    (coordinatePolar_isFinitePolytope hp hP.2.1 hP.2.2.2)
    (coordinatePolar_isSymmetricConvexBody hp hP)
  let : Fintype (FullFlagWithTop (coordinatePolar P)) :=
    Fintype.ofFinite (FullFlagWithTop (coordinatePolar P))
  apply le_trans (funkVolume_le_polarFlag_denominator_integrals hp hP hτ0 hτ1)
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro F _
  apply Finset.sum_congr rfl
  intro G _
  exact flag_denominator_integral_eq_dualDomain hp hP τ F G

/-- The actual radius used by the frozen FVW epsilon envelope is now connected. -/
theorem funkVolume_radius_le_dualFlag_integrals {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    {R : ℝ} (hR : 0 < R) :
    let : Finite (FullFlagWithTop P) := fullFlagWithTop_finite hp hP
    let : Fintype (FullFlagWithTop P) := Fintype.ofFinite (FullFlagWithTop P)
    let : Finite (FullFlagWithTop (coordinatePolar P)) := fullFlagWithTop_finite
      (coordinatePolar_isFinitePolytope hp hP.2.1 hP.2.2.2)
      (coordinatePolar_isSymmetricConvexBody hp hP)
    let : Fintype (FullFlagWithTop (coordinatePolar P)) :=
      Fintype.ofFinite (FullFlagWithTop (coordinatePolar P))
    funkVolume P (radius R) ≤
      ∑ F : FullFlagWithTop P, ∑ G : FullFlagWithTop (coordinatePolar P),
        ∫⁻ u in dualFlagDomain (radius R) F G, dualProductKernel u :=
  funkVolume_le_dualFlag_integrals hp hP (radius_pos hR).le (radius_lt_one R)

end
end Funk
