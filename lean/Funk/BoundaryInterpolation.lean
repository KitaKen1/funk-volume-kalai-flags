import Funk.FeasibleRegion
import Funk.DualCoordinates

/-! Direct boundary interpolation events for the remaining probability-cover input.
The explicit real/imaginary inverse is identified with existential complex interpolation.
The boundary chart reconstruction includes both endpoints. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

/-- Real part of the unique inverse-basis interpolant of sampled complex values. -/
def boundaryRealWitness {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℂ) : Space n :=
  basisMap B⁻¹ (fun i => (z i).re)

/-- Imaginary part of the same interpolant, without a sign/height parameterization. -/
def boundaryImagWitness {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℂ) : Space n :=
  basisMap B⁻¹ (fun i => (z i).im)

/-- Test every row of the actual interpolant in the actual closed lens. -/
def boundaryInterpolationEvent {n : ℕ} {ι : Type*} (τ : ℝ) (rows : ι → Space n)
    (s : Fin n → ι) : Set (Fin n → ℂ) :=
  {z | ∀ j, complexRow (rows j)
    (boundaryRealWitness (fun i => rows (s i)) z)
    (boundaryImagWitness (fun i => rows (s i)) z) ∈ lensGraphBody τ}

theorem continuous_boundaryRealWitness {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (boundaryRealWitness B) := by
  unfold boundaryRealWitness
  fun_prop

theorem continuous_boundaryImagWitness {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (boundaryImagWitness B) := by
  unfold boundaryImagWitness
  fun_prop

theorem complexRow_boundaryWitness {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.det ≠ 0) (z : Fin n → ℂ) (i : Fin n) :
    complexRow (B i) (boundaryRealWitness B z) (boundaryImagWitness B z) = z i := by
  apply Complex.ext
  · exact congrFun (basisMap_inverse_right hB (fun i => (z i).re)) i
  · exact congrFun (basisMap_inverse_right hB (fun i => (z i).im)) i

theorem boundaryWitness_unique {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.det ≠ 0) (z : Fin n → ℂ) (Y X : Space n)
    (he : ∀ i, complexRow (B i) Y X = z i) :
    Y = boundaryRealWitness B z ∧ X = boundaryImagWitness B z := by
  constructor
  · apply basisMap_injective hB
    ext i
    exact (congrArg Complex.re (he i)).trans
      (congrArg Complex.re (complexRow_boundaryWitness hB z i)).symm
  · apply basisMap_injective hB
    ext i
    exact (congrArg Complex.im (he i)).trans
      (congrArg Complex.im (complexRow_boundaryWitness hB z i)).symm

/-- Literal existential feasibility, with no measurable projection required. -/
theorem mem_boundaryInterpolationEvent_iff {n : ℕ} {ι : Type*}
    (τ : ℝ) (rows : ι → Space n) (s : Fin n → ι)
    (hB : Matrix.det (fun i => rows (s i)) ≠ 0) (z : Fin n → ℂ) :
    z ∈ boundaryInterpolationEvent τ rows s ↔ ∃ Y X : Space n,
      (∀ i, complexRow (rows (s i)) Y X = z i) ∧
      ∀ j, complexRow (rows j) Y X ∈ lensGraphBody τ := by
  constructor
  · intro hz
    exact ⟨_, _, complexRow_boundaryWitness hB z, hz⟩
  · rintro ⟨Y, X, he, hall⟩
    obtain ⟨rfl, rfl⟩ := boundaryWitness_unique hB z Y X he
    exact hall

theorem isClosed_boundaryInterpolationEvent {n : ℕ} {ι : Type*}
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : ι → Space n) (s : Fin n → ι) :
    IsClosed (boundaryInterpolationEvent τ rows s) := by
  unfold boundaryInterpolationEvent
  rw [ofPred_forall]
  apply isClosed_iInter
  intro j
  apply (lensGraphBody_isClosed hτ0 hτ1).preimage
  have hc : Continuous (fun z : Fin n → ℂ =>
      (dotProduct (rows j) (boundaryRealWitness (fun i => rows (s i)) z),
       dotProduct (rows j) (boundaryImagWitness (fun i => rows (s i)) z))) := by
    unfold dotProduct boundaryRealWitness boundaryImagWitness
    fun_prop
  exact Complex.equivRealProdCLM.symm.continuous.comp hc

/-- Reconstruct a genuine boundary point from its chart, also at the two endpoints. -/
theorem lensBranchPoint_boundaryCoordinates {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {z : ℂ} (hz : z ∈ frontier (lensGraphBody τ)) :
    lensBranchPoint τ (lensBoundaryCoordinates τ z).1 (lensBoundaryCoordinates τ z).2 = z := by
  have ha := lensGraphBody_frontier_subset_circleImage hτ0 hτ1 hz
  rw [lensCircleImage_eq_arcs hτ0 hτ1] at ha
  rcases ha with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
  · have ht : lensBoundaryCoordinates τ (lensRightPoint τ y) = (true, y) := by
      simp [lensBoundaryCoordinates, lensRightPoint_chord, lensRightPoint_im hτ0 hτ1 hy,
        lensProfile_nonneg hτ0 hτ1 hy]
    rw [ht]
    rfl
  · have hyneg : -y ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hy.2], by linarith [hy.1]⟩
    by_cases hp : 0 < lensProfile τ (-y)
    · have ht : lensBoundaryCoordinates τ (lensLeftPoint τ y) = (false, y) := by
        simp [lensBoundaryCoordinates, lensLeftPoint_chord, lensLeftPoint_im hτ0 hτ1 hy,
          show ¬0 ≤ -lensProfile τ (-y) by linarith]
      rw [ht]
      rfl
    · have he : lensProfile τ (-y) = 0 := le_antisymm (le_of_not_gt hp)
        (lensProfile_nonneg hτ0 hτ1 hyneg)
      have hyend : y = -1 ∨ y = 1 := by
        by_contra h
        have hs : y ∈ Ioo (-1 : ℝ) 1 :=
          ⟨lt_of_le_of_ne hy.1 (by tauto), lt_of_le_of_ne hy.2 (by tauto)⟩
        have hg := lensProfile_pos hτ0 hτ1
          (show -y ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith [hs.2], by linarith [hs.1]⟩)
        linarith
      have hr : lensProfile τ y = 0 := by
        rcases hyend with rfl | rfl
        · exact (lensProfile_endpoints hτ0 hτ1).1
        · exact (lensProfile_endpoints hτ0 hτ1).2
      have ht : lensBoundaryCoordinates τ (lensLeftPoint τ y) = (true, y) := by
        simp only [lensBoundaryCoordinates, lensLeftPoint_chord, he, neg_zero,
          lensLeftPoint_im hτ0 hτ1 hy, le_refl, ite_true]
      rw [ht]
      change lensRightPoint τ y = lensLeftPoint τ y
      apply Complex.ext
      · have hright := lensRightPoint_chord τ y
        have hleft := lensLeftPoint_chord τ y
        rw [hr] at hright
        rw [he, neg_zero] at hleft
        dsimp only [lensChordCoordinate] at hright hleft
        rw [lensRightPoint_im hτ0 hτ1 hy] at hright
        rw [lensLeftPoint_im hτ0 hτ1 hy] at hleft
        linarith
      · rw [lensRightPoint_im hτ0 hτ1 hy, lensLeftPoint_im hτ0 hτ1 hy]

end
end Funk
