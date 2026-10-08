import Funk.IrredundantDirections
import Funk.LensBranchCurvature

/-! Extra activity is exactly a zero of an explicit real residual in basis
coordinates. The endpoint chord cancels. No zero-set nullity is assumed or
concluded here. -/

open Set Matrix MeasureTheory

namespace Funk
noncomputable section

def branchCollisionResidual {n : ℕ} (τ : ℝ) (b : Fin n → Bool) (σ : Bool)
    (coeff t : Space n) : ℝ :=
  dotProduct coeff (fun i => lensBranchProfile τ (b i) (t i)) -
    lensBranchProfile τ σ (dotProduct coeff t)

theorem lensGraphBody_frontier_iff_branch {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (z : ℂ) : z ∈ frontier (lensGraphBody τ) ↔
      ∃ b : Bool, z = lensBranchPoint τ b z.im := by
  constructor
  · intro hz
    have ha := lensGraphBody_frontier_subset_circleImage hτ0 hτ1 hz
    rw [lensCircleImage_eq_arcs hτ0 hτ1] at ha
    rcases ha with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
    · exact ⟨true, by rw [lensRightPoint_im hτ0 hτ1 hy]; rfl⟩
    · exact ⟨false, by rw [lensLeftPoint_im hτ0 hτ1 hy]; rfl⟩
  · rintro ⟨b, he⟩
    rw [he]
    exact lensBranchPoint_mem_frontier hτ0 hτ1 b

theorem lensGraphBody_frontier_iff_profile {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {z : ℂ} (hz : z.im ∈ Icc (-1) 1) : z ∈ frontier (lensGraphBody τ) ↔
      ∃ b : Bool, lensChordCoordinate τ z = lensBranchProfile τ b z.im := by
  rw [lensGraphBody_frontier_iff_branch hτ0 hτ1]
  apply exists_congr
  intro b
  constructor
  · intro he
    exact (congr_arg (lensChordCoordinate τ) he).trans (lensBranchPoint_chord τ b z.im)
  · intro he
    apply Complex.ext
    · have hr := lensBranchPoint_re hτ0 hτ1 b hz
      dsimp only [lensChordCoordinate] at he
      linarith
    · exact (lensBranchPoint_im hτ0 hτ1 b hz).symm

theorem row_witness_chord {n : ℕ} {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (b : Fin n → Bool) {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.det ≠ 0)
    (a : Space n) {X : Space n} (hX : X ∈ stripBody B) :
    lensChordCoordinate τ (complexRow a (basisRealWitness τ b B X) X) =
      dotProduct (rowBasisCoefficients B a)
        (fun i => lensBranchProfile τ (b i) (basisMap B X i)) := by
  have hr : dotProduct a (basisRealWitness τ b B X) =
      dotProduct (rowBasisCoefficients B a)
        (fun i => (lensBranchPoint τ (b i) (basisMap B X i)).re) := by
    rw [← rowBasisCoefficients_dot hB, basisMap_realWitness τ b hB]
  have he : (fun i => (lensBranchPoint τ (b i) (basisMap B X i)).re) =
      (fun i => lensBranchProfile τ (b i) (basisMap B X i)) +
        (tiltedLens τ Complex.I).re • basisMap B X := by
    funext i
    exact lensBranchPoint_re hτ0 hτ1 (b i) (abs_le.mp (hX i))
  change dotProduct a (basisRealWitness τ b B X) -
    (tiltedLens τ Complex.I).re * dotProduct a X = _
  rw [hr, he, dotProduct_add, dotProduct_smul, smul_eq_mul,
    rowBasisCoefficients_dot hB]
  ring

/-- Activity on the actual lens frontier, not an abstract replacement curve. -/
theorem extra_active_iff_residual_zero {n : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (b : Fin n → Bool)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.det ≠ 0) (a : Space n)
    {X : Space n} (hX : X ∈ stripBody B) (ha : |dotProduct a X| ≤ 1) :
    complexRow a (basisRealWitness τ b B X) X ∈ frontier (lensGraphBody τ) ↔
      ∃ σ : Bool, branchCollisionResidual τ b σ (rowBasisCoefficients B a)
        (basisMap B X) = 0 := by
  rw [lensGraphBody_frontier_iff_profile hτ0 hτ1 (abs_le.mp ha),
    row_witness_chord hτ0 hτ1 b hB a hX]
  simp only [branchCollisionResidual, sub_eq_zero, rowBasisCoefficients_dot hB,
    complexRow]

theorem measurable_lensBranchProfile (τ : ℝ) (b : Bool) :
    Measurable (lensBranchProfile τ b) := by
  have hm := (lensChordCoordinate_continuous τ).measurable.comp
    (measurable_lensBranchPoint τ b)
  simpa only [Function.comp_def, lensBranchPoint_chord] using hm

theorem measurable_branchCollisionResidual {n : ℕ} (τ : ℝ) (b : Fin n → Bool)
    (σ : Bool) (coeff : Space n) : Measurable (branchCollisionResidual τ b σ coeff) := by
  unfold branchCollisionResidual dotProduct
  apply Measurable.sub
  · exact Finset.measurable_sum _ (fun i _ =>
      measurable_const.mul ((measurable_lensBranchProfile τ (b i)).comp (measurable_pi_apply i)))
  · apply (measurable_lensBranchProfile τ σ).comp
    fun_prop

theorem measurableSet_collision_residual_zero {n : ℕ} (τ : ℝ) (b : Fin n → Bool)
    (σ : Bool) (coeff : Space n) : MeasurableSet {t | branchCollisionResidual τ b σ coeff t = 0} :=
  measurableSet_eq_fun (measurable_branchCollisionResidual τ b σ coeff) measurable_const

end
end Funk
