import Funk.LensCurvature
import Funk.FeasibleRegion

/-! The branch profile is the chord coordinate of the actual boundary point.
Its first and second derivatives are obtained from the actual right profile,
including reflection on the left branch. -/

open Set Filter
open scoped Topology

namespace Funk
noncomputable section

def lensBranchProfile (τ : ℝ) (b : Bool) (y : ℝ) : ℝ :=
  if b then lensProfile τ y else -lensProfile τ (-y)

theorem lensBranchPoint_chord (τ : ℝ) (b : Bool) (y : ℝ) :
    lensChordCoordinate τ (lensBranchPoint τ b y) = lensBranchProfile τ b y := by
  cases b
  · exact lensLeftPoint_chord τ y
  · exact lensRightPoint_chord τ y

theorem lensBranchPoint_re {τ y : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (b : Bool) (hy : y ∈ Icc (-1) 1) :
    (lensBranchPoint τ b y).re =
      lensBranchProfile τ b y + (tiltedLens τ Complex.I).re * y := by
  have he := lensBranchPoint_chord τ b y
  dsimp only [lensChordCoordinate] at he
  rw [lensBranchPoint_im hτ0 hτ1 b hy] at he
  linarith

theorem lensBranchProfile_continuousOn {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (b : Bool) : ContinuousOn (lensBranchProfile τ b) (Icc (-1) 1) := by
  cases b
  · exact ((lensProfile_continuousOn hτ0 hτ1).comp continuous_neg.continuousOn
      (fun _ hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩)).neg
  · exact lensProfile_continuousOn hτ0 hτ1

def lensBranchProfileSlope (τ : ℝ) (b : Bool) (y : ℝ) : ℝ :=
  deriv (lensProfile τ) (if b then y else -y)

def lensBranchProfileCurvature (τ : ℝ) (b : Bool) (y : ℝ) : ℝ :=
  if b then lensProfileCurvature τ y else -lensProfileCurvature τ (-y)

theorem hasDerivAt_lensBranchProfile {τ y : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (b : Bool) (hy : y ∈ Ioo (-1) 1) :
    HasDerivAt (lensBranchProfile τ b) (lensBranchProfileSlope τ b y) y := by
  cases b
  · have hn : -y ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have hd := (((hasDerivAt_lensProfile hτ0 hτ1 hn).differentiableAt.hasDerivAt).comp y
      ((hasDerivAt_id y).neg)).neg
    convert hd using 1
    all_goals first | rfl | simp [lensBranchProfileSlope]
  · exact (hasDerivAt_lensProfile hτ0 hτ1 hy).differentiableAt.hasDerivAt

theorem hasDerivAt_lensBranchProfileSlope {τ y : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (b : Bool) (hy : y ∈ Ioo (-1) 1) :
    HasDerivAt (lensBranchProfileSlope τ b) (lensBranchProfileCurvature τ b y) y := by
  cases b
  · have hn : -y ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hy.2], by linarith [hy.1]⟩
    convert (hasDerivAt_lensProfile_deriv hτ0 hτ1 hn).comp y ((hasDerivAt_id y).neg) using 1
    all_goals first | rfl | simp [lensBranchProfileCurvature]
  · exact hasDerivAt_lensProfile_deriv hτ0 hτ1 hy

theorem lensBranchProfileCurvature_ne_zero {τ y : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (b : Bool) (hy : y ∈ Ioo (-1) 1) : lensBranchProfileCurvature τ b y ≠ 0 := by
  cases b
  · exact neg_ne_zero.mpr (lensProfileCurvature_neg hτ0 hτ1
      ⟨by linarith [hy.2], by linarith [hy.1]⟩).ne
  · exact (lensProfileCurvature_neg hτ0 hτ1 hy).ne

theorem lensBranchProfile_second_deriv_ne_zero {τ y : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (b : Bool) (hy : y ∈ Ioo (-1) 1) :
    deriv (deriv (lensBranchProfile τ b)) y ≠ 0 := by
  have he : deriv (lensBranchProfile τ b) =ᶠ[𝓝 y] lensBranchProfileSlope τ b := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with u hu
    exact (hasDerivAt_lensBranchProfile hτ0 hτ1 b hu).deriv
  rw [((hasDerivAt_lensBranchProfileSlope hτ0 hτ1 b hy).congr_of_eventuallyEq he).deriv]
  exact lensBranchProfileCurvature_ne_zero hτ0 hτ1 b hy

end
end Funk
