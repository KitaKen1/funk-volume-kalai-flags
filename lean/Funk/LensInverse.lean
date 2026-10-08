import Funk.LensUnivalent

/-! An actual inverse on the lens interior, with both inverse identities,
analyticity, and the derivative formula. -/

open Set Metric Filter
open scoped Topology

namespace Funk
noncomputable section

def tiltedLensInverse (τ : ℝ) : ℂ → ℂ :=
  Function.invFunOn (tiltedLens τ) (ball 0 1)

theorem tiltedLensInverse_left {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {z : ℂ} (hz : z ∈ ball 0 1) : tiltedLensInverse τ (tiltedLens τ z) = z :=
  (tiltedLens_injOn_ball hτ0 hτ1).leftInvOn_invFunOn hz

theorem tiltedLensInverse_right {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {w : ℂ} (hw : w ∈ interior (lensGraphBody τ)) :
    tiltedLens τ (tiltedLensInverse τ w) = w :=
  (tiltedLens_bijOn_ball hτ0 hτ1).surjOn.rightInvOn_invFunOn hw

theorem tiltedLensInverse_mem_ball {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {w : ℂ} (hw : w ∈ interior (lensGraphBody τ)) : tiltedLensInverse τ w ∈ ball 0 1 :=
  Function.invFunOn_mem ((tiltedLens_bijOn_ball hτ0 hτ1).surjOn hw)

theorem tiltedLensInverse_analyticOnNhd {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    AnalyticOnNhd ℂ (tiltedLensInverse τ) (interior (lensGraphBody τ)) := by
  intro w hw
  obtain ⟨z, hz, rfl⟩ := (tiltedLens_bijOn_ball hτ0 hτ1).surjOn hw
  have ha := (tiltedLens_diffContOnCl τ).differentiableOn.analyticOnNhd isOpen_ball z hz
  apply (analyticAt_comp_iff_of_deriv_ne_zero ha
    (tiltedLens_deriv_ne_zero hτ0 hτ1 (mem_ball_zero_iff.mp hz))).mp
  apply analyticAt_id.congr
  filter_upwards [isOpen_ball.mem_nhds hz] with u hu
  exact (tiltedLensInverse_left hτ0 hτ1 hu).symm

theorem hasDerivAt_tiltedLensInverse {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {w : ℂ} (hw : w ∈ interior (lensGraphBody τ)) :
    HasDerivAt (tiltedLensInverse τ)
      (deriv (tiltedLens τ) (tiltedLensInverse τ w))⁻¹ w := by
  obtain ⟨z, hz, rfl⟩ := (tiltedLens_bijOn_ball hτ0 hτ1).surjOn hw
  rw [tiltedLensInverse_left hτ0 hτ1 hz]
  have ha := (tiltedLens_diffContOnCl τ).differentiableOn.analyticOnNhd isOpen_ball z hz
  apply (ha.hasStrictDerivAt.to_local_left_inverse
    (tiltedLens_deriv_ne_zero hτ0 hτ1 (mem_ball_zero_iff.mp hz)) ?_).hasDerivAt
  filter_upwards [isOpen_ball.mem_nhds hz] with u hu
  exact tiltedLensInverse_left hτ0 hτ1 hu

theorem tiltedLens_biholomorphic {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    BijOn (tiltedLens τ) (ball 0 1) (interior (lensGraphBody τ)) ∧
      AnalyticOnNhd ℂ (tiltedLens τ) (ball 0 1) ∧
      AnalyticOnNhd ℂ (tiltedLensInverse τ) (interior (lensGraphBody τ)) ∧
      LeftInvOn (tiltedLensInverse τ) (tiltedLens τ) (ball 0 1) ∧
      RightInvOn (tiltedLensInverse τ) (tiltedLens τ) (interior (lensGraphBody τ)) :=
  ⟨tiltedLens_bijOn_ball hτ0 hτ1,
    (tiltedLens_diffContOnCl τ).differentiableOn.analyticOnNhd isOpen_ball,
    tiltedLensInverse_analyticOnNhd hτ0 hτ1,
    fun _ hz => tiltedLensInverse_left hτ0 hτ1 hz,
    fun _ hw => tiltedLensInverse_right hτ0 hτ1 hw⟩

end
end Funk
