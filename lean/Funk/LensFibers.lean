import Funk.LensDiskImage
import Mathlib.Topology.DiscreteSubset

/-! Finite fibers and a zero-free inner circle for each interior target value.
These provide concrete input for future zero counting, not a proof that the
number of preimages or their total multiplicity is one. -/

open Set Metric Filter
open scoped Topology

namespace Funk
noncomputable section

def lensFiber (τ : ℝ) (w : ℂ) : Set ℂ :=
  {z ∈ closedBall 0 1 | tiltedLens τ z = w}

theorem lensFiber_isCompact (τ : ℝ) (w : ℂ) : IsCompact (lensFiber τ w) := by
  apply (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset
  · exact isClosed_closedBall.isClosed_eq (tiltedLens_diffContOnCl τ).continuousOn_ball
      continuousOn_const
  · exact fun _ hz => hz.1

theorem lensFiber_nonempty {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) {w : ℂ}
    (hw : w ∈ lensGraphBody τ) : (lensFiber τ w).Nonempty := by
  rw [← tiltedLens_image_closedBall hτ0 hτ1] at hw
  obtain ⟨z, hz, he⟩ := hw
  exact ⟨z, hz, he⟩

theorem lensFiber_subset_ball {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) {w : ℂ}
    (hw : w ∈ interior (lensGraphBody τ)) : lensFiber τ w ⊆ ball 0 1 := by
  intro z hz
  exact tiltedLens_preimage_interior_mem_ball hτ0 hτ1 hz.1 (hz.2.symm ▸ hw)

theorem tiltedLens_not_locally_constant {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {z : ℂ} (hz : z ∈ ball 0 1) (w : ℂ) :
    ¬∀ᶠ u in 𝓝 z, tiltedLens τ u = w := by
  intro h
  have ha := (tiltedLens_diffContOnCl τ).differentiableOn.analyticOnNhd isOpen_ball
  have he := ha.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    (convex_ball (0 : ℂ) 1).isPreconnected hz h
  exact tiltedLens_not_constant_on_disk hτ0 hτ1 ⟨w, he⟩

theorem tiltedLens_fiber_isolated {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {z : ℂ} (hz : z ∈ ball 0 1) (w : ℂ) :
    ∀ᶠ u in 𝓝[≠] z, tiltedLens τ u ≠ w := by
  have ha := (tiltedLens_diffContOnCl τ).differentiableOn.analyticOnNhd isOpen_ball z hz
  exact (ha.eventually_eq_or_eventually_ne analyticAt_const).resolve_left
    (tiltedLens_not_locally_constant hτ0 hτ1 hz w)

theorem lensFiber_isDiscrete {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) {w : ℂ}
    (hw : w ∈ interior (lensGraphBody τ)) : IsDiscrete (lensFiber τ w) := by
  apply isDiscrete_iff_nhdsNE.mpr
  intro z hz
  rw [inf_principal_eq_bot]
  filter_upwards [tiltedLens_fiber_isolated hτ0 hτ1 (lensFiber_subset_ball hτ0 hτ1 hw hz) w]
    with u hu
  exact fun hm => hu hm.2

theorem lensFiber_finite {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) {w : ℂ}
    (hw : w ∈ interior (lensGraphBody τ)) : (lensFiber τ w).Finite :=
  (lensFiber_isCompact τ w).finite (lensFiber_isDiscrete hτ0 hτ1 hw)

/-- All preimages of an interior point fit strictly inside a smaller circle. -/
theorem lensFiber_exists_inner_radius {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) {w : ℂ}
    (hw : w ∈ interior (lensGraphBody τ)) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ z ∈ lensFiber τ w, ‖z‖ < r := by
  obtain ⟨z, hz, hmax⟩ := (lensFiber_isCompact τ w).exists_isMaxOn
    (lensFiber_nonempty hτ0 hτ1 (interior_subset hw)) continuous_norm.continuousOn
  have hz1 : ‖z‖ < 1 := by simpa using lensFiber_subset_ball hτ0 hτ1 hw hz
  refine ⟨(‖z‖ + 1) / 2, by positivity, by linarith, ?_⟩
  intro u hu
  have hle : ‖u‖ ≤ ‖z‖ := hmax hu
  linarith

theorem tiltedLens_analyticOnNhd_inner_closedBall (τ : ℝ) {r : ℝ} (hr : r < 1) :
    AnalyticOnNhd ℂ (tiltedLens τ) (closedBall 0 r) := by
  apply ((tiltedLens_diffContOnCl τ).differentiableOn.analyticOnNhd isOpen_ball).mono
  intro z hz
  have hn : ‖z‖ ≤ r := by simpa using hz
  simpa using hn.trans_lt hr

/-- A finite fiber, contained in an interior circle where F-w has no zero.
The theorem does not assign the fiber a cardinality or a multiplicity. -/
theorem tiltedLens_innerCircle_certificate {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {w : ℂ} (hw : w ∈ interior (lensGraphBody τ)) :
    (lensFiber τ w).Finite ∧ (lensFiber τ w).Nonempty ∧
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        AnalyticOnNhd ℂ (tiltedLens τ) (closedBall 0 r) ∧
        (lensFiber τ w ⊆ ball 0 r) ∧
        ∀ z ∈ sphere (0 : ℂ) r, tiltedLens τ z ≠ w := by
  refine ⟨lensFiber_finite hτ0 hτ1 hw,
    lensFiber_nonempty hτ0 hτ1 (interior_subset hw), ?_⟩
  obtain ⟨r, hr0, hr1, hsub⟩ := lensFiber_exists_inner_radius hτ0 hτ1 hw
  refine ⟨r, hr0, hr1, tiltedLens_analyticOnNhd_inner_closedBall τ hr1,
    (fun z hz => by simpa using hsub z hz), ?_⟩
  intro z hz he
  have hn : ‖z‖ = r := by simpa using hz
  have hm : z ∈ lensFiber τ w := ⟨by simpa [hn] using hr1.le, he⟩
  have hlt := hsub z hm
  linarith

end
end Funk
