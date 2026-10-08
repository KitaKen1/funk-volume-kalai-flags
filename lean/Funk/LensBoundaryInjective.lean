import Funk.LensArcSeparation

/-! Injectivity of the actual lens map on the entire unit circle.  Distinct
parameters in one period are separated using the two arcs and their endpoints.
This is a boundary result, not injectivity on the open disk. -/

open Set

namespace Funk
noncomputable section

theorem lensBoundary_meeting_endpoints {τ θ φ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hθ : θ ∈ Icc (-Real.pi / 2) (Real.pi / 2))
    (hφ : φ ∈ Icc (-Real.pi / 2) (Real.pi / 2))
    (heq : lensRadialTrace τ 1 θ = lensRadialTrace τ 1 (φ + Real.pi)) :
    (θ = -Real.pi / 2 ∧ φ = Real.pi / 2) ∨
      (θ = Real.pi / 2 ∧ φ = -Real.pi / 2) := by
  have hends : -Real.pi / 2 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hinj := lensBoundary_injOn_right hτ0 hτ1
  rcases lensBoundary_meeting_is_endpoint hτ0 hτ1 hθ hφ heq with hl | hr
  · left
    refine ⟨hl, ?_⟩
    rw [hl, lensBoundary_opposite_endpoints, lensRadialTrace_add_pi] at heq
    exact hinj hφ (right_mem_Icc.mpr hends) (neg_injective heq.symm)
  · right
    refine ⟨hr, ?_⟩
    rw [hr, lensRadialTrace_add_pi] at heq
    apply hinj hφ (left_mem_Icc.mpr hends)
    rw [lensBoundary_opposite_endpoints, heq, neg_neg]

theorem lensBoundary_ne_opposite_Ioc {τ θ φ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hθ : θ ∈ Ioc (-Real.pi / 2) (Real.pi / 2))
    (hφ : φ ∈ Ioc (-Real.pi / 2) (Real.pi / 2)) :
    lensRadialTrace τ 1 θ ≠ lensRadialTrace τ 1 (φ + Real.pi) := by
  intro h
  rcases lensBoundary_meeting_endpoints hτ0 hτ1 ⟨hθ.1.le, hθ.2⟩
    ⟨hφ.1.le, hφ.2⟩ h with he | he
  · linarith [he.1, hθ.1]
  · linarith [he.2, hφ.1]

theorem lensBoundary_injOn_period {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    InjOn (lensRadialTrace τ 1) (Ioc (-Real.pi / 2) (3 * Real.pi / 2)) := by
  intro x hx y hy hxy
  have hinj := lensBoundary_injOn_right hτ0 hτ1
  by_cases hxr : x ≤ Real.pi / 2
  · by_cases hyr : y ≤ Real.pi / 2
    · exact hinj ⟨hx.1.le, hxr⟩ ⟨hy.1.le, hyr⟩ hxy
    · have hs : y - Real.pi ∈ Ioc (-Real.pi / 2) (Real.pi / 2) :=
        ⟨by linarith, by linarith [hy.2]⟩
      exact False.elim (lensBoundary_ne_opposite_Ioc hτ0 hτ1 ⟨hx.1, hxr⟩ hs
        (by simpa only [sub_add_cancel] using hxy))
  · have hsx : x - Real.pi ∈ Ioc (-Real.pi / 2) (Real.pi / 2) :=
      ⟨by linarith, by linarith [hx.2]⟩
    by_cases hyr : y ≤ Real.pi / 2
    · exact False.elim (lensBoundary_ne_opposite_Ioc hτ0 hτ1 ⟨hy.1, hyr⟩ hsx
        (by simpa only [sub_add_cancel] using hxy.symm))
    · have hsy : y - Real.pi ∈ Ioc (-Real.pi / 2) (Real.pi / 2) :=
        ⟨by linarith, by linarith [hy.2]⟩
      have he : lensRadialTrace τ 1 (x - Real.pi) = lensRadialTrace τ 1 (y - Real.pi) := by
        apply neg_injective
        rw [← lensRadialTrace_add_pi, ← lensRadialTrace_add_pi]
        simpa only [sub_add_cancel] using hxy
      have h := hinj ⟨hsx.1.le, hsx.2⟩ ⟨hsy.1.le, hsy.2⟩ he
      linarith

theorem circleMap_image_lens_period :
    circleMap 0 1 '' Ioc (-Real.pi / 2) (3 * Real.pi / 2) = {z : ℂ | ‖z‖ = 1} := by
  have hi : -Real.pi / 2 + 2 * Real.pi = 3 * Real.pi / 2 := by ring
  rw [← hi, (periodic_circleMap 0 1).image_Ioc Real.two_pi_pos, range_circleMap]
  ext z
  simp

/-- Injectivity of the actual infinite-series map on the whole unit circle. -/
theorem tiltedLens_injOn_unitCircle {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    InjOn (tiltedLens τ) {z : ℂ | ‖z‖ = 1} := by
  intro z hz w hw heq
  rw [← circleMap_image_lens_period] at hz hw
  obtain ⟨θ, hθ, rfl⟩ := hz
  obtain ⟨φ, hφ, rfl⟩ := hw
  have h := lensBoundary_injOn_period hτ0 hτ1 hθ hφ heq
  rw [h]

/-- A closed embedding of the unit circle into the plane.  No convexity or
identification with the frontier of the open-disk image is asserted here. -/
theorem tiltedLens_isClosedEmbedding_unitCircle {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    Topology.IsClosedEmbedding (fun z : {z : ℂ | ‖z‖ = 1} => tiltedLens τ z) := by
  have hk : IsCompact {z : ℂ | ‖z‖ = 1} := by
    simpa [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : ℂ) (1 : ℝ)
  let : CompactSpace {z : ℂ | ‖z‖ = 1} := isCompact_iff_compactSpace.mp hk
  have hc : ContinuousOn (tiltedLens τ) {z : ℂ | ‖z‖ = 1} :=
    (tiltedLens_continuousOn τ).mono (fun z hz => hz.le)
  apply (continuousOn_iff_continuous_domRestrict.mp hc).isClosedEmbedding
  intro z w h
  exact Subtype.ext (tiltedLens_injOn_unitCircle hτ0 hτ1 z.property w.property h)

end
end Funk
