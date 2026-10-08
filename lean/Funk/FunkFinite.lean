import Funk.CubeFunk

/-! Finiteness of the actual Funk integral for every compact convex body
containing zero in its interior. No symmetry or lower-bound hypothesis is used. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

/-- Interior at zero supplies a uniform radius in every coordinate direction. -/
theorem exists_axis_radius {n : ℕ} {K : Set (Space n)} (hK : 0 ∈ interior K) :
    ∃ r : ℝ, 0 < r ∧ ∀ i : Fin n, ∀ a : ℝ, |a| ≤ r → Pi.single i a ∈ K := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hK)
  refine ⟨ε / 2, by positivity, ?_⟩
  intro i a ha
  apply hball
  rw [Metric.mem_ball, dist_zero_right, Pi.norm_single, Real.norm_eq_abs]
  linarith

/-- Convex interpolation transports each inner direction to any contracted point. -/
theorem axis_mem_translate {n : ℕ} {K : Set (Space n)} (hK : Convex ℝ K)
    {r τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hr : ∀ i : Fin n, ∀ a : ℝ, |a| ≤ r → Pi.single i a ∈ K)
    {X : Space n} (hX : X ∈ K) (i : Fin n) (a : ℝ) (ha : |a| ≤ r) :
    Pi.single i ((1 - τ) * a) ∈ translate K (τ • X) := by
  refine ⟨τ • X + (1 - τ) • Pi.single i a,
    hK hX (hr i a ha) hτ0 (by linarith) (by ring), ?_⟩
  ext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [Pi.single_eq_of_ne hji]

theorem convex_polar_subset_box {n : ℕ} {K : Set (Space n)} (hK : Convex ℝ K)
    {r τ : ℝ} (hr0 : 0 < r) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hr : ∀ i : Fin n, ∀ a : ℝ, |a| ≤ r → Pi.single i a ∈ K)
    {X : Space n} (hX : X ∈ K) :
    coordinatePolar (translate K (τ • X)) ⊆
      coordinateBox n (-(1 / ((1 - τ) * r))) (1 / ((1 - τ) * r)) := by
  intro y hy
  rw [mem_coordinateBox]
  intro i
  have hg : 0 < (1 - τ) * r := mul_pos (by linarith) hr0
  have hp := hy _ (axis_mem_translate hK hτ0 hτ1 hr hX i r (by rw [abs_of_pos hr0]))
  have hm := hy _ (axis_mem_translate hK hτ0 hτ1 hr hX i (-r) (by rw [abs_neg, abs_of_pos hr0]))
  rw [dotProduct_single] at hp hm
  refine ⟨?_, (le_div_iff₀ hg).mpr hp⟩
  have hn : -y i ≤ 1 / ((1 - τ) * r) := (le_div_iff₀ hg).mpr (by nlinarith)
  linarith

theorem convex_polar_volume_upper {n : ℕ} {K : Set (Space n)} (hK : Convex ℝ K)
    {r τ : ℝ} (hr0 : 0 < r) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hr : ∀ i : Fin n, ∀ a : ℝ, |a| ≤ r → Pi.single i a ∈ K)
    {X : Space n} (hX : X ∈ K) :
    volume (coordinatePolar (translate K (τ • X))) ≤
      ENNReal.ofReal (2 / ((1 - τ) * r)) ^ n := by
  calc
    _ ≤ volume (coordinateBox n (-(1 / ((1 - τ) * r))) (1 / ((1 - τ) * r))) :=
      measure_mono (convex_polar_subset_box hK hr0 hτ0 hτ1 hr hX)
    _ = _ := by rw [volume_coordinateBox]; congr 2; ring

/-- A finite constant dominates the kernel uniformly over the contracted body. -/
theorem funkVolume_convex_upper {n : ℕ} {K : Set (Space n)}
    (hc : IsCompact K) (hv : Convex ℝ K) {r τ : ℝ}
    (hr0 : 0 < r) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hr : ∀ i : Fin n, ∀ a : ℝ, |a| ≤ r → Pi.single i a ∈ K) :
    funkVolume K τ ≤ ENNReal.ofReal (2 / ((1 - τ) * r)) ^ n *
      volume ((fun X : Space n => τ • X) '' K) := by
  have hs : IsCompact ((fun X : Space n => τ • X) '' K) :=
    hc.image (continuous_id.const_smul τ)
  unfold funkVolume
  calc
    _ ≤ ∫⁻ _x in (fun X : Space n => τ • X) '' K,
        ENNReal.ofReal (2 / ((1 - τ) * r)) ^ n := by
      apply setLIntegral_mono' hs.measurableSet
      rintro x ⟨X, hX, rfl⟩
      exact convex_polar_volume_upper hv hr0 hτ0 hτ1 hr hX
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]

/-- The finiteness half of the frozen Funk target, in all dimensions. -/
theorem funkVolume_convex_finite {n : ℕ} {K : Set (Space n)}
    (hc : IsCompact K) (hv : Convex ℝ K) (hi : 0 ∈ interior K)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) : funkVolume K τ < ⊤ := by
  obtain ⟨r, hr0, hr⟩ := exists_axis_radius hi
  have hs : volume ((fun X : Space n => τ • X) '' K) < ⊤ :=
    (hc.image (show Continuous (fun X : Space n => τ • X) from
      continuous_id.const_smul τ)).measure_lt_top
  apply lt_of_le_of_lt (funkVolume_convex_upper hc hv hr0 hτ0 hτ1 hr)
  exact ENNReal.mul_lt_top (by finiteness) hs

theorem funkVolume_symmetricConvexBody_finite {n : ℕ} {K : Set (Space n)}
    (hK : IsSymmetricConvexBody K) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    funkVolume K τ < ⊤ :=
  funkVolume_convex_finite hK.1 hK.2.1 hK.2.2.2 hτ0.le hτ1

end
end Funk
