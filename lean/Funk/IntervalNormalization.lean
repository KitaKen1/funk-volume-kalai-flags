import Funk.Targets
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! One-dimensional calibration with the actual coordinate polar and Lebesgue
measure. No freely specified volume function is used in the geometric lemmas.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Funk

noncomputable section

def coordinateInterval (a b : ℝ) : Set (Space 1) := {z | z 0 ∈ Icc a b}

theorem coordinateInterval_eq_pi (a b : ℝ) :
    coordinateInterval a b = Set.pi Set.univ (fun _ : Fin 1 => Icc a b) := by
  ext z
  change z 0 ∈ Icc a b ↔ ∀ i : Fin 1, i ∈ Set.univ → z i ∈ Icc a b
  constructor
  · intro h i _
    fin_cases i
    exact h
  · intro h
    exact h 0 (Set.mem_univ _)

theorem volume_coordinateInterval (a b : ℝ) :
    volume (coordinateInterval a b) = ENNReal.ofReal (b - a) := by
  rw [coordinateInterval_eq_pi, volume_pi_pi]
  simp [Real.volume_Icc]

theorem scalar_interval_polar_iff {r x y : ℝ} (hr : 0 < r)
    (hxl : -r < x) (hxu : x < r) :
    (∀ z : ℝ, -r ≤ z → z ≤ r → y * (z - x) ≤ 1) ↔
      -(1 / (r + x)) ≤ y ∧ y ≤ 1 / (r - x) := by
  have hp : 0 < r + x := by linarith
  have hm : 0 < r - x := by linarith
  constructor
  · intro h
    constructor
    · have hy : -y ≤ 1 / (r + x) := (le_div_iff₀ hp).mpr (by
        have hh := h (-r) le_rfl (by linarith)
        nlinarith)
      linarith
    · exact (le_div_iff₀ hm).mpr (h r (by linarith) le_rfl)
  · rintro ⟨hyl, hyu⟩ z hzl hzu
    by_cases hy : 0 ≤ y
    · exact (mul_le_mul_of_nonneg_left (sub_le_sub_right hzu x) hy).trans
        ((le_div_iff₀ hm).mp hyu)
    · have hneg : -y * (r + x) ≤ 1 :=
        (le_div_iff₀ hp).mp (by linarith : -y ≤ 1 / (r + x))
      have hz := mul_le_mul_of_nonpos_left (sub_le_sub_right hzl x) (le_of_not_ge hy)
      nlinarith

theorem polar_translated_coordinateInterval {r : ℝ} {x : Space 1} (hr : 0 < r)
    (hxl : -r < x 0) (hxu : x 0 < r) :
    coordinatePolar (translate (coordinateInterval (-r) r) x) =
      coordinateInterval (-(1 / (r + x 0))) (1 / (r - x 0)) := by
  ext y
  change (∀ z ∈ translate (coordinateInterval (-r) r) x, dotProduct y z ≤ 1) ↔ _
  change _ ↔ -(1 / (r + x 0)) ≤ y 0 ∧ y 0 ≤ 1 / (r - x 0)
  rw [← scalar_interval_polar_iff hr hxl hxu]
  constructor
  · intro hy z hzl hzu
    have h := hy ((fun _ : Fin 1 => z) - x) ⟨(fun _ => z), ⟨hzl, hzu⟩, rfl⟩
    simpa [dotProduct, Fin.sum_univ_one] using h
  · intro hy z hz
    obtain ⟨w, hw, rfl⟩ := hz
    simpa [dotProduct, Fin.sum_univ_one] using hy (w 0) hw.1 hw.2

theorem volume_polar_translated_coordinateInterval {r : ℝ} {x : Space 1} (hr : 0 < r)
    (hxl : -r < x 0) (hxu : x 0 < r) :
    volume (coordinatePolar (translate (coordinateInterval (-r) r) x)) =
      ENNReal.ofReal (1 / (r - x 0) + 1 / (r + x 0)) := by
  rw [polar_translated_coordinateInterval hr hxl hxu, volume_coordinateInterval]
  simp

theorem interval_kernel_integrable {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    IntervalIntegrable (fun x : ℝ => 1 / (1 - x) + 1 / (1 + x)) volume (-τ) τ := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by linarith : -τ ≤ τ)]
  apply ContinuousOn.add
  · apply continuousOn_const.div (continuousOn_const.sub continuousOn_id)
    intro x hx
    change 1 - x ≠ 0
    linarith [hx.2]
  · apply continuousOn_const.div (continuousOn_const.add continuousOn_id)
    intro x hx
    change 1 + x ≠ 0
    linarith [hx.1]

theorem interval_kernel_integral {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    (∫ x in (-τ)..τ, (1 / (1 - x) + 1 / (1 + x))) = 4 * Real.artanh τ := by
  have hminus : IntervalIntegrable (fun x : ℝ => 1 / (1 - x)) volume (-τ) τ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith : -τ ≤ τ)]
    apply continuousOn_const.div (continuousOn_const.sub continuousOn_id)
    intro x hx
    change 1 - x ≠ 0
    linarith [hx.2]
  have hplus : IntervalIntegrable (fun x : ℝ => 1 / (1 + x)) volume (-τ) τ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith : -τ ≤ τ)]
    apply continuousOn_const.div (continuousOn_const.add continuousOn_id)
    intro x hx
    change 1 + x ≠ 0
    linarith [hx.1]
  rw [intervalIntegral.integral_add hminus hplus]
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => 1 / x) 1,
    intervalIntegral.integral_comp_add_left (fun x : ℝ => 1 / x) 1]
  rw [integral_one_div_of_pos (by linarith) (by linarith),
    integral_one_div_of_pos (by linarith) (by linarith)]
  rw [Real.artanh_eq_half_log ⟨by linarith, hτ₁.le⟩]
  simp only [sub_neg_eq_add, ← sub_eq_add_neg]
  ring

theorem scaled_unit_coordinateInterval {τ : ℝ} (hτ : 0 < τ) :
    (fun y : Space 1 => τ • y) '' coordinateInterval (-1) 1 = coordinateInterval (-τ) τ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change -τ ≤ τ * y 0 ∧ τ * y 0 ≤ τ
    change -1 ≤ y 0 ∧ y 0 ≤ 1 at hy
    constructor <;> nlinarith [hy.1, hy.2]
  · intro hx
    change -τ ≤ x 0 ∧ x 0 ≤ τ at hx
    refine ⟨fun i => x i / τ, ?_, ?_⟩
    · change -1 ≤ x 0 / τ ∧ x 0 / τ ≤ 1
      constructor
      · apply (le_div_iff₀ hτ).mpr
        simpa using hx.1
      · apply (div_le_iff₀ hτ).mpr
        simpa using hx.2
    · ext i
      change τ * (x i / τ) = x i
      field_simp

theorem lintegral_coordinateInterval (a b : ℝ) (g : ℝ → ℝ≥0∞) :
    (∫⁻ z in coordinateInterval a b, g (z 0)) = ∫⁻ t in Icc a b, g t := by
  exact (volume_preserving_piUnique (fun _ : Fin 1 => ℝ)).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)).measurableEmbedding g (Icc a b)

theorem lintegral_interval_kernel {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    (∫⁻ x in Icc (-τ) τ, ENNReal.ofReal (1 / (1 - x) + 1 / (1 + x))) =
      ENNReal.ofReal (4 * Real.artanh τ) := by
  have hab : -τ ≤ τ := by linarith
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
    (interval_kernel_integrable hτ₀ hτ₁)
  have hn : 0 ≤ᵐ[volume.restrict (Icc (-τ) τ)]
      (fun x : ℝ => 1 / (1 - x) + 1 / (1 + x)) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with x hx
    have hm : 0 < 1 - x := by linarith [hx.2]
    have hp : 0 < 1 + x := by linarith [hx.1]
    exact add_nonneg (div_nonneg (by norm_num) hm.le) (div_nonneg (by norm_num) hp.le)
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    interval_kernel_integral hτ₀ hτ₁]

/-- Exact calibration of the actual Funk-volume definition for the unit interval.
This is a proved example in dimension one, not the all-dimensional target. -/
theorem funkVolume_unit_interval {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    funkVolume (coordinateInterval (-1) 1) τ = ENNReal.ofReal (4 * Real.artanh τ) := by
  unfold funkVolume
  rw [scaled_unit_coordinateInterval hτ₀]
  have heq :
      (∫⁻ x in coordinateInterval (-τ) τ,
        volume (coordinatePolar (translate (coordinateInterval (-1) 1) x))) =
      ∫⁻ x in coordinateInterval (-τ) τ,
        ENNReal.ofReal (1 / (1 - x 0) + 1 / (1 + x 0)) := by
    apply setLIntegral_congr_fun
      (measurableSet_Icc.preimage (measurable_pi_apply 0))
    intro x hx
    change -τ ≤ x 0 ∧ x 0 ≤ τ at hx
    exact volume_polar_translated_coordinateInterval (by norm_num)
      (by linarith [hx.1]) (by linarith [hx.2])
  rw [heq, lintegral_coordinateInterval (-τ) τ
    (fun t => ENNReal.ofReal (1 / (1 - t) + 1 / (1 + t))),
    lintegral_interval_kernel hτ₀ hτ₁]

theorem funkVolume_unit_interval_finite {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    funkVolume (coordinateInterval (-1) 1) τ < ⊤ := by
  rw [funkVolume_unit_interval hτ₀ hτ₁]
  exact ENNReal.ofReal_lt_top

theorem unit_coordinateInterval_isSymmetricConvexBody :
    IsSymmetricConvexBody (coordinateInterval (-1) 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [coordinateInterval_eq_pi, Set.pi_univ_Icc]
    exact isCompact_Icc
  · rw [coordinateInterval_eq_pi, Set.pi_univ_Icc]
    exact convex_Icc _ _
  · intro x hx
    change -1 ≤ x 0 ∧ x 0 ≤ 1 at hx
    change -1 ≤ -(x 0) ∧ -(x 0) ≤ 1
    constructor <;> linarith [hx.1, hx.2]
  · apply mem_interior.mpr
    refine ⟨(fun x : Space 1 => x 0) ⁻¹' Ioo (-1) 1, ?_,
      isOpen_Ioo.preimage (continuous_apply 0), ?_⟩
    · intro x hx
      exact ⟨hx.1.le, hx.2.le⟩
    · norm_num

end
end Funk
