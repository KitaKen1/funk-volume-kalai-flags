import Funk.BranchDensity
import Funk.IntervalNormalization
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Constructions.Pi

/-! Probability measures for the branch/height model.
Rows are independent by the explicit product construction. The sign and height
within a row are kept together; no independence between them is assumed.
Identification with the actual complex boundary and its independent row products
is proved in LensBoundaryMeasure and LensBoundaryProbability. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk

noncomputable section

def branchSign (b : Bool) : ℝ := if b then 1 else -1

theorem branchSign_cases (b : Bool) : branchSign b = 1 ∨ branchSign b = -1 := by
  cases b <;> simp [branchSign]

theorem measurable_branchDensity (τ ε : ℝ) : Measurable (branchDensity τ ε) := by
  unfold branchDensity
  fun_prop

theorem continuousOn_branchDensity {τ ε : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1)
    (hε : ε = 1 ∨ ε = -1) : ContinuousOn (branchDensity τ ε) (Icc (-1) 1) := by
  unfold branchDensity
  apply continuousOn_const.div
  · fun_prop
  · intro t ht
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Real.artanh_pos ⟨hτ₀, hτ₁⟩).ne')
      (denominator_pos hτ₀.le hτ₁ hε (abs_le.mpr ht)).ne'

/-- An unnormalised branch has mass one half, including its branch probability. -/
def branchMeasure (τ ε : ℝ) : Measure ℝ :=
  (volume.restrict (Icc (-1) 1)).withDensity (fun t => ENNReal.ofReal (branchDensity τ ε t))

theorem branchMeasure_apply (τ ε : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    branchMeasure τ ε s = ∫⁻ t in s ∩ Icc (-1) 1, ENNReal.ofReal (branchDensity τ ε t) := by
  rw [branchMeasure, withDensity_apply _ hs, Measure.restrict_restrict hs]

theorem branchMeasure_univ {τ ε : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1)
    (hε : ε = 1 ∨ ε = -1) : branchMeasure τ ε Set.univ = 1 / 2 := by
  rw [branchMeasure_apply _ _ MeasurableSet.univ, Set.univ_inter]
  have hi : IntegrableOn (branchDensity τ ε) (Icc (-1) 1) volume :=
    (continuousOn_branchDensity hτ₀ hτ₁ hε).integrableOn_Icc
  have hn : 0 ≤ᵐ[volume.restrict (Icc (-1) 1)] branchDensity τ ε := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t ht
    exact (branchDensity_pos hτ₀ hτ₁ hε (abs_le.mpr ht)).le
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rcases hε with rfl | rfl
  · rw [positiveBranch_mass hτ₀ hτ₁, ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  · rw [negativeBranch_mass hτ₀ hτ₁, ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num

theorem branchMeasure_outside (τ ε : ℝ) : branchMeasure τ ε (Icc (-1) 1)ᶜ = 0 := by
  rw [branchMeasure_apply _ _ measurableSet_Icc.compl]
  simp

theorem branchMeasure_singleton (τ ε t : ℝ) : branchMeasure τ ε {t} = 0 := by
  unfold branchMeasure
  exact measure_singleton t

/-- The two tags distinguish the branches even when their heights coincide. -/
def branchJoint (τ : ℝ) : Measure (Bool × ℝ) :=
  (branchMeasure τ 1).map (Prod.mk true) + (branchMeasure τ (-1)).map (Prod.mk false)

theorem branchJoint_univ {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    branchJoint τ Set.univ = 1 := by
  rw [branchJoint, Measure.add_apply]
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ,
    Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simp only [Set.preimage_univ]
  rw [branchMeasure_univ hτ₀ hτ₁ (Or.inl rfl),
    branchMeasure_univ hτ₀ hτ₁ (Or.inr rfl)]
  exact ENNReal.add_halves 1

theorem branchJoint_isProbability {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    IsProbabilityMeasure (branchJoint τ) := ⟨branchJoint_univ hτ₀ hτ₁⟩

/-- Exact joint event law, retaining the dependence of height on the branch. -/
theorem branchJoint_slice (τ : ℝ) (b : Bool) {s : Set ℝ} (hs : MeasurableSet s) :
    branchJoint τ ({b} ×ˢ s) = branchMeasure τ (branchSign b) s := by
  rw [branchJoint, Measure.add_apply]
  rw [Measure.map_apply (by fun_prop) ((measurableSet_singleton b).prod hs),
    Measure.map_apply (by fun_prop) ((measurableSet_singleton b).prod hs)]
  cases b <;> simp [branchSign]

theorem branchJoint_sign_mass {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) (b : Bool) :
    branchJoint τ ({b} ×ˢ (Set.univ : Set ℝ)) = 1 / 2 := by
  rw [branchJoint_slice _ _ MeasurableSet.univ]
  exact branchMeasure_univ hτ₀ hτ₁ (branchSign_cases b)

theorem branchJoint_height_singleton (τ t : ℝ) :
    branchJoint τ (Set.univ ×ˢ ({t} : Set ℝ)) = 0 := by
  rw [branchJoint, Measure.add_apply]
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ.prod (measurableSet_singleton t)),
    Measure.map_apply (by fun_prop) (MeasurableSet.univ.prod (measurableSet_singleton t))]
  simp [branchMeasure_singleton]

theorem branchJoint_height_support {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    branchJoint τ (Set.univ ×ˢ Icc (-1) 1) = 1 := by
  have he (ε : ℝ) : branchMeasure τ ε (Icc (-1) 1) = branchMeasure τ ε Set.univ := by
    rw [branchMeasure_apply _ _ measurableSet_Icc,
      branchMeasure_apply _ _ MeasurableSet.univ]
    simp
  rw [branchJoint, Measure.add_apply]
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ.prod measurableSet_Icc),
    Measure.map_apply (by fun_prop) (MeasurableSet.univ.prod measurableSet_Icc)]
  have hp (b : Bool) : Prod.mk b ⁻¹' (Set.univ ×ˢ Icc (-1 : ℝ) 1) = Icc (-1) 1 := by
    ext t
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]
  rw [hp, hp]
  rw [he, he, branchMeasure_univ hτ₀ hτ₁ (Or.inl rfl),
    branchMeasure_univ hτ₀ hτ₁ (Or.inr rfl)]
  exact ENNReal.add_halves 1

/-- Independence between rows is encoded here, not inside the single-row measure. -/
def rowJoint (m : ℕ) (τ : ℝ) : Measure (Fin m → Bool × ℝ) :=
  Measure.pi (fun _ => branchJoint τ)

theorem rowJoint_isProbability (m : ℕ) {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    IsProbabilityMeasure (rowJoint m τ) := by
  let := branchJoint_isProbability hτ₀ hτ₁
  unfold rowJoint
  infer_instance

theorem rowJoint_box (m : ℕ) {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1)
    (b : Fin m → Bool) (s : Fin m → Set ℝ) (hs : ∀ i, MeasurableSet (s i)) :
    rowJoint m τ (Set.pi Set.univ (fun i => {b i} ×ˢ s i)) =
      ∏ i, branchMeasure τ (branchSign (b i)) (s i) := by
  let := branchJoint_isProbability hτ₀ hτ₁
  rw [rowJoint, Measure.pi_pi]
  apply Finset.prod_congr rfl
  intro i _
  exact branchJoint_slice τ (b i) (hs i)

theorem rowJoint_signs_mass (m : ℕ) {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1)
    (b : Fin m → Bool) :
    rowJoint m τ (Set.pi Set.univ (fun i => {b i} ×ˢ (Set.univ : Set ℝ))) =
      (1 / 2 : ℝ≥0∞) ^ m := by
  rw [rowJoint_box m hτ₀ hτ₁ b (fun _ => Set.univ) (fun _ => MeasurableSet.univ)]
  simp_rw [branchMeasure_univ hτ₀ hτ₁ (branchSign_cases _)]
  simp

theorem rowJoint_height_support (m : ℕ) {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    rowJoint m τ (Set.pi Set.univ (fun _ => Set.univ ×ˢ Icc (-1) 1)) = 1 := by
  let := branchJoint_isProbability hτ₀ hτ₁
  rw [rowJoint, Measure.pi_pi]
  simp only [branchJoint_height_support hτ₀ hτ₁, Finset.prod_const_one]

end
end Funk
