import Funk.CubePolar
import Funk.IntervalNormalization
import Mathlib.MeasureTheory.Integral.Pi

/-! The actual Funk integral for coordinate cubes in every finite dimension.
The lower bound uses the certified signed-axis simplices and product integration.
This module makes no assertion about arbitrary symmetric convex bodies. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk

noncomputable section

def coordinateBox (n : ℕ) (a b : ℝ) : Set (Space n) :=
  Set.pi Set.univ (fun _ => Icc a b)

theorem mem_coordinateBox {n : ℕ} {a b : ℝ} {x : Space n} :
    x ∈ coordinateBox n a b ↔ ∀ i, a ≤ x i ∧ x i ≤ b := by
  simp only [coordinateBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]

theorem measurableSet_coordinateBox (n : ℕ) (a b : ℝ) :
    MeasurableSet (coordinateBox n a b) := by
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

theorem volume_coordinateBox (n : ℕ) (a b : ℝ) :
    volume (coordinateBox n a b) = ENNReal.ofReal (b - a) ^ n := by
  rw [coordinateBox, volume_pi_pi]
  simp [Real.volume_Icc]

theorem coordinateCube_eq_box (n : ℕ) :
    coordinateCube n = coordinateBox n (-1) 1 := by
  ext x
  simp [mem_coordinateCube, mem_coordinateBox, abs_le]

theorem scaled_coordinateCube {n : ℕ} {τ : ℝ} (hτ : 0 < τ) :
    (fun y : Space n => τ • y) '' coordinateCube n = coordinateBox n (-τ) τ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_coordinateBox]
    intro i
    have hi := abs_le.mp ((mem_coordinateCube y).mp hy i)
    change -τ ≤ τ * y i ∧ τ * y i ≤ τ
    constructor <;> nlinarith [hi.1, hi.2]
  · intro hx
    have hx := mem_coordinateBox.mp hx
    refine ⟨fun i => x i / τ, ?_, ?_⟩
    · rw [mem_coordinateCube]
      intro i
      rw [abs_le]
      constructor
      · exact (le_div_iff₀ hτ).mpr (by simpa using (hx i).1)
      · exact (div_le_iff₀ hτ).mpr (by simpa using (hx i).2)
    · ext i
      change τ * (x i / τ) = x i
      field_simp

def cubeKernel (x : ℝ) : ℝ := 1 / (1 - x) + 1 / (1 + x)

theorem cubeKernel_nonneg {τ x : ℝ} (hτ : τ < 1) (hx : x ∈ Icc (-τ) τ) :
    0 ≤ cubeKernel x := by
  have hm : 0 < 1 - x := by linarith [hx.2]
  have hp : 0 < 1 + x := by linarith [hx.1]
  exact add_nonneg (one_div_pos.mpr hm).le (one_div_pos.mpr hp).le

theorem cube_kernel_integrable {n : ℕ} {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    IntegrableOn (fun x : Space n => (∏ i, cubeKernel (x i)) / (n.factorial : ℝ))
      (coordinateBox n (-τ) τ) := by
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -τ ≤ τ)).mp
    (interval_kernel_integrable hτ₀ hτ₁)
  have hp := Integrable.fintype_prod (ι := Fin n) (fun _ => hi)
  change Integrable _ (volume.restrict (Set.pi Set.univ (fun _ : Fin n => Icc (-τ) τ)))
  rw [show (volume : Measure (Space n)) = Measure.pi (fun _ => volume) from rfl,
    Measure.restrict_pi_pi]
  exact hp.div_const _

theorem cube_kernel_integral {n : ℕ} {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    (∫ x in coordinateBox n (-τ) τ,
      (∏ i, cubeKernel (x i)) / (n.factorial : ℝ)) =
      (4 * Real.artanh τ) ^ n / (n.factorial : ℝ) := by
  unfold coordinateBox
  rw [show (volume : Measure (Space n)) = Measure.pi (fun _ => volume) from rfl,
    Measure.restrict_pi_pi, integral_div, integral_fintype_prod_eq_pow]
  simp only [Fintype.card_fin]
  congr 2
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -τ ≤ τ)]
  exact interval_kernel_integral hτ₀ hτ₁

theorem lintegral_cube_kernel {n : ℕ} {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    (∫⁻ x in coordinateBox n (-τ) τ,
      ENNReal.ofReal ((∏ i, cubeKernel (x i)) / (n.factorial : ℝ))) =
      ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) := by
  have hn : 0 ≤ᵐ[volume.restrict (coordinateBox n (-τ) τ)]
      (fun x => (∏ i, cubeKernel (x i)) / (n.factorial : ℝ)) := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_coordinateBox n (-τ) τ)]
      with x hx
    exact div_nonneg (Finset.prod_nonneg (fun i _ =>
      cubeKernel_nonneg hτ₁ (mem_coordinateBox.mp hx i))) (by positivity)
  rw [← ofReal_integral_eq_lintegral_ofReal (cube_kernel_integrable hτ₀ hτ₁) hn,
    cube_kernel_integral hτ₀ hτ₁]

/-- A lower bound for the frozen, geometric Funk-volume definition, for all cubes. -/
theorem funkVolume_coordinateCube_lower {n : ℕ} {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) ≤
      funkVolume (coordinateCube n) τ := by
  rw [funkVolume, scaled_coordinateCube hτ₀, ← lintegral_cube_kernel hτ₀ hτ₁]
  apply setLIntegral_mono' (measurableSet_coordinateBox n (-τ) τ)
  intro x hx
  obtain ⟨X, hX, rfl⟩ := (scaled_coordinateCube hτ₀).symm ▸ hx
  simpa [cubeKernel, Pi.smul_apply, smul_eq_mul] using
    cube_polar_volume_lower hτ₀.le hτ₁ hX


/-- Testing the coordinate directions bounds the whole translated polar. -/
theorem cube_polar_subset_box {n : ℕ} {τ : ℝ} {x : Space n}
    (hτ₁ : τ < 1) (hx : x ∈ coordinateBox n (-τ) τ) :
    coordinatePolar (translate (coordinateCube n) x) ⊆
      coordinateBox n (-(1 / (1 - τ))) (1 / (1 - τ)) := by
  intro y hy
  rw [mem_coordinateBox]
  intro i
  have hgap : 0 < 1 - τ := by linarith
  have htest (a : ℝ) (ha : |a| ≤ 1 - τ) :
      Pi.single i a ∈ translate (coordinateCube n) x := by
    refine ⟨x + Pi.single i a, ?_, by simp⟩
    rw [mem_coordinateCube]
    intro j
    by_cases hji : j = i
    · subst j
      simp only [Pi.add_apply, Pi.single_eq_same]
      calc
        |x i + a| ≤ |x i| + |a| := abs_add_le _ _
        _ ≤ τ + (1 - τ) := add_le_add (abs_le.mpr (mem_coordinateBox.mp hx i)) ha
        _ = 1 := by ring
    · simpa [Pi.single_eq_of_ne hji] using
        (abs_le.mpr (mem_coordinateBox.mp hx j)).trans hτ₁.le
  have hp := hy _ (htest (1 - τ) (by rw [abs_of_pos hgap]))
  have hm := hy _ (htest (-(1 - τ)) (by rw [abs_neg, abs_of_pos hgap]))
  rw [dotProduct_single] at hp hm
  constructor
  · have hneg : -y i ≤ 1 / (1 - τ) := (le_div_iff₀ hgap).mpr (by nlinarith)
    linarith
  · exact (le_div_iff₀ hgap).mpr hp

theorem cube_polar_volume_upper {n : ℕ} {τ : ℝ} {x : Space n}
    (hτ₁ : τ < 1) (hx : x ∈ coordinateBox n (-τ) τ) :
    volume (coordinatePolar (translate (coordinateCube n) x)) ≤
      ENNReal.ofReal (2 / (1 - τ)) ^ n := by
  calc
    _ ≤ volume (coordinateBox n (-(1 / (1 - τ))) (1 / (1 - τ))) :=
      measure_mono (cube_polar_subset_box hτ₁ hx)
    _ = _ := by rw [volume_coordinateBox]; congr 2; ring

/-- A coarse explicit finite majorant; sharpness is not needed for finiteness. -/
theorem funkVolume_coordinateCube_upper {n : ℕ} {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    funkVolume (coordinateCube n) τ ≤
      ENNReal.ofReal (2 / (1 - τ)) ^ n * ENNReal.ofReal (2 * τ) ^ n := by
  rw [funkVolume, scaled_coordinateCube hτ₀]
  calc
    _ ≤ ∫⁻ _x in coordinateBox n (-τ) τ, ENNReal.ofReal (2 / (1 - τ)) ^ n :=
      setLIntegral_mono' (measurableSet_coordinateBox n (-τ) τ)
        (fun _ hx => cube_polar_volume_upper hτ₁ hx)
    _ = _ := by
      rw [lintegral_const, Measure.restrict_apply_univ, volume_coordinateBox]
      congr 3
      ring

theorem funkVolume_coordinateCube_finite {n : ℕ} {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    funkVolume (coordinateCube n) τ < ⊤ := by
  apply lt_of_le_of_lt (funkVolume_coordinateCube_upper hτ₀ hτ₁)
  finiteness

theorem coordinateCube_isSymmetricConvexBody (n : ℕ) :
    IsSymmetricConvexBody (coordinateCube n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [coordinateCube_eq_box, coordinateBox, Set.pi_univ_Icc]
    exact isCompact_Icc
  · rw [coordinateCube_eq_box, coordinateBox, Set.pi_univ_Icc]
    exact convex_Icc _ _
  · intro x hx
    simpa [mem_coordinateCube] using hx
  · rw [coordinateCube_eq_box, coordinateBox, Set.pi_univ_Icc,
      mem_interior_iff_mem_nhds]
    exact pi_Icc_mem_nhds (by intro i; norm_num) (by intro i; norm_num)

/-- Both requirements of the Funk target for a genuine convex body, in all dimensions. -/
theorem coordinateCube_funk_target (n : ℕ) {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    IsSymmetricConvexBody (coordinateCube n) ∧
      funkVolume (coordinateCube n) τ < ⊤ ∧
      ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) ≤
        funkVolume (coordinateCube n) τ :=
  ⟨coordinateCube_isSymmetricConvexBody n,
    funkVolume_coordinateCube_finite hτ₀ hτ₁, funkVolume_coordinateCube_lower hτ₀ hτ₁⟩

end
end Funk
