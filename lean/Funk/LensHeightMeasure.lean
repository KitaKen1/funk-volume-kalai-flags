import Funk.DensityTransport
import Funk.BranchProbability
import Funk.LensHeightInverse

/-! Exact pushforward measures for both signed height branches, including
the angular normalization and the existing branchDensity. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

def lensHalfAngular : Measure ℝ :=
  ENNReal.ofReal (1 / (2 * Real.pi)) • volume.restrict (Icc (-Real.pi / 2) (Real.pi / 2))

def lensBranchHeight (τ : ℝ) (b : Bool) (θ : ℝ) : ℝ :=
  if b then tiltedHeight τ θ else -tiltedHeight τ θ

theorem measurable_lensBranchHeight (τ : ℝ) (b : Bool) :
    Measurable (lensBranchHeight τ b) := by
  cases b <;> unfold lensBranchHeight tiltedHeight lensHeight <;> dsimp <;> fun_prop

theorem tiltedHeight_image_Icc {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    tiltedHeight τ '' Icc (-Real.pi / 2) (Real.pi / 2) = Icc (-1) 1 := by
  apply Subset.antisymm
  · rintro y ⟨θ, hθ, rfl⟩
    exact tiltedHeight_mem_Icc hτ0 hτ1 hθ
  · intro y hy
    exact ⟨lensHeightAngle τ y, lensHeightAngle_mem_Icc hτ0 hτ1 hy,
      tiltedHeight_lensHeightAngle hτ0 hτ1 (lensHeight_margin_pos_of_le_one hτ0 hτ1 hy.2)⟩

theorem lensBranchHeight_image_Icc {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (b : Bool) :
    lensBranchHeight τ b '' Icc (-Real.pi / 2) (Real.pi / 2) = Icc (-1) 1 := by
  cases b
  · change (fun θ => -tiltedHeight τ θ) '' _ = _
    rw [← image_image (f := tiltedHeight τ) (g := fun y : ℝ => -y), tiltedHeight_image_Icc hτ0 hτ1]
    ext y
    simp
  · exact tiltedHeight_image_Icc hτ0 hτ1

theorem lensBranchHeight_injective {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (b : Bool) :
    Function.Injective (lensBranchHeight τ b) := by
  cases b
  · exact neg_injective.comp (tiltedHeight_strictMono hτ0 hτ1).injective
  · exact (tiltedHeight_strictMono hτ0 hτ1).injective

theorem hasDerivAt_lensBranchHeight (τ : ℝ) (b : Bool) (θ : ℝ) :
    HasDerivAt (lensBranchHeight τ b)
      (if b then deriv (tiltedHeight τ) θ else -deriv (tiltedHeight τ) θ) θ := by
  have hd := (hasDerivAt_tiltedHeight τ θ).differentiableAt.hasDerivAt
  cases b
  · exact hd.neg
  · exact hd

theorem lensBranchHeight_density_jacobian {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (b : Bool) (θ : ℝ) :
    ENNReal.ofReal |if b then deriv (tiltedHeight τ) θ else -deriv (tiltedHeight τ) θ| *
      ENNReal.ofReal (branchDensity τ (branchSign b) (lensBranchHeight τ b θ)) =
        ENNReal.ofReal (1 / (2 * Real.pi)) := by
  have hd : 0 < deriv (tiltedHeight τ) θ :=
    lensHeight_deriv_pos hτ0 (lensRate_pos hτ0 hτ1) (lensScale_pos hτ0 hτ1) θ
  have hj := tiltedHeight_density_jacobian hτ0 hτ1 θ
  cases b <;> simp only [lensBranchHeight, branchSign, Bool.false_eq_true, ite_false, ite_true]
  · rw [abs_neg, abs_of_pos hd, branchDensity_reflect, neg_neg,
      ← ENNReal.ofReal_mul hd.le, mul_comm, hj]
  · rw [abs_of_pos hd, ← ENNReal.ofReal_mul hd.le, mul_comm, hj]

theorem lensBranchHeight_map {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (b : Bool) :
    lensHalfAngular.map (lensBranchHeight τ b) = branchMeasure τ (branchSign b) := by
  apply map_scaled_restrict_eq_withDensity measurableSet_Icc (measurable_lensBranchHeight τ b)
    (fun θ _ => (hasDerivAt_lensBranchHeight τ b θ).hasDerivWithinAt)
    (lensBranchHeight_injective hτ0 hτ1 b).injOn (lensBranchHeight_image_Icc hτ0 hτ1 b)
  intro θ _
  exact lensBranchHeight_density_jacobian hτ0 hτ1 b θ

theorem lensHalfAngular_univ : lensHalfAngular univ = 1 / 2 := by
  rw [lensHalfAngular, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
    Real.volume_Icc]
  rw [← ENNReal.ofReal_mul (by positivity)]
  have he : 1 / (2 * Real.pi) * (Real.pi / 2 - -Real.pi / 2) = (1 : ℝ) / 2 := by
    field_simp
    ring
  rw [he, ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

instance lensHalfAngular_isFiniteMeasure : IsFiniteMeasure lensHalfAngular :=
  ⟨by rw [lensHalfAngular_univ]; norm_num⟩

theorem lensHalfAngular_ae_mem_Ioo :
    ∀ᵐ θ ∂lensHalfAngular, θ ∈ Ioo (-Real.pi / 2) (Real.pi / 2) := by
  unfold lensHalfAngular
  rw [← restrict_Ioo_eq_restrict_Icc]
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ioo) _

end
end Funk
