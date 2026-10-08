import Funk.BasisDensityTransport

/-! Scaling the frozen Funk integral and cancelling the exact probability
normalization. The lower-bound theorem explicitly retains its mass input. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

theorem basisMap_smul_one {n : ℕ} (τ : ℝ) :
    (basisMap (τ • (1 : Matrix (Fin n) (Fin n) ℝ)) : Space n → Space n) =
      fun X => τ • X := by
  ext X i
  simp [basisMap]

theorem funkVolume_scale {n : ℕ} {K : Set (Space n)} (hK : MeasurableSet K)
    {τ : ℝ} (hτ : 0 < τ) :
    funkVolume K τ = ENNReal.ofReal (τ ^ n) *
      ∫⁻ X in K, volume (coordinatePolar (translate K (τ • X))) := by
  have hd : (τ • (1 : Matrix (Fin n) (Fin n) ℝ)).det = τ ^ n := by simp
  have h := lintegral_basisMap_image (by rw [hd]; exact pow_ne_zero _ hτ.ne') hK
    (fun x => volume (coordinatePolar (translate K x)))
  rw [basisMap_smul_one, hd, abs_of_pos (pow_pos hτ _),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
  exact h

theorem funk_normalization_cancel (n : ℕ) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) * basisVolumeFactor n τ =
      ENNReal.ofReal (τ ^ n) := by
  have ha : 0 < 4 * Real.artanh τ := mul_pos (by norm_num) (Real.artanh_pos ⟨hτ0, hτ1⟩)
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [basisVolumeFactor, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [div_pow]
  field_simp

/-- An exact reduction to the normalized mass integral, not a proof of that input. -/
theorem funkVolume_lower_of_mass_integral {n : ℕ} {K : Set (Space n)}
    (hK : MeasurableSet K) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hmass : 1 ≤ basisVolumeFactor n τ *
      ∫⁻ X in K, volume (coordinatePolar (translate K (τ • X)))) :
    ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) ≤ funkVolume K τ := by
  rw [funkVolume_scale hK hτ0]
  have h := mul_le_mul_right hmass (ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)))
  rwa [mul_one, ← mul_assoc, funk_normalization_cancel n hτ0 hτ1] at h

end
end Funk
