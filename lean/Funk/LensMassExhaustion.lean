import Funk.LensPowerRegular
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! An explicit exhaustion by regular positive levels for the actual tilted lens.
Continuity from below is valid for any nonnegative density, even infinite mass. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Funk
noncomputable section

/-- Dyadic levels increasing to one. -/
def lensRegularLevel (r : ℕ) : ℝ := 1 - (1/2 : ℝ) ^ (r+1)

theorem lensRegularLevel_mem (r : ℕ) : lensRegularLevel r ∈ Ioo (0 : ℝ) 1 := by
  have hp : 0 < (1/2 : ℝ)^r := pow_pos (by norm_num) _
  have hb : (1/2 : ℝ)^r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  simp only [lensRegularLevel, mem_Ioo, pow_succ]
  constructor <;> nlinarith

theorem lensRegularLevel_strictMono : StrictMono lensRegularLevel := by
  apply strictMono_nat_of_lt_succ
  intro r
  have hp : 0 < (1/2 : ℝ) ^ (r+1) := pow_pos (by norm_num) _
  simp only [lensRegularLevel, pow_succ]
  nlinarith [pow_pos (show (0 : ℝ) < 1/2 by norm_num) r]

theorem lensRegularLevel_tendsto : Tendsto lensRegularLevel atTop (𝓝 1) := by
  have hp : Tendsto (fun r : ℕ => (1/2 : ℝ)^r) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have he : lensRegularLevel = fun r : ℕ => 1 - (1/2 : ℝ)^r * (1/2 : ℝ) := by
    funext r
    simp only [lensRegularLevel, pow_succ]
  rw [he]
  simpa only [zero_mul, sub_zero] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub (hp.mul_const (1/2 : ℝ))

theorem lensPower_regular_value_sequence {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n)
    (hK : IsCompact (stripBody rows)) {k : ℕ} (hk : 0 < k) :
    StrictMono lensRegularLevel ∧ (∀ r, lensRegularLevel r ∈ Ioo (0 : ℝ) 1) ∧
      Tendsto lensRegularLevel atTop (𝓝 1) ∧
      ∀ r z, z ∈ lensComplexDomain τ rows → lensPowerEnergy τ rows k z = lensRegularLevel r →
        Function.Surjective (fderiv ℝ (lensPowerEnergy τ rows k) z) := by
  exact ⟨lensRegularLevel_strictMono, lensRegularLevel_mem, lensRegularLevel_tendsto,
    fun r _ hz he => lensPowerEnergy_positive_regular hτ0 hτ1 rows hK hk
      (lensRegularLevel_mem r).1 hz he⟩

theorem lensPower_regular_sublevels_monotone {n m : ℕ} (τ : ℝ)
    (rows : Fin m → Space n) (k : ℕ) :
    Monotone (fun r => {z | z ∈ lensComplexDomain τ rows ∧ lensPowerEnergy τ rows k z < lensRegularLevel r}) := by
  intro a b hab z hz
  exact ⟨hz.1, hz.2.trans_le (lensRegularLevel_strictMono.monotone hab)⟩

theorem lensPower_regular_sublevels_union {n m : ℕ} (τ : ℝ)
    (rows : Fin m → Space n) (k : ℕ) :
    (⋃ r, {z | z ∈ lensComplexDomain τ rows ∧ lensPowerEnergy τ rows k z < lensRegularLevel r}) =
      {z | z ∈ lensComplexDomain τ rows ∧ lensPowerEnergy τ rows k z < 1} := by
  ext z
  simp only [mem_iUnion, mem_ofPred_eq]
  constructor
  · rintro ⟨r, hz, hr⟩
    exact ⟨hz, hr.trans (lensRegularLevel_mem r).2⟩
  · rintro ⟨hz, he⟩
    obtain ⟨r, hr⟩ := (lensRegularLevel_tendsto.eventually (Ioi_mem_nhds he)).exists
    exact ⟨r, hz, hr⟩

/-- This exhaustion identity asserts no lower bound for the density. -/
theorem lensPower_mass_exhaustion_iSup {n m : ℕ} (τ : ℝ)
    (rows : Fin m → Space n) (k : ℕ) (μ : Measure (LensComplexSpace n))
    (ρ : LensComplexSpace n → ℝ≥0∞) :
    (∫⁻ z in {z | z ∈ lensComplexDomain τ rows ∧ lensPowerEnergy τ rows k z < 1}, ρ z ∂μ) =
      ⨆ r, ∫⁻ z in {z | z ∈ lensComplexDomain τ rows ∧ lensPowerEnergy τ rows k z < lensRegularLevel r}, ρ z ∂μ := by
  rw [← lensPower_regular_sublevels_union τ rows k]
  exact setLIntegral_iUnion_of_directed ρ (lensPower_regular_sublevels_monotone τ rows k).directed_le

end
end Funk
