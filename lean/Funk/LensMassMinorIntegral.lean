import Funk.LensPowerMinorSum
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! A genuine finite sum of minor integrals on the actual lens energy sublevel.
All restricted-measure measurability hypotheses are proved here. This is not
an angular change-of-variables formula or the final probability upper bound. -/

open Set Matrix Complex MeasureTheory
open scoped BigOperators ENNReal

namespace Funk
noncomputable section

theorem lensPowerRowFactor_continuousOn {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ) (j : Fin m) :
    ContinuousOn (fun z => lensPowerRowFactor τ rows k z j) (lensComplexDomain τ rows) := by
  have hg : ContinuousOn (fun z => tiltedLensInverse τ (lensComplexRow (rows j) z))
      (lensComplexDomain τ rows) := (tiltedLensInverse_analyticOnNhd hτ0 hτ1).continuousOn.comp
    (lensComplexRow (rows j)).continuous.continuousOn (fun _ hz => hz j)
  have hd : ContinuousOn (fun z => deriv (tiltedLensInverse τ) (lensComplexRow (rows j) z))
      (lensComplexDomain τ rows) := (tiltedLensInverse_analyticOnNhd hτ0 hτ1).deriv.continuousOn.comp
    (lensComplexRow (rows j)).continuous.continuousOn (fun _ hz => hz j)
  exact (continuousOn_const.mul (hg.pow (k-1))).mul hd

theorem lensPowerWeight_continuousOn {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ) (j : Fin m) :
    ContinuousOn (fun z => lensPowerWeight τ rows k z j) (lensComplexDomain τ rows) :=
  Complex.continuous_normSq.comp_continuousOn
    (lensPowerRowFactor_continuousOn hτ0 hτ1 rows k j)

theorem lensPower_minorDensity_continuousOn {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ) (s : Fin n → Fin m) :
    ContinuousOn (fun z => (n.factorial : ℝ) *
      (∏ i, lensPowerWeight τ rows k z (s i)) * (Matrix.of fun i => rows (s i)).det ^ 2)
      (lensComplexDomain τ rows) := by
  exact (continuousOn_const.mul (continuousOn_finsetProd _
    (fun i _ => lensPowerWeight_continuousOn hτ0 hτ1 rows k (s i)))).mul continuousOn_const

theorem lensPower_massSublevel_measurableSet {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ) :
    MeasurableSet (lensComplexDomain τ rows ∩ {z | lensPowerEnergy τ rows k z < 1}) :=
  ((lensPowerEnergy_continuousOn hτ0 hτ1 rows k).isOpen_inter_preimage
    (isOpen_lensComplexDomain τ rows) isOpen_Iio).measurableSet

/-- Restriction to the actual sublevel supplies measurability for every summand. -/
theorem lensPower_minorDensity_aemeasurable {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ) (s : Fin n → Fin m) :
    AEMeasurable (fun z => ENNReal.ofReal ((n.factorial : ℝ) *
      (∏ i, lensPowerWeight τ rows k z (s i)) * (Matrix.of fun i => rows (s i)).det ^ 2))
      (volume.restrict (lensComplexDomain τ rows ∩ {z | lensPowerEnergy τ rows k z < 1})) :=
  (ENNReal.continuous_ofReal.comp_continuousOn
    (lensPower_minorDensity_continuousOn hτ0 hτ1 rows k s)).mono
      (fun _ hz => hz.1) |>.aemeasurable (lensPower_massSublevel_measurableSet hτ0 hτ1 rows k)

/-- Exact finite sum for the actual mass, using the existing unsigned basis indices. -/
theorem lensPower_massIntegral_eq_unsigned_minor_integrals {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ) :
    OAI.Mahler.massIntegral (lensComplexDomain τ rows)
      (fun j => lensPowerComponent τ rows k j) =
      ∑ s ∈ unsignedBasisIndices rows,
        ∫⁻ z in lensComplexDomain τ rows ∩ {z | lensPowerEnergy τ rows k z < 1},
          ENNReal.ofReal ((n.factorial : ℝ) * (∏ i, lensPowerWeight τ rows k z (s i)) *
            (Matrix.of fun i => rows (s i)).det ^ 2) := by
  classical
  unfold OAI.Mahler.massIntegral
  simp only [lensPower_upstream_tau_eq]
  calc
    _ = ∫⁻ z in lensComplexDomain τ rows ∩ {z | lensPowerEnergy τ rows k z < 1},
        ∑ s ∈ unsignedBasisIndices rows, ENNReal.ofReal ((n.factorial : ℝ) *
          (∏ i, lensPowerWeight τ rows k z (s i)) *
            (Matrix.of fun i => rows (s i)).det ^ 2) := by
      apply setLIntegral_congr_fun (lensPower_massSublevel_measurableSet hτ0 hτ1 rows k)
      intro z hz
      exact lensPower_massDensity_ofReal_eq_unsigned_sum hτ0 hτ1 rows k hz.1
    _ = _ := lintegral_finsetSum' _ (fun s _ =>
      lensPower_minorDensity_aemeasurable hτ0 hτ1 rows k s)

/-- The already proved mass lower bound now holds for the exact finite minor integral sum. -/
theorem lensPower_unsigned_minor_integrals_lower {n m : ℕ} (hn : 1 ≤ n) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n)
    (hK : IsCompact (stripBody rows)) {k : ℕ} (hk : 1 ≤ k) :
    ENNReal.ofReal ((Real.pi * (k : ℝ))^n) ≤
      ∑ s ∈ unsignedBasisIndices rows,
        ∫⁻ z in lensComplexDomain τ rows ∩ {z | lensPowerEnergy τ rows k z < 1},
          ENNReal.ofReal ((n.factorial : ℝ) * (∏ i, lensPowerWeight τ rows k z (s i)) *
            (Matrix.of fun i => rows (s i)).det ^ 2) := by
  rw [← lensPower_massIntegral_eq_unsigned_minor_integrals hτ0 hτ1 rows k]
  exact lensPower_massIntegral_lower hn hτ0 hτ1 rows hK hk

end
end Funk
