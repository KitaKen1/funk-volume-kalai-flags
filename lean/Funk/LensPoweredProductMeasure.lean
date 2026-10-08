import Funk.LensPoweredSimplex

/-! The exact common powered-radius/angle domain is a product after a
volume-preserving coordinate regrouping. Its finite volume and mass coefficient
normalization are proved; identification with the existing lensAngular boundary
probability and reverse Fatou remain separate obligations. -/

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Funk
noncomputable section

def lensStandardAngleCube (n : ℕ) : Set (Space n) :=
  Set.univ.pi (fun _ => Ioo (-Real.pi) Real.pi)

theorem measurableSet_lensStandardAngleCube (n : ℕ) :
    MeasurableSet (lensStandardAngleCube n) := MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)

theorem lensPoweredPolarSimplex_eq_product_preimage (n : ℕ) :
    lensPoweredPolarSimplex n =
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)) ⁻¹'
        (positivePoweredSimplex n ×ˢ lensStandardAngleCube n) := by
  ext q
  simp [lensPoweredPolarSimplex, lensPolarChart, Complex.polarCoord_target,
    positivePoweredSimplex, lensStandardAngleCube, MeasurableEquiv.arrowProdEquivProdArrow,
    Equiv.arrowProdEquivProdArrow, forall_and, and_assoc, and_comm]

theorem volume_lensStandardAngleCube (n : ℕ) :
    volume (lensStandardAngleCube n) = ENNReal.ofReal ((2*Real.pi)^n) := by
  rw [lensStandardAngleCube, volume_pi_pi]
  simp only [Real.volume_Ioo, sub_neg_eq_add, ← two_mul, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow (by positivity : 0 ≤ 2*Real.pi)]

theorem volume_lensPoweredPolarSimplex (n : ℕ) :
    volume (lensPoweredPolarSimplex n) = ENNReal.ofReal ((2*Real.pi)^n / (n.factorial : ℝ)) := by
  rw [lensPoweredPolarSimplex_eq_product_preimage,
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)).measure_preimage
      (((isOpen_positivePoweredSimplex n).measurableSet.prod
        (measurableSet_lensStandardAngleCube n)).nullMeasurableSet)]
  change (volume.prod volume) (positivePoweredSimplex n ×ˢ lensStandardAngleCube n) = _
  rw [Measure.prod_prod, volume_positivePoweredSimplex, volume_lensStandardAngleCube,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem volume_lensPoweredPolarSimplex_ne_top (n : ℕ) :
    volume (lensPoweredPolarSimplex n) ≠ ∞ := by
  rw [volume_lensPoweredPolarSimplex]
  exact ENNReal.ofReal_ne_top

/-- Exact coefficient normalization on the common finite integration domain. -/
theorem lensPoweredPolarSimplex_coefficient_volume (n k : ℕ) :
    ENNReal.ofReal ((n.factorial : ℝ) * ((k : ℝ)/2)^n) *
      volume (lensPoweredPolarSimplex n) = ENNReal.ofReal ((Real.pi * (k : ℝ))^n) := by
  rw [volume_lensPoweredPolarSimplex, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [div_eq_mul_inv]
  calc
    _ = ((k : ℝ)/2)^n * (2*Real.pi)^n := by field_simp
    _ = ((Real.pi * (k : ℝ))^n) := by rw [← mul_pow]; congr 1; ring

/-- Arbitrary integrands transport to the literal product domain, without a measurability premise. -/
theorem lintegral_lensPoweredPolarSimplex_product {n : ℕ}
    (g : (Fin n → ℝ × ℝ) → ℝ≥0∞) :
    (∫⁻ q in lensPoweredPolarSimplex n, g q) =
      ∫⁻ p in positivePoweredSimplex n ×ˢ lensStandardAngleCube n,
        g ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)).symm p) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)
  have hp := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)).symm
  rw [← lintegral_indicator (measurableSet_lensPoweredPolarSimplex n),
    ← hp.lintegral_comp_emb e.symm.measurableEmbedding,
    ← lintegral_indicator ((isOpen_positivePoweredSimplex n).measurableSet.prod
      (measurableSet_lensStandardAngleCube n))]
  apply lintegral_congr
  intro p
  change (lensPoweredPolarSimplex n).indicator g (e.symm p) =
    (positivePoweredSimplex n ×ˢ lensStandardAngleCube n).indicator (fun p => g (e.symm p)) p
  have he : e.symm p ∈ lensPoweredPolarSimplex n ↔
      p ∈ positivePoweredSimplex n ×ˢ lensStandardAngleCube n := by
    rw [lensPoweredPolarSimplex_eq_product_preimage]
    change e (e.symm p) ∈ (positivePoweredSimplex n ×ˢ lensStandardAngleCube n) ↔
      p ∈ (positivePoweredSimplex n ×ˢ lensStandardAngleCube n)
    rw [e.apply_symm_apply]
  by_cases hm : p ∈ positivePoweredSimplex n ×ˢ lensStandardAngleCube n
  · simp only [indicator_of_mem (he.mpr hm), indicator_of_mem hm]
  · simp only [indicator_of_notMem (fun h => hm (he.mp h)), indicator_of_notMem hm]

/-- Actual mass on the literal product of positive simplex and standard angles. -/
theorem lensPower_massIntegral_eq_powered_product_integrals {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) {k : ℕ} (hk : 1 ≤ k) :
    OAI.Mahler.massIntegral (lensComplexDomain τ rows) (fun j => lensPowerComponent τ rows k j) =
      ∑ s ∈ unsignedBasisIndices rows,
        ENNReal.ofReal ((n.factorial : ℝ) * ((k : ℝ)/2)^n) *
          ∫⁻ p in positivePoweredSimplex n ×ˢ lensStandardAngleCube n,
            lensPoweredBasisIndicator τ rows k s
              ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)).symm p) := by
  classical
  rw [lensPower_massIntegral_eq_powered_simplex_integrals hτ0 hτ1 rows hk]
  apply Finset.sum_congr rfl
  intro s _
  rw [lintegral_lensPoweredPolarSimplex_product]

theorem lensPower_powered_product_integrals_lower {n m : ℕ} (hn : 1 ≤ n) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n)
    (hK : IsCompact (stripBody rows)) {k : ℕ} (hk : 1 ≤ k) :
    ENNReal.ofReal ((Real.pi * (k : ℝ))^n) ≤
      ∑ s ∈ unsignedBasisIndices rows,
        ENNReal.ofReal ((n.factorial : ℝ) * ((k : ℝ)/2)^n) *
          ∫⁻ p in positivePoweredSimplex n ×ˢ lensStandardAngleCube n,
            lensPoweredBasisIndicator τ rows k s
              ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)).symm p) := by
  rw [← lensPower_massIntegral_eq_powered_product_integrals hτ0 hτ1 rows hk]
  exact lensPower_massIntegral_lower hn hτ0 hτ1 rows hK hk

/-- A genuine common finite-measure dominator for the upcoming reverse-Fatou step. -/
theorem lensPoweredBasisIndicator_integral_le_volume {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n)
    (k : ℕ) (s : Fin n → Fin m) :
    (∫⁻ q in lensPoweredPolarSimplex n, lensPoweredBasisIndicator τ rows k s q) ≤
      volume (lensPoweredPolarSimplex n) := by
  calc
    _ ≤ ∫⁻ _q in lensPoweredPolarSimplex n, (1 : ℝ≥0∞) :=
      lintegral_mono (lensPoweredBasisIndicator_le_one τ rows k s)
    _ = volume (lensPoweredPolarSimplex n) := by simp

theorem lensPoweredBasisIndicator_integral_ne_top {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n)
    (k : ℕ) (s : Fin n → Fin m) :
    (∫⁻ q in lensPoweredPolarSimplex n, lensPoweredBasisIndicator τ rows k s q) ≠ ∞ :=
  ne_top_of_le_ne_top (volume_lensPoweredPolarSimplex_ne_top n)
    (lensPoweredBasisIndicator_integral_le_volume τ rows k s)

end
end Funk
