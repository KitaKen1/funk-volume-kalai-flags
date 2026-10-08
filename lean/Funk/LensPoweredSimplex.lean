import Funk.LensMassPoweredIntegral
import Funk.PoweredSimplexVolume

/-! Genuine simplex support for the actual powered-radius mass indicator.
Selected row energy is bounded by the full energy, so the transformed domain
has sum t_i < 1. No simplex or boundary-cover premise is supplied. -/

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Funk
noncomputable section

/-- Positive powered radii in the actual simplex, with the standard polar angles. -/
def lensPoweredPolarSimplex (n : ℕ) : Set (Fin n → ℝ × ℝ) :=
  lensPolarChart n ∩ {q | ∑ i, (q i).1 < 1}

theorem measurableSet_lensPoweredPolarSimplex (n : ℕ) :
    MeasurableSet (lensPoweredPolarSimplex n) :=
  (measurableSet_lensPolarChart n).inter (isOpen_lt (by fun_prop) continuous_const).measurableSet

theorem lensBasisPowerDomain_selected_energy_le {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ)
    {s : Fin n → Fin m} (hs : s ∈ unsignedBasisIndices rows)
    {u : LensComplexSpace n} (hu : u ∈ lensOpenPolydisk n) :
    (∑ i, ‖u i ^ k‖^2) ≤
      lensPowerEnergy τ rows k (lensBasisParametrization τ (Matrix.of fun i => rows (s i)) u) := by
  classical
  have hB : (Matrix.of fun i => rows (s i)).det ≠ 0 := ((mem_unsignedBasisIndices rows s).mp hs).2
  unfold lensPowerEnergy
  apply Finset.sum_le_sum_of_injOn s ((mem_unsignedBasisIndices rows s).mp hs).1.injective.injOn
  · intro i _
    exact Finset.mem_univ _
  · intro i _
    have hr := lensBasisParametrization_selected_row hB τ u i
    change lensComplexRow (rows (s i))
      (lensBasisParametrization τ (Matrix.of fun i => rows (s i)) u) = tiltedLens τ (u i) at hr
    rw [lensPowerComponent, hr, tiltedLensInverse_left hτ0 hτ1 (hu i)]
  · intro j _ _
    exact sq_nonneg _

theorem lensPolarRoot_selected_power_energy {n : ℕ} {k : ℕ} (hk : 1 ≤ k)
    {q : Fin n → ℝ × ℝ} (hq : q ∈ lensPolarChart n) (i : Fin n) :
    ‖lensPolarVector (lensPolarRoot k q) i ^ k‖^2 = (q i).1 := by
  rw [norm_pow, ← pow_mul, mul_comm k 2]
  change ‖Complex.polarCoord.symm (lensPolarRoot k q i)‖^(2*k) = _
  rw [Complex.norm_polarCoord_symm, abs_of_pos ((lensPolarRoot_mapsTo k hq) i (mem_univ i)).1]
  exact Real.rpow_inv_natCast_pow (hq i (mem_univ i)).1.le (by omega : 2*k ≠ 0)

theorem lensPoweredBasisIndicator_support {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) {k : ℕ} (hk : 1 ≤ k)
    {s : Fin n → Fin m} (hs : s ∈ unsignedBasisIndices rows)
    {q : Fin n → ℝ × ℝ} (hq : q ∈ lensPolarChart n)
    (hf : lensPoweredBasisIndicator τ rows k s q ≠ 0) : q ∈ lensPoweredPolarSimplex n := by
  classical
  have hu : lensPolarVector (lensPolarRoot k q) ∈ lensBasisPowerDomain τ rows k s := by
    by_contra h
    exact hf (by simp [lensPoweredBasisIndicator, indicator_of_notMem h])
  refine ⟨hq, ?_⟩
  have he := lensBasisPowerDomain_selected_energy_le hτ0 hτ1 rows k hs hu.1
  simp_rw [lensPolarRoot_selected_power_energy hk hq] at he
  exact he.trans_lt hu.2.2

theorem lensPoweredBasisIndicator_le_one {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n)
    (k : ℕ) (s : Fin n → Fin m) (q : Fin n → ℝ × ℝ) :
    lensPoweredBasisIndicator τ rows k s q ≤ 1 := by
  classical
  by_cases hu : lensPolarVector (lensPolarRoot k q) ∈ lensBasisPowerDomain τ rows k s
  · simp only [lensPoweredBasisIndicator, indicator_of_mem hu, le_refl]
  · simp only [lensPoweredBasisIndicator, indicator_of_notMem hu, zero_le]

/-- The exact integral can be restricted to the genuine powered-radius simplex. -/
theorem lensPoweredBasisIndicator_integral_eq_simplex {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) {k : ℕ} (hk : 1 ≤ k)
    {s : Fin n → Fin m} (hs : s ∈ unsignedBasisIndices rows) :
    (∫⁻ q in lensPolarChart n, lensPoweredBasisIndicator τ rows k s q) =
      ∫⁻ q in lensPoweredPolarSimplex n, lensPoweredBasisIndicator τ rows k s q := by
  classical
  rw [← lintegral_indicator (measurableSet_lensPolarChart n),
    ← lintegral_indicator (measurableSet_lensPoweredPolarSimplex n)]
  apply lintegral_congr
  intro q
  by_cases hq : q ∈ lensPolarChart n
  · by_cases hf : lensPoweredBasisIndicator τ rows k s q = 0
    · simp [Set.indicator, hq, hf]
    · simp only [indicator_of_mem hq, indicator_of_mem
        (lensPoweredBasisIndicator_support hτ0 hτ1 rows hk hs hq hf)]
  · have hs' : q ∉ lensPoweredPolarSimplex n := fun h => hq h.1
    simp only [indicator_of_notMem hq, indicator_of_notMem hs']

/-- Actual mass with the exact n! (k/2)^n coefficient and actual simplex domain. -/
theorem lensPower_massIntegral_eq_powered_simplex_integrals {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) {k : ℕ} (hk : 1 ≤ k) :
    OAI.Mahler.massIntegral (lensComplexDomain τ rows) (fun j => lensPowerComponent τ rows k j) =
      ∑ s ∈ unsignedBasisIndices rows,
        ENNReal.ofReal ((n.factorial : ℝ) * ((k : ℝ)/2)^n) *
          ∫⁻ q in lensPoweredPolarSimplex n, lensPoweredBasisIndicator τ rows k s q := by
  classical
  rw [lensPower_massIntegral_eq_powered_integrals hτ0 hτ1 rows hk]
  apply Finset.sum_congr rfl
  intro s hs
  rw [lensPoweredBasisIndicator_integral_eq_simplex hτ0 hτ1 rows hk hs]

theorem lensPower_powered_simplex_integrals_lower {n m : ℕ} (hn : 1 ≤ n) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n)
    (hK : IsCompact (stripBody rows)) {k : ℕ} (hk : 1 ≤ k) :
    ENNReal.ofReal ((Real.pi * (k : ℝ))^n) ≤
      ∑ s ∈ unsignedBasisIndices rows,
        ENNReal.ofReal ((n.factorial : ℝ) * ((k : ℝ)/2)^n) *
          ∫⁻ q in lensPoweredPolarSimplex n, lensPoweredBasisIndicator τ rows k s q := by
  rw [← lensPower_massIntegral_eq_powered_simplex_integrals hτ0 hτ1 rows hk]
  exact lensPower_massIntegral_lower hn hτ0 hτ1 rows hK hk

end
end Funk
