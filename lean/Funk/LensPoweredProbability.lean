import Funk.LensPoweredAngularIntegral

/-! A genuine fixed probability space for the limiting argument: the positive
simplex has density n!, independently of the existing lensAngularRows law.
The actual mass lower bound is reduced to an unscaled indicator probability
sum. This does not yet prove the boundary-event limsup or reverse-Fatou cover. -/

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Funk
noncomputable section

/-- Uniform probability law on the actual powered-radius simplex. -/
def lensPoweredSimplexProbability (n : ℕ) : Measure (Space n) :=
  ENNReal.ofReal (n.factorial : ℝ) • volume.restrict (positivePoweredSimplex n)

theorem lensPoweredSimplexProbability_univ (n : ℕ) :
    lensPoweredSimplexProbability n univ = 1 := by
  rw [lensPoweredSimplexProbability, Measure.smul_apply, Measure.restrict_apply_univ,
    volume_positivePoweredSimplex, smul_eq_mul, ← ENNReal.ofReal_mul (by positivity)]
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  simp [hf]

instance lensPoweredSimplexProbability_isProbability (n : ℕ) :
    IsProbabilityMeasure (lensPoweredSimplexProbability n) :=
  ⟨lensPoweredSimplexProbability_univ n⟩

/-- Fixed joint probability law; the literal old angular law is retained. -/
def lensPoweredProbability (n : ℕ) : Measure (Space n × Space n) :=
  (lensPoweredSimplexProbability n).prod (lensAngularRows n)

instance lensPoweredProbability_isProbability (n : ℕ) :
    IsProbabilityMeasure (lensPoweredProbability n) := by
  let := lensAngularRows_isProbability n
  unfold lensPoweredProbability
  infer_instance

theorem lensPoweredProbability_univ (n : ℕ) : lensPoweredProbability n univ = 1 :=
  measure_univ

/-- No finite-measure premise is supplied; the actual joint law is a probability measure. -/
theorem lensPoweredProbability_univ_ne_top (n : ℕ) :
    lensPoweredProbability n univ ≠ ∞ := by
  rw [lensPoweredProbability_univ]
  exact ENNReal.one_ne_top

/-- Exact Tonelli and n! normalization for every measurable joint observable. -/
theorem lintegral_lensPoweredProbability {n : ℕ} {g : Space n × Space n → ℝ≥0∞}
    (hg : Measurable g) :
    (∫⁻ p, g p ∂lensPoweredProbability n) = ENNReal.ofReal (n.factorial : ℝ) *
      ∫⁻ t in positivePoweredSimplex n, ∫⁻ θ, g (t,θ) ∂lensAngularRows n := by
  let := lensAngularRows_isProbability n
  rw [lensPoweredProbability, lintegral_prod _ hg.aemeasurable,
    lensPoweredSimplexProbability, lintegral_smul_measure, smul_eq_mul]

/-- Actual mass factorization over the fixed simplex/angular probability space. -/
theorem lensPower_massIntegral_eq_powered_probability {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) {k : ℕ} (hk : 1 ≤ k) :
    OAI.Mahler.massIntegral (lensComplexDomain τ rows) (fun j => lensPowerComponent τ rows k j) =
      ENNReal.ofReal ((Real.pi*(k : ℝ))^n) *
        ∑ s ∈ unsignedBasisIndices rows,
          ∫⁻ p, lensPoweredProductIndicator τ rows k s p ∂lensPoweredProbability n := by
  classical
  rw [lensPower_massIntegral_eq_existing_angular_integrals hτ0 hτ1 rows hk, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [lintegral_lensPoweredProbability (measurable_lensPoweredProductIndicator hτ0 hτ1 rows k s),
    mul_assoc]

/-- The known (πk)^n answer is cancelled only after deriving the actual probability factorization. -/
theorem lensPower_powered_probability_lower {n m : ℕ} (hn : 1 ≤ n) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n)
    (hK : IsCompact (stripBody rows)) {k : ℕ} (hk : 1 ≤ k) :
    1 ≤ ∑ s ∈ unsignedBasisIndices rows,
      ∫⁻ p, lensPoweredProductIndicator τ rows k s p ∂lensPoweredProbability n := by
  have hc : ENNReal.ofReal ((Real.pi*(k : ℝ))^n) ≠ 0 := by
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    exact pow_pos (mul_pos Real.pi_pos (Nat.cast_pos.mpr (by omega : 0 < k))) _
  have h := lensPower_massIntegral_lower hn hτ0 hτ1 rows hK hk
  rw [lensPower_massIntegral_eq_powered_probability hτ0 hτ1 rows hk] at h
  exact (ENNReal.mul_le_mul_iff_right hc ENNReal.ofReal_ne_top).mp (by simpa only [mul_one] using h)

theorem lensPoweredProductIndicator_le_one {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n)
    (k : ℕ) (s : Fin n → Fin m) (p : Space n × Space n) :
    lensPoweredProductIndicator τ rows k s p ≤ 1 :=
  lensPoweredBasisIndicator_le_one τ rows k s _

/-- Common integral bound 1 for every k and actual unsigned-basis indicator. -/
theorem lensPoweredProductIndicator_probability_integral_le_one {n m : ℕ}
    (τ : ℝ) (rows : Fin m → Space n) (k : ℕ) (s : Fin n → Fin m) :
    (∫⁻ p, lensPoweredProductIndicator τ rows k s p ∂lensPoweredProbability n) ≤ 1 := by
  calc
    _ ≤ ∫⁻ _p, (1 : ℝ≥0∞) ∂lensPoweredProbability n :=
      lintegral_mono (lensPoweredProductIndicator_le_one τ rows k s)
    _ = 1 := by simp

theorem lensPoweredProductIndicator_probability_integral_ne_top {n m : ℕ}
    (τ : ℝ) (rows : Fin m → Space n) (k : ℕ) (s : Fin n → Fin m) :
    (∫⁻ p, lensPoweredProductIndicator τ rows k s p ∂lensPoweredProbability n) ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    (lensPoweredProductIndicator_probability_integral_le_one τ rows k s)

end
end Funk
