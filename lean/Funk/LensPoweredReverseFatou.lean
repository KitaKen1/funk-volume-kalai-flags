import Funk.LensPoweredBoundaryLimit
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! Reverse Fatou on the genuine fixed simplex/angular probability space.
The dominating constant is the finite number of actual unsigned bases. The
limiting events are the literal old boundaryInterpolationEvent. -/

open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Funk
noncomputable section

def lensPoweredBoundaryIndicator {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n)
    (s : Fin n → Fin m) (p : Space n × Space n) : ℝ≥0∞ :=
  ((lensBoundaryTraceRows n τ) ⁻¹' boundaryInterpolationEvent τ rows s).indicator (fun _ => 1) p.2

theorem measurable_lensPoweredBoundaryIndicator {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (s : Fin n → Fin m) :
    Measurable (lensPoweredBoundaryIndicator τ rows s) :=
  (measurable_const.indicator ((measurable_lensBoundaryTraceRows n τ)
    (isClosed_boundaryInterpolationEvent hτ0 hτ1 rows s).measurableSet)).comp measurable_snd

theorem lensPoweredProbability_ae_simplex (n : ℕ) :
    ∀ᵐ p ∂lensPoweredProbability n, p.1 ∈ positivePoweredSimplex n := by
  let := lensAngularRows_isProbability n
  have hr : ∀ᵐ t ∂lensPoweredSimplexProbability n, t ∈ positivePoweredSimplex n :=
    Measure.ae_smul_measure (ae_restrict_mem (isOpen_positivePoweredSimplex n).measurableSet) _
  exact (measurePreserving_fst (μ := lensPoweredSimplexProbability n)
    (ν := lensAngularRows n)).quasiMeasurePreserving.ae hr

/-- Failure of the closed limit event gives an eventual zero; success gives the bound 1. -/
theorem lensPoweredProductIndicator_eventually_le_boundary {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (s : Fin n → Fin m)
    {p : Space n × Space n} (hp : p.1 ∈ positivePoweredSimplex n) :
    ∀ᶠ k : ℕ in atTop, lensPoweredProductIndicator τ rows (k+1) s p ≤
      lensPoweredBoundaryIndicator τ rows s p := by
  classical
  by_cases hb : lensBoundaryTraceRows n τ p.2 ∈ boundaryInterpolationEvent τ rows s
  · apply Eventually.of_forall
    intro k
    simpa only [lensPoweredBoundaryIndicator, indicator_of_mem (show p.2 ∈ (lensBoundaryTraceRows n τ) ⁻¹'
        boundaryInterpolationEvent τ rows s from hb)] using
      lensPoweredProductIndicator_le_one τ rows (k+1) s p
  · filter_upwards [lensPoweredProductIndicator_eventually_zero_of_not_boundary
      hτ0 hτ1 rows s hp p.2 hb] with k hk
    simpa only [Prod.eta, hk, lensPoweredBoundaryIndicator, indicator_of_notMem (show p.2 ∉ (lensBoundaryTraceRows n τ) ⁻¹'
        boundaryInterpolationEvent τ rows s from hb)] using
      (le_refl (0 : ℝ≥0∞))

/-- All bases are finite, so their eventual indicator bound can be intersected before limsup. -/
theorem lensPowered_indicator_sum_limsup_le_boundary {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n)
    {p : Space n × Space n} (hp : p.1 ∈ positivePoweredSimplex n) :
    limsup (fun k : ℕ => ∑ s ∈ unsignedBasisIndices rows,
      lensPoweredProductIndicator τ rows (k+1) s p) atTop ≤
        ∑ s ∈ unsignedBasisIndices rows, lensPoweredBoundaryIndicator τ rows s p := by
  classical
  have he : ∀ᶠ k : ℕ in atTop, (∑ s ∈ unsignedBasisIndices rows,
      lensPoweredProductIndicator τ rows (k+1) s p) ≤
        ∑ s ∈ unsignedBasisIndices rows, lensPoweredBoundaryIndicator τ rows s p := by
    have h := eventually_all.mpr (fun s : Fin n → Fin m =>
      lensPoweredProductIndicator_eventually_le_boundary hτ0 hτ1 rows s hp)
    filter_upwards [h] with k hk
    exact Finset.sum_le_sum (fun s _ => hk s)
  exact limsup_le_of_le (h := he)

/-- Integrating the literal closed boundary indicator gives its existing angular probability. -/
theorem lensPoweredBoundaryIndicator_integral {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (s : Fin n → Fin m) :
    (∫⁻ p, lensPoweredBoundaryIndicator τ rows s p ∂lensPoweredProbability n) =
      lensAngularRows n ((lensBoundaryTraceRows n τ) ⁻¹' boundaryInterpolationEvent τ rows s) := by
  let := lensAngularRows_isProbability n
  rw [lensPoweredProbability,
    lintegral_prod _ (measurable_lensPoweredBoundaryIndicator hτ0 hτ1 rows s).aemeasurable]
  simp only [lensPoweredBoundaryIndicator]
  rw [lintegral_indicator_const ((measurable_lensBoundaryTraceRows n τ)
    (isClosed_boundaryInterpolationEvent hτ0 hτ1 rows s).measurableSet)]
  simp

/-- Actual compact-strip angular interpolation cover, with no cover or limiting premise. -/
theorem lensBoundary_angular_interpolation_cover {n m : ℕ} (hn : 1 ≤ n) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (hK : IsCompact (stripBody rows)) :
    1 ≤ ∑ s ∈ unsignedBasisIndices rows,
      lensAngularRows n ((lensBoundaryTraceRows n τ) ⁻¹' boundaryInterpolationEvent τ rows s) := by
  classical
  let f : ℕ → Space n × Space n → ℝ≥0∞ := fun k p =>
    ∑ s ∈ unsignedBasisIndices rows, lensPoweredProductIndicator τ rows (k+1) s p
  have hf (k : ℕ) : Measurable (f k) :=
    Finset.measurable_sum _ (fun s _ => measurable_lensPoweredProductIndicator hτ0 hτ1 rows (k+1) s)
  have hbound (k : ℕ) : f k ≤ᵐ[lensPoweredProbability n]
      fun _ => ((unsignedBasisIndices rows).card : ℝ≥0∞) := by
    apply Eventually.of_forall
    intro p
    calc
      _ ≤ ∑ _s ∈ unsignedBasisIndices rows, (1 : ℝ≥0∞) :=
        Finset.sum_le_sum (fun s _ => lensPoweredProductIndicator_le_one τ rows (k+1) s p)
      _ = _ := by simp
  have hfin : (∫⁻ _p, ((unsignedBasisIndices rows).card : ℝ≥0∞) ∂lensPoweredProbability n) ≠ ∞ := by simp
  have hlower : 1 ≤ limsup (fun k => ∫⁻ p, f k p ∂lensPoweredProbability n) atTop := by
    have he : ∀ᶠ k : ℕ in atTop, 1 ≤ ∫⁻ p, f k p ∂lensPoweredProbability n := by
      apply Eventually.of_forall
      intro k
      rw [show f k = fun p => ∑ s ∈ unsignedBasisIndices rows,
        lensPoweredProductIndicator τ rows (k+1) s p by rfl,
        lintegral_finsetSum _ (fun s _ =>
          measurable_lensPoweredProductIndicator hτ0 hτ1 rows (k+1) s)]
      exact lensPower_powered_probability_lower hn hτ0 hτ1 rows hK (by omega)
    exact le_limsup_of_frequently_le he.frequently
  calc
    _ ≤ limsup (fun k => ∫⁻ p, f k p ∂lensPoweredProbability n) atTop := hlower
    _ ≤ ∫⁻ p, limsup (fun k => f k p) atTop ∂lensPoweredProbability n :=
      limsup_lintegral_le _ hf hbound hfin
    _ ≤ ∫⁻ p, ∑ s ∈ unsignedBasisIndices rows, lensPoweredBoundaryIndicator τ rows s p
        ∂lensPoweredProbability n := by
      apply lintegral_mono_ae
      filter_upwards [lensPoweredProbability_ae_simplex n] with p hp
      exact lensPowered_indicator_sum_limsup_le_boundary hτ0 hτ1 rows hp
    _ = _ := by
      rw [lintegral_finsetSum _ (fun s _ =>
        measurable_lensPoweredBoundaryIndicator hτ0 hτ1 rows s)]
      exact Finset.sum_congr rfl (fun s _ => lensPoweredBoundaryIndicator_integral hτ0 hτ1 rows s)

end
end Funk
