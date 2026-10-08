import Funk.LensPoweredProbability
import Funk.LensStandardBoundaryProbability
import Mathlib.Analysis.SpecificLimits.Basic

/-! Actual powered radii approach the boundary from inside the disk.
Membership in the genuine mass indicator forces the forward sample to lie
in the literal closed interpolation event. A failed limiting boundary event
therefore forces that mass indicator to vanish eventually. -/

open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Funk
noncomputable section

/-- The exact powered-radius forward sample in ordinary complex coordinates. -/
def lensPoweredForwardSample {n : ℕ} (τ : ℝ) (k : ℕ) (t θ : Space n) : Fin n → ℂ :=
  fun i => lensRadialTrace τ (t i ^ (((2*k : ℕ) : ℝ)⁻¹)) (θ i)

theorem lensPoweredRadius_tendsto {t : ℝ} (ht : 0 < t) :
    Tendsto (fun k : ℕ => t ^ (((2*(k+1) : ℕ) : ℝ)⁻¹)) atTop (𝓝 1) := by
  have he : Tendsto (fun k : ℕ => (((2*(k+1) : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1/2)
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
      mul_inv_rev, one_div, mul_zero, zero_mul, mul_comm] using h
  simpa only [Real.rpow_zero, Function.comp_def] using
    (Real.continuousAt_const_rpow ht.ne').tendsto.comp he

theorem lensPoweredRadius_tendsto_from_left {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Tendsto (fun k : ℕ => t ^ (((2*(k+1) : ℕ) : ℝ)⁻¹)) atTop (𝓝[<] 1) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨lensPoweredRadius_tendsto ht0, Eventually.of_forall fun k => ?_⟩
  exact Real.rpow_lt_one ht0.le ht1 (inv_pos.mpr (Nat.cast_pos.mpr (by omega)))

/-- Coordinatewise actual F approaches the literal old boundary trace at every positive simplex point. -/
theorem lensPoweredForwardSample_tendsto {n : ℕ} (τ : ℝ) {t : Space n}
    (ht : t ∈ positivePoweredSimplex n) (θ : Space n) :
    Tendsto (fun k : ℕ => lensPoweredForwardSample τ (k+1) t θ) atTop
      (𝓝 (lensBoundaryTraceRows n τ θ)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  exact (lensRadialTrace_tendsto τ (θ i)).comp
    (lensPoweredRadius_tendsto_from_left (ht.1 i) (positivePoweredSimplex_coordinate_lt_one ht i))

/-- Interior feasibility of the exact basis domain implies closed feasibility of its actual F sample. -/
theorem lensBasisPowerDomain_forward_mem_boundaryInterpolationEvent {n m : ℕ}
    (τ : ℝ) (rows : Fin m → Space n) (k : ℕ) (s : Fin n → Fin m)
    {u : LensComplexSpace n} (hu : u ∈ lensBasisPowerDomain τ rows k s) :
    (fun i => tiltedLens τ (u i)) ∈ boundaryInterpolationEvent τ rows s := by
  intro j
  have hj := hu.2.1 j
  rw [lensBasisParametrization, lensComplexRow_eq_complexRow] at hj
  obtain ⟨hr, hi⟩ := lensBasisMap_inverse_boundaryWitness
    (Matrix.of fun i => rows (s i)) (lensCoordinateForward τ u)
  rw [hr, hi] at hj
  exact interior_subset hj

set_option maxHeartbeats 1000000 in
/-- Nonzero actual powered indicator gives the same literal closed interpolation event. -/
theorem lensPoweredProductIndicator_forward_mem_event {n m : ℕ} (τ : ℝ)
    (rows : Fin m → Space n) (k : ℕ) (s : Fin n → Fin m) (t θ : Space n)
    (hf : lensPoweredProductIndicator τ rows k s (t,θ) ≠ 0) :
    lensPoweredForwardSample τ k t θ ∈ boundaryInterpolationEvent τ rows s := by
  rw [lensPoweredProductIndicator_eq_circleMap] at hf
  let u : LensComplexSpace n :=
    WithLp.toLp 2 (fun i => circleMap 0 (t i ^ (((2*k : ℕ) : ℝ)⁻¹)) (θ i))
  have hu : u ∈ lensBasisPowerDomain τ rows k s := by
    by_contra h
    exact hf (indicator_of_notMem h _)
  have h := lensBasisPowerDomain_forward_mem_boundaryInterpolationEvent τ rows k s hu
  change (fun i => tiltedLens τ (u i)) ∈ boundaryInterpolationEvent τ rows s
  exact h

/-- A failed limiting boundary event makes the actual mass indicator eventually zero. -/
theorem lensPoweredProductIndicator_eventually_zero_of_not_boundary {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (s : Fin n → Fin m)
    {t : Space n} (ht : t ∈ positivePoweredSimplex n) (θ : Space n)
    (hb : lensBoundaryTraceRows n τ θ ∉ boundaryInterpolationEvent τ rows s) :
    ∀ᶠ k : ℕ in atTop, lensPoweredProductIndicator τ rows (k+1) s (t,θ) = 0 := by
  have h := (lensPoweredForwardSample_tendsto τ ht θ).eventually
    ((isClosed_boundaryInterpolationEvent hτ0 hτ1 rows s).isOpen_compl.mem_nhds hb)
  filter_upwards [h] with k hk
  by_contra hf
  exact hk (lensPoweredProductIndicator_forward_mem_event τ rows (k+1) s t θ hf)

end
end Funk
