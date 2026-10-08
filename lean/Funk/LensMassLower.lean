import Funk.LensPowerMassInput
import Funk.LensMassExhaustion
import OAI.Analysis.Mahler.HomogeneousEndpoint
import OAI.Analysis.Mahler.HomogeneousMassAssembly
import OAI.Analysis.Mahler.MassLimit

/-! Application of the unchanged pinned homogeneous-flux and Stokes proofs to
our actual tilted lens. This proves a mass lower bound; probability covering
and its Jacobian/radial/reverse-Fatou upper estimate are separate obligations. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Funk
noncomputable section

theorem lensPower_upstream_tau_eq {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n) (k : ℕ)
    (z : LensComplexSpace n) :
    OAI.Mahler.tau (fun j => lensPowerComponent τ rows k j) z =
      lensPowerEnergy τ rows k z := by
  simp only [OAI.Mahler.tau, lensPowerEnergy, Complex.normSq_eq_norm_sq]

/-- All ten genuine upstream input fields follow from the local geometry. -/
theorem lensPower_upstream_massHypotheses {n m : ℕ} (hn : 1 ≤ n) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n)
    (hK : IsCompact (stripBody rows)) {k : ℕ} (hk : 1 ≤ k) :
    OAI.Mahler.MassHypotheses n m k (lensComplexDomain τ rows)
      (fun j => lensPowerComponent τ rows k j) (lensLeadingPolynomial τ rows k) := by
  have h := lensPowerMassInput_of_compact hn hτ0 hτ1 rows hK hk
  exact {
    dimension_pos := h.dimension_pos
    degree_pos := h.degree_pos
    open_domain := h.open_domain
    zero_mem := h.zero_mem
    holomorphic := h.holomorphic
    isolated_zero := h.isolated_zero
    homogeneous := h.homogeneous
    leading_nonzero := h.leading_nonzero
    taylor_remainder := h.taylor_remainder
    compact_sublevels := fun R hR hR1 => by
      simpa only [lensPower_upstream_tau_eq] using h.compact_sublevels R hR hR1 }

theorem lensPower_upstream_tau_fderiv_ne_zero {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n)
    (hK : IsCompact (stripBody rows)) {k : ℕ} (hk : 1 ≤ k)
    {R : ℝ} (hR : 0 < R) {z : LensComplexSpace n}
    (hz : z ∈ lensComplexDomain τ rows)
    (he : OAI.Mahler.tau (fun j => lensPowerComponent τ rows k j) z = R) :
    fderiv ℝ (OAI.Mahler.tau (fun j => lensPowerComponent τ rows k j)) z ≠ 0 := by
  have ht : OAI.Mahler.tau (fun j => lensPowerComponent τ rows k j) =
      lensPowerEnergy τ rows k := funext (lensPower_upstream_tau_eq τ rows k)
  rw [ht] at he ⊢
  exact lensPowerEnergy_positive_fderiv_ne_zero hτ0 hτ1 rows hK hk hR hz he

/-- The actual leading polynomial has the full numerical homogeneous flux. -/
theorem lensPower_homogeneousSphereFlux_value {d m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space (d+1))
    (hK : IsCompact (stripBody rows)) {k : ℕ} (hk : 1 ≤ k) :
    OAI.Mahler.homogeneousSphereFlux d m (lensLeadingPolynomial τ rows k) =
      (Real.pi * (k : ℝ)) ^ (d+1) :=
  (lensPower_upstream_massHypotheses (by omega) hτ0 hτ1 rows hK hk).homogeneousSphereFlux_value

/-- No regularity or homogeneous-value premise is left to the caller. -/
theorem lensPower_massBelow_lower {d m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space (d+1))
    (hK : IsCompact (stripBody rows)) {k : ℕ} (hk : 1 ≤ k)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1) :
    ENNReal.ofReal (R^(d+1) * (Real.pi * (k : ℝ))^(d+1)) ≤
      OAI.Mahler.massBelow (lensComplexDomain τ rows)
        (fun j => lensPowerComponent τ rows k j) R := by
  have h := lensPower_upstream_massHypotheses (by omega) hτ0 hτ1 rows hK hk
  exact h.regular_massBelow_of_homogeneous_value hR hR1
    (fun _ hz he => lensPower_upstream_tau_fderiv_ne_zero hτ0 hτ1 rows hK hk hR hz he)
    h.homogeneousSphereFlux_value

/-- Dyadic sublevel lower bounds tend to the full mass, even for infinite mass. -/
theorem lensPower_massIntegral_lower_succ {d m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space (d+1))
    (hK : IsCompact (stripBody rows)) {k : ℕ} (hk : 1 ≤ k) :
    ENNReal.ofReal ((Real.pi * (k : ℝ))^(d+1)) ≤
      OAI.Mahler.massIntegral (lensComplexDomain τ rows)
        (fun j => lensPowerComponent τ rows k j) := by
  apply OAI.Mahler.massIntegral_lower_of_sublevels _ _ k lensRegularLevel_tendsto
    (fun r => (lensRegularLevel_mem r).2.le)
  intro r
  exact lensPower_massBelow_lower hτ0 hτ1 rows hK hk
    (lensRegularLevel_mem r).1 (lensRegularLevel_mem r).2

/-- The mass lower bound holds in every positive complex dimension. -/
theorem lensPower_massIntegral_lower {n m : ℕ} (hn : 1 ≤ n) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n)
    (hK : IsCompact (stripBody rows)) {k : ℕ} (hk : 1 ≤ k) :
    ENNReal.ofReal ((Real.pi * (k : ℝ))^n) ≤
      OAI.Mahler.massIntegral (lensComplexDomain τ rows)
        (fun j => lensPowerComponent τ rows k j) := by
  cases n with
  | zero => omega
  | succ d => exact lensPower_massIntegral_lower_succ hτ0 hτ1 rows hK hk

end
end Funk
