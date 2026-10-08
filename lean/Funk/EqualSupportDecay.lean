import Funk.LogCoordinateBand
import Funk.PairLeadingUpper

/-! Equal positive supports give a bounded logarithmic difference and degree n-1 growth.
The support equality is an explicit condition on genuine flag vertices. No classification of
all distinct flag pairs is assumed to follow from this conditional decay result. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace Funk
noncomputable section

/-- Equal supports give two uniform comparison inequalities, including their zero entries. -/
theorem exists_ratio_of_equal_positiveSupport {κ : Type*} [Fintype κ] {n : ℕ}
    (V : κ → Space n) (hV : ∀ k i, 0 ≤ V k i) (i j : Fin n)
    (hs : positiveSupport V i = positiveSupport V j) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ k, c * V k j ≤ V k i ∧ c * V k i ≤ V k j := by
  obtain ⟨c, hc, hc1, hr⟩ := exists_positive_comparison_ratio V hV
  have hpos (k : κ) : 0 < V k i ↔ 0 < V k j := by
    rw [← mem_positiveSupport, hs, mem_positiveSupport]
  refine ⟨c, hc, hc1, ?_⟩
  intro k
  by_cases hi : 0 < V k i
  · exact ⟨hr k i j hi, hr k j i ((hpos k).mp hi)⟩
  · have hj : ¬ 0 < V k j := fun h => hi ((hpos k).mpr h)
    have hzi : V k i = 0 := le_antisymm (le_of_not_gt hi) (hV k i)
    have hzj : V k j = 0 := le_antisymm (le_of_not_gt hj) (hV k j)
    simp [hzi, hzj]

/-- A one-sided comparison at actual vertices survives truncation and convexification. -/
theorem dualFlagDomain_comparison_of_vertices {n : ℕ} {P : Set (Space n)}
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P))
    (i j : Fin n) {c τ : ℝ} (hc1 : c ≤ 1) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hv : ∀ k, c * dualCoordinates (flagMatrix G) (flagPoint F k) j ≤
      dualCoordinates (flagMatrix G) (flagPoint F k) i)
    {u : Space n} (hu : u ∈ dualFlagDomain τ F G) : c * u j ≤ u i := by
  rw [dualFlagDomain_eq_convexHull] at hu
  have hverts : Set.range (fun k => dualCoordinates (flagMatrix G) (τ • flagPoint F k)) ⊆
      {u : Space n | c * u j ≤ u i} := by
    rintro _ ⟨k, rfl⟩
    have hbase := hv k
    simp only [dualCoordinates_component] at hbase
    have h0 : c * (1 - τ) ≤ 1 - τ := by
      nlinarith [mul_le_mul_of_nonneg_right hc1 (sub_nonneg.mpr hτ1)]
    have h1 := mul_le_mul_of_nonneg_left hbase hτ0
    change c * dualCoordinates (flagMatrix G) (τ • flagPoint F k) j ≤
      dualCoordinates (flagMatrix G) (τ • flagPoint F k) i
    simp only [dualFlagDomain_vertex_component]
    nlinarith
  have hconv : Convex ℝ {u : Space n | c * u j ≤ u i} := by
    intro x hx y hy s t hs ht _
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left hx hs, mul_le_mul_of_nonneg_left hy ht]
  exact convexHull_min hverts hconv hu

/-- The two comparisons become a fixed interval for the actual logarithmic difference. -/
theorem dualLogDomain_difference_bounds {n : ℕ} {P : Set (Space n)}
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P))
    (i j : Fin n) {c τ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hv : ∀ k, c * dualCoordinates (flagMatrix G) (flagPoint F k) j ≤
        dualCoordinates (flagMatrix G) (flagPoint F k) i ∧
      c * dualCoordinates (flagMatrix G) (flagPoint F k) i ≤
        dualCoordinates (flagMatrix G) (flagPoint F k) j)
    {z : Space n} (hz : z ∈ dualLogDomain τ F G) :
    Real.log c ≤ z i - z j ∧ z i - z j ≤ -Real.log c := by
  have h1 := dualFlagDomain_comparison_of_vertices F G i j hc1 hτ0 hτ1
    (fun k => (hv k).1) hz
  have h2 := dualFlagDomain_comparison_of_vertices F G j i hc1 hτ0 hτ1
    (fun k => (hv k).2) hz
  have hl1 := Real.log_le_log (mul_pos hc (expCoordinates_pos z j)) h1
  have hl2 := Real.log_le_log (mul_pos hc (expCoordinates_pos z i)) h2
  simp only [expCoordinates, Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp] at hl1 hl2
  constructor <;> linarith

/-- Support equality supplies an actual fixed-width band, without a numerical ratio input. -/
theorem exists_dualLogDomain_band_of_equal_support {n : ℕ} {P : Set (Space (n + 1))}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P))
    (i : Fin (n + 1)) (j : Fin n)
    (hs : positiveSupport (fun k => dualCoordinates (flagMatrix G) (flagPoint F k)) i =
      positiveSupport (fun k => dualCoordinates (flagMatrix G) (flagPoint F k)) (i.succAbove j)) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ R : ℝ, 0 < R →
      dualLogDomain (radius R) F G ⊆
        logCoordinateBand i j (-R) (Real.log 2) (Real.log c) (-Real.log c) := by
  obtain ⟨c, hc, hc1, hv⟩ := exists_ratio_of_equal_positiveSupport
    (fun k => dualCoordinates (flagMatrix G) (flagPoint F k))
    (flag_dual_vertex_nonneg hp hP F G) i (i.succAbove j) hs
  refine ⟨c, hc, hc1, ?_⟩
  intro R hR z hz
  have hd := dualLogDomain_difference_bounds F G i (i.succAbove j) hc hc1
    (radius_pos hR).le (radius_lt_one R).le hv hz
  refine ⟨?_, by linarith [hd.1], by linarith [hd.2]⟩
  intro k
  have hb := dualLogDomain_radius_bounds hp hP hR F G hz (i.succAbove k)
  have hlog : Real.log (2 - Real.exp (-R)) ≤ Real.log 2 :=
    Real.log_le_log (by linarith [(Real.exp_lt_one_iff.mpr (show -R < 0 by linarith))]) (by linarith [Real.exp_pos (-R)])
  exact ⟨hb.1, hb.2.trans hlog⟩

/-- A genuine pair with equal supports has a degree n upper in ambient dimension n+1. -/
theorem exists_dualFlag_integral_lower_degree_of_equal_support
    {n : ℕ} {P : Set (Space (n + 1))}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P))
    (i : Fin (n + 1)) (j : Fin n)
    (hs : positiveSupport (fun k => dualCoordinates (flagMatrix G) (flagPoint F k)) i =
      positiveSupport (fun k => dualCoordinates (flagMatrix G) (flagPoint F k)) (i.succAbove j)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 0 < R →
      (∫⁻ u in dualFlagDomain (radius R) F G, dualProductKernel u) ≤
        ENNReal.ofReal (K * (R + Real.log 2) ^ n) := by
  obtain ⟨c, hc, hc1, hband⟩ := exists_dualLogDomain_band_of_equal_support hp hP F G i j hs
  have hlog : Real.log c ≤ 0 := Real.log_nonpos hc.le hc1
  let K := (-2 * Real.log c) / ((n + 1).factorial : ℝ)
  have hK : 0 ≤ K := div_nonneg (by linarith) (Nat.cast_nonneg _)
  refine ⟨K, hK, ?_⟩
  intro R hR
  rw [dualFlag_integral_eq_log_volume hp hP (radius_pos hR).le (radius_lt_one R)]
  calc
    _ ≤ ENNReal.ofReal (1 / ((n + 1).factorial : ℝ)) *
        volume (logCoordinateBand i j (-R) (Real.log 2) (Real.log c) (-Real.log c)) :=
      mul_le_mul_right (measure_mono (hband R hR)) _
    _ = _ := by
      rw [volume_logCoordinateBand, ← ENNReal.ofReal_pow (by linarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]),
        ← ENNReal.ofReal_mul (show 0 ≤ -Real.log c - Real.log c by linarith),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      dsimp [K]
      ring

/-- One fewer power has normalized limit zero, even with a fixed shift and multiplier. -/
theorem tendsto_lower_degree_ratio (n : ℕ) (K C : ℝ) :
    Tendsto (fun R : ℝ => K * (R + C) ^ n / R ^ (n + 1)) atTop (𝓝 (0 : ℝ)) := by
  have ht := (tendsto_const_nhds (x := K)).mul
    ((tendsto_shifted_power_ratio n C 1).mul
      (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 (0 : ℝ))))
  simp only [div_one, mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [div_pow, pow_succ]
  field_simp

/-- The degree bound gives arbitrarily small leading coefficient at every large radius. -/
theorem eventually_lower_degree_le (n : ℕ) (K C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, 0 < R ∧ K * (R + C) ^ n ≤ ε * R ^ (n + 1) := by
  have he := (tendsto_lower_degree_ratio n K C).eventually_lt_const hε
  filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with R h hR
  exact ⟨hR, ((div_lt_iff₀ (pow_pos hR _)).mp h).le⟩

/-- Convert a proved actual lower-degree bound into a normalized zero limit.
Finiteness is established before using toReal; the bound is on the genuine integral. -/
theorem tendsto_dualFlag_integral_ratio_zero_of_lower_degree
    {n : ℕ} {P : Set (Space (n + 1))}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P))
    {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ R : ℝ, 0 < R →
      (∫⁻ u in dualFlagDomain (radius R) F G, dualProductKernel u) ≤
        ENNReal.ofReal (K * (R + Real.log 2) ^ n)) :
    Tendsto (fun R : ℝ =>
      (∫⁻ u in dualFlagDomain (radius R) F G, dualProductKernel u).toReal /
        R ^ (n + 1)) atTop (𝓝 (0 : ℝ)) := by
  apply squeeze_zero' ?_ ?_ (tendsto_lower_degree_ratio n K (Real.log 2))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact div_nonneg ENNReal.toReal_nonneg (pow_nonneg hR.le _)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hfin := dualFlag_integral_finite hp hP (radius_pos hR).le (radius_lt_one R) F G
    have hnonneg : 0 ≤ K * (R + Real.log 2) ^ n :=
      mul_nonneg hK (pow_nonneg (by linarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]) _)
    exact div_le_div_of_nonneg_right
      ((ENNReal.le_ofReal_iff_toReal_le hfin.ne hnonneg).mp (hb R hR)) (pow_nonneg hR.le _)

/-- Equal positive supports remove the leading term in the actual integral. -/
theorem tendsto_dualFlag_integral_equal_support_ratio_zero
    {n : ℕ} {P : Set (Space (n + 1))}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P))
    (i : Fin (n + 1)) (j : Fin n)
    (hs : positiveSupport (fun k => dualCoordinates (flagMatrix G) (flagPoint F k)) i =
      positiveSupport (fun k => dualCoordinates (flagMatrix G) (flagPoint F k)) (i.succAbove j)) :
    Tendsto (fun R : ℝ =>
      (∫⁻ u in dualFlagDomain (radius R) F G, dualProductKernel u).toReal /
        R ^ (n + 1)) atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨K, hK, hb⟩ := exists_dualFlag_integral_lower_degree_of_equal_support hp hP F G i j hs
  exact tendsto_dualFlag_integral_ratio_zero_of_lower_degree hp hP F G hK hb

/-- Actual contribution decay, with the equal-support geometric condition retained. -/
theorem dualFlag_integral_equal_support_epsilon_upper
    {n : ℕ} {P : Set (Space (n + 1))}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P))
    (i : Fin (n + 1)) (j : Fin n)
    (hs : positiveSupport (fun k => dualCoordinates (flagMatrix G) (flagPoint F k)) i =
      positiveSupport (fun k => dualCoordinates (flagMatrix G) (flagPoint F k)) (i.succAbove j))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      (∫⁻ u in dualFlagDomain (radius R) F G, dualProductKernel u) ≤
        ENNReal.ofReal (ε * R ^ (n + 1)) := by
  obtain ⟨K, _, hK⟩ := exists_dualFlag_integral_lower_degree_of_equal_support hp hP F G i j hs
  obtain ⟨b, hb⟩ := eventually_atTop.mp (eventually_lower_degree_le n K (Real.log 2) hε)
  refine ⟨max b 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro R hR
  have h := hb R ((le_max_left _ _).trans hR)
  exact (hK R h.1).trans (ENNReal.ofReal_le_ofReal h.2)

end
end Funk
