import Funk.EqualSupportDecay

/-! A column positive at every actual flag vertex has a radius-independent coordinate floor.
One fixed coordinate interval gives degree n growth in dimension n+1, and normalized decay. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace Funk
noncomputable section

/-- Exact ordinary volume with one distinguished interval and n equal remaining intervals. -/
theorem volume_one_coordinate_box {n : ℕ} (i : Fin (n + 1)) (L U a b : ℝ) :
    volume (Icc (i.insertNth a (fun _ => L) : Space (n + 1))
      (i.insertNth b (fun _ => U))) =
      ENNReal.ofReal (b - a) * ENNReal.ofReal (U - L) ^ n := by
  rw [Real.volume_Icc_pi, Fin.prod_univ_succAbove _ i]
  simp

/-- A fixed vertex floor at most one survives all truncations 0<=tau<=1. -/
theorem dualFlagDomain_floor_of_vertices {n : ℕ} {P : Set (Space n)}
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P))
    (i : Fin n) {c τ : ℝ} (hc1 : c ≤ 1) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hv : ∀ k, c ≤ dualCoordinates (flagMatrix G) (flagPoint F k) i)
    {u : Space n} (hu : u ∈ dualFlagDomain τ F G) : c ≤ u i := by
  rw [dualFlagDomain_eq_convexHull] at hu
  have hverts : Set.range (fun k => dualCoordinates (flagMatrix G) (τ • flagPoint F k)) ⊆
      {u : Space n | c ≤ u i} := by
    rintro _ ⟨k, rfl⟩
    have hbase := hv k
    simp only [dualCoordinates_component] at hbase
    have h0 := mul_le_mul_of_nonneg_right hc1 (sub_nonneg.mpr hτ1)
    have h1 := mul_le_mul_of_nonneg_left hbase hτ0
    change c ≤ dualCoordinates (flagMatrix G) (τ • flagPoint F k) i
    simp only [dualFlagDomain_vertex_component]
    nlinarith
  have hconv : Convex ℝ {u : Space n | c ≤ u i} := by
    intro x hx y hy s t hs ht hst
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left hx hs, mul_le_mul_of_nonneg_left hy ht]
  exact convexHull_min hverts hconv hu

/-- Positivity at all actual vertices supplies a fixed floor without a supplied constant. -/
theorem exists_dualLogDomain_box_of_positive_column {n : ℕ} {P : Set (Space (n + 1))}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P))
    (i : Fin (n + 1))
    (hv : ∀ k, 0 < dualCoordinates (flagMatrix G) (flagPoint F k) i) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ R : ℝ, 0 < R →
      dualLogDomain (radius R) F G ⊆
        Icc (i.insertNth (Real.log c) (fun _ => -R)) (fun _ => Real.log 2) := by
  obtain ⟨c, hc, hc1, hfloor⟩ := finite_positive_floor Finset.univ
    (fun k => dualCoordinates (flagMatrix G) (flagPoint F k) i) (fun k _ => hv k)
  refine ⟨c, hc, hc1, ?_⟩
  intro R hR z hz
  have hbase := dualFlagDomain_floor_of_vertices F G i hc1
    (radius_pos hR).le (radius_lt_one R).le (fun k => hfloor k (Finset.mem_univ _)) hz
  have hlog := Real.log_le_log hc hbase
  simp only [expCoordinates, Real.log_exp] at hlog
  refine ⟨?_, ?_⟩
  · change ∀ j, (i.insertNth (Real.log c) (fun _ => -R) : Space (n + 1)) j ≤ z j
    intro j
    induction j using i.succAboveCases
    · simpa only [Fin.insertNth_apply_same] using hlog
    · rename_i j
      simpa only [Fin.insertNth_apply_succAbove] using
        (dualLogDomain_radius_bounds hp hP hR F G hz (i.succAbove j)).1
  · intro j
    have hb := (dualLogDomain_radius_bounds hp hP hR F G hz j).2
    have hpos : 0 < 2 - Real.exp (-R) :=
      by linarith [(Real.exp_lt_one_iff.mpr (show -R < 0 by linarith))]
    exact hb.trans (Real.log_le_log hpos (by linarith [Real.exp_pos (-R)]))

/-- The actual logarithmic domain fits a box with one fixed side. -/
theorem exists_dualFlag_integral_lower_degree_of_positive_column
    {n : ℕ} {P : Set (Space (n + 1))}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P))
    (i : Fin (n + 1))
    (hv : ∀ k, 0 < dualCoordinates (flagMatrix G) (flagPoint F k) i) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 0 < R →
      (∫⁻ u in dualFlagDomain (radius R) F G, dualProductKernel u) ≤
        ENNReal.ofReal (K * (R + Real.log 2) ^ n) := by
  obtain ⟨c, hc, hc1, hbox⟩ := exists_dualLogDomain_box_of_positive_column hp hP F G i hv
  have hlog : Real.log c ≤ 0 := Real.log_nonpos hc.le hc1
  let K := (Real.log 2 - Real.log c) / ((n + 1).factorial : ℝ)
  have hwidth : 0 ≤ Real.log 2 - Real.log c := by
    linarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]
  refine ⟨K, div_nonneg hwidth (Nat.cast_nonneg _), ?_⟩
  intro R hR
  rw [dualFlag_integral_eq_log_volume hp hP (radius_pos hR).le (radius_lt_one R)]
  calc
    _ ≤ ENNReal.ofReal (1 / ((n + 1).factorial : ℝ)) *
        volume (Icc (i.insertNth (Real.log c) (fun _ => -R)) (fun _ => Real.log 2)) :=
      mul_le_mul_right (measure_mono (hbox R hR)) _
    _ = _ := by
      have hconst : (fun _ : Fin (n + 1) => Real.log 2) =
          i.insertNth (Real.log 2) (fun _ => Real.log 2) := by
        ext j
        induction j using i.succAboveCases <;> simp
      rw [hconst, volume_one_coordinate_box,
        ← ENNReal.ofReal_pow (by linarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]),
        ← ENNReal.ofReal_mul hwidth, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      dsimp [K]
      ring

/-- A positive column removes the leading term of the actual contribution. -/
theorem tendsto_dualFlag_integral_positive_column_ratio_zero
    {n : ℕ} {P : Set (Space (n + 1))}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P))
    (i : Fin (n + 1))
    (hv : ∀ k, 0 < dualCoordinates (flagMatrix G) (flagPoint F k) i) :
    Tendsto (fun R : ℝ =>
      (∫⁻ u in dualFlagDomain (radius R) F G, dualProductKernel u).toReal /
        R ^ (n + 1)) atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨K, hK, hb⟩ := exists_dualFlag_integral_lower_degree_of_positive_column hp hP F G i hv
  exact tendsto_dualFlag_integral_ratio_zero_of_lower_degree hp hP F G hK hb

/-- Every larger radius satisfies the epsilon envelope once the threshold is reached. -/
theorem dualFlag_integral_positive_column_epsilon_upper
    {n : ℕ} {P : Set (Space (n + 1))}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P))
    (i : Fin (n + 1))
    (hv : ∀ k, 0 < dualCoordinates (flagMatrix G) (flagPoint F k) i)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      (∫⁻ u in dualFlagDomain (radius R) F G, dualProductKernel u) ≤
        ENNReal.ofReal (ε * R ^ (n + 1)) := by
  obtain ⟨K, _, hK⟩ := exists_dualFlag_integral_lower_degree_of_positive_column hp hP F G i hv
  obtain ⟨b, hb⟩ := eventually_atTop.mp (eventually_lower_degree_le n K (Real.log 2) hε)
  refine ⟨max b 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro R hR
  have h := hb R ((le_max_left _ _).trans hR)
  exact (hK R h.1).trans (ENNReal.ofReal_le_ofReal h.2)

end
end Funk
