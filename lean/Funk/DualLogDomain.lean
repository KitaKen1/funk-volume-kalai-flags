import Funk.DualFlagUpper
import Funk.LogCoordinates

/-! Actual flag-pair integrals are ordinary volumes in logarithmic coordinates.
The coarse box bound is not the sharp FVW coefficient. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

def dualLogDomain {n : ℕ} {P : Set (Space n)} (τ : ℝ)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) : Set (Space n) :=
  expCoordinates ⁻¹' dualFlagDomain τ F G

theorem dualLogDomain_measurableSet {n : ℕ} {P : Set (Space n)} (τ : ℝ)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) :
    MeasurableSet (dualLogDomain τ F G) :=
  (dualFlagDomain_measurableSet τ F G).preimage (continuous_expCoordinates n).measurable

theorem expCoordinates_image_dualLogDomain {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) :
    expCoordinates '' dualLogDomain τ F G = dualFlagDomain τ F G :=
  expCoordinates_image_preimage (fun _ hu i =>
    dualFlagDomain_coordinates_pos hp hP hτ0 hτ1 F G hu i)

theorem dualLogDomain_eq_log_image {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) :
    dualLogDomain τ F G = logCoordinates '' dualFlagDomain τ F G :=
  preimage_expCoordinates_eq_log_image (fun _ hu i =>
    dualFlagDomain_coordinates_pos hp hP hτ0 hτ1 F G hu i)

theorem dualLogDomain_isCompact {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) :
    IsCompact (dualLogDomain τ F G) := by
  rw [dualLogDomain_eq_log_image hp hP hτ0 hτ1 F G]
  apply (dualFlagDomain_isCompact τ F G).image_of_continuousOn
  apply continuousOn_pi.mpr
  intro i
  exact (continuous_apply i).continuousOn.log (fun u hu =>
    ne_of_gt (dualFlagDomain_coordinates_pos hp hP hτ0 hτ1 F G hu i))

/-- Exact flattening of an actual flag-pair contribution, with all adapters supplied. -/
theorem dualFlag_integral_eq_log_volume {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) :
    (∫⁻ u in dualFlagDomain τ F G, dualProductKernel u) =
      ENNReal.ofReal (1 / (n.factorial : ℝ)) * volume (dualLogDomain τ F G) := by
  rw [← expCoordinates_image_dualLogDomain hp hP hτ0 hτ1 F G]
  exact lintegral_expCoordinates_kernel (dualLogDomain_measurableSet τ F G)

theorem dualLogDomain_radius_bounds {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    {R : ℝ} (hR : 0 < R) (F : FullFlagWithTop P)
    (G : FullFlagWithTop (coordinatePolar P)) {z : Space n}
    (hz : z ∈ dualLogDomain (radius R) F G) (i : Fin n) :
    -R ≤ z i ∧ z i ≤ Real.log (2 - Real.exp (-R)) := by
  have hb := dualFlagDomain_radius_bounds hp hP hR F G hz i
  constructor
  · exact Real.exp_le_exp.mp hb.1
  · have hp' : 0 < 2 - Real.exp (-R) :=
      lt_of_lt_of_le (expCoordinates_pos z i) hb.2
    exact (Real.le_log_iff_exp_le hp').mpr hb.2

theorem dualLogDomain_radius_subset_box {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    {R : ℝ} (hR : 0 < R) (F : FullFlagWithTop P)
    (G : FullFlagWithTop (coordinatePolar P)) :
    dualLogDomain (radius R) F G ⊆
      Set.Icc (fun _ => -R) (fun _ => Real.log (2 - Real.exp (-R))) := by
  intro z hz
  exact ⟨fun i => (dualLogDomain_radius_bounds hp hP hR F G hz i).1,
    fun i => (dualLogDomain_radius_bounds hp hP hR F G hz i).2⟩

theorem dualFlag_integral_le_log_box {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    {R : ℝ} (hR : 0 < R) (F : FullFlagWithTop P)
    (G : FullFlagWithTop (coordinatePolar P)) :
    (∫⁻ u in dualFlagDomain (radius R) F G, dualProductKernel u) ≤
      ENNReal.ofReal ((R + Real.log (2 - Real.exp (-R))) ^ n / (n.factorial : ℝ)) := by
  have he : Real.exp (-R) ≤ 1 := (Real.exp_lt_one_iff.mpr (by linarith)).le
  have hw : 0 ≤ R + Real.log (2 - Real.exp (-R)) :=
    add_nonneg hR.le (Real.log_nonneg (by linarith))
  rw [dualFlag_integral_eq_log_volume hp hP (radius_pos hR).le (radius_lt_one R)]
  calc
    _ ≤ ENNReal.ofReal (1 / (n.factorial : ℝ)) *
        volume (Set.Icc (fun _ : Fin n => -R)
          (fun _ => Real.log (2 - Real.exp (-R)))) :=
      mul_le_mul_right (measure_mono (dualLogDomain_radius_subset_box hp hP hR F G)) _
    _ = _ := by
      rw [Real.volume_Icc_pi]
      simp only [sub_neg_eq_add, add_comm (Real.log _) R, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
      rw [← ENNReal.ofReal_pow hw, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

/-- Concrete frozen-volume upper bound by ordinary log-domain volumes. -/
theorem funkVolume_radius_le_dualLog_volumes {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    {R : ℝ} (hR : 0 < R) :
    let : Finite (FullFlagWithTop P) := fullFlagWithTop_finite hp hP
    let : Fintype (FullFlagWithTop P) := Fintype.ofFinite (FullFlagWithTop P)
    let : Finite (FullFlagWithTop (coordinatePolar P)) := fullFlagWithTop_finite
      (coordinatePolar_isFinitePolytope hp hP.2.1 hP.2.2.2)
      (coordinatePolar_isSymmetricConvexBody hp hP)
    let : Fintype (FullFlagWithTop (coordinatePolar P)) :=
      Fintype.ofFinite (FullFlagWithTop (coordinatePolar P))
    funkVolume P (radius R) ≤ ∑ F : FullFlagWithTop P,
      ∑ G : FullFlagWithTop (coordinatePolar P),
        ENNReal.ofReal (1 / (n.factorial : ℝ)) * volume (dualLogDomain (radius R) F G) := by
  let : Finite (FullFlagWithTop P) := fullFlagWithTop_finite hp hP
  let : Fintype (FullFlagWithTop P) := Fintype.ofFinite (FullFlagWithTop P)
  let : Finite (FullFlagWithTop (coordinatePolar P)) := fullFlagWithTop_finite
    (coordinatePolar_isFinitePolytope hp hP.2.1 hP.2.2.2)
    (coordinatePolar_isSymmetricConvexBody hp hP)
  let : Fintype (FullFlagWithTop (coordinatePolar P)) :=
    Fintype.ofFinite (FullFlagWithTop (coordinatePolar P))
  apply le_trans (funkVolume_radius_le_dualFlag_integrals hp hP hR)
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro F _
  apply Finset.sum_congr rfl
  intro G _
  exact dualFlag_integral_eq_log_volume hp hP (radius_pos hR).le (radius_lt_one R) F G

end
end Funk
