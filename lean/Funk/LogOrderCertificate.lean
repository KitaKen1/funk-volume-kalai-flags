import Funk.DualLogDomain
import Funk.OrderedLogSimplex
import Mathlib.MeasureTheory.Group.Measure

/-! Finite vertex inequalities certify ordered logarithmic containment.
A positive scaling and coordinate permutation are supplied as checkable witnesses, not as a solved flag
correspondence or a proved existence theorem for all matching flag pairs. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

def orderedLogTranslate {n : ℕ} (v : Space n) (σ : Equiv.Perm (Fin n)) (r : ℝ) : Set (Space n) :=
  (fun z => fun i => z (σ i) - v i) ⁻¹' orderedLogSimplex n r

theorem isClosed_orderedLogTranslate {n : ℕ} (v : Space n) (σ : Equiv.Perm (Fin n)) (r : ℝ) :
    IsClosed (orderedLogTranslate v σ r) := by
  apply (isClosed_orderedLogSimplex n r).preimage
  fun_prop

theorem volume_orderedLogTranslate {n : ℕ} (v : Space n) (σ : Equiv.Perm (Fin n)) {r : ℝ} (hr : 0 ≤ r) :
    volume (orderedLogTranslate v σ r) = ENNReal.ofReal (r ^ n / (n.factorial : ℝ)) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ.symm
  have hcoord (z : Space n) (i : Fin n) : e z i = z (σ i) := by
    simpa [e] using MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => ℝ) σ.symm z (σ i)
  have he : (fun z : Space n => fun i => z (σ i) - v i) =
      (fun z : Space n => z - v) ∘ e := by
    funext z
    ext i
    exact congrArg (fun t => t - v i) (hcoord z i).symm
  have hm : MeasurableSet ((fun z : Space n => z - v) ⁻¹' orderedLogSimplex n r) :=
    (isClosed_orderedLogSimplex n r).measurableSet.preimage
      (continuous_id.sub continuous_const).measurable
  rw [orderedLogTranslate, he, Set.preimage_comp,
    (volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) σ.symm).measure_preimage
      hm.nullMeasurableSet]
  have ht : (fun z : Space n => z - v) = fun z => -v + z := by
    funext z
    abel
  rw [ht, measure_preimage_add, volume_orderedLogSimplex n hr]

theorem lintegral_exp_orderedLogTranslate {n : ℕ} (v : Space n) (σ : Equiv.Perm (Fin n)) {r : ℝ} (hr : 0 ≤ r) :
    (∫⁻ u in expCoordinates '' orderedLogTranslate v σ r, dualProductKernel u) =
      ENNReal.ofReal (r ^ n / (n.factorial : ℝ) ^ 2) := by
  rw [lintegral_expCoordinates_kernel (isClosed_orderedLogTranslate v σ r).measurableSet,
    volume_orderedLogTranslate v σ hr, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- A finite certificate: inequalities need only be checked on genuine flag vertices. -/
def FlagOrderCertificate {n : ℕ} {P : Set (Space n)}
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P))
    (σ : Equiv.Perm (Fin n)) (a : Space n) : Prop :=
  ∀ k : Fin (n + 1), ∀ i j : Fin n, i ≤ j →
    a j * dualCoordinates (flagMatrix G) (flagPoint F k) (σ j) ≤
      a i * dualCoordinates (flagMatrix G) (flagPoint F k) (σ i)

theorem flagOrderCertificate_antitone {n : ℕ} {P : Set (Space n)}
    {F : FullFlagWithTop P} {G : FullFlagWithTop (coordinatePolar P)}
    {σ : Equiv.Perm (Fin n)} {a : Space n} (hc : FlagOrderCertificate F G σ a) : Antitone a := by
  intro i j hij
  have h := hc (Fin.last n) i j hij
  simpa [flagPoint_top, dualCoordinates_apply] using h

/-- Truncation preserves a certificate because the top vertex is the all-one vector. -/
theorem flagOrderCertificate_scaled_vertices {n : ℕ} {P : Set (Space n)}
    {F : FullFlagWithTop P} {G : FullFlagWithTop (coordinatePolar P)}
    {σ : Equiv.Perm (Fin n)} {a : Space n} (hc : FlagOrderCertificate F G σ a)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (k : Fin (n + 1)) (i j : Fin n) (hij : i ≤ j) :
    a j * dualCoordinates (flagMatrix G) (τ • flagPoint F k) (σ j) ≤
      a i * dualCoordinates (flagMatrix G) (τ • flagPoint F k) (σ i) := by
  have hbase := hc k i j hij
  simp only [dualCoordinates_component] at hbase
  have htop := flagOrderCertificate_antitone hc hij
  have h0 := mul_le_mul_of_nonneg_right htop (sub_nonneg.mpr hτ1)
  have h1 := mul_le_mul_of_nonneg_left hbase hτ0
  simp only [dualFlagDomain_vertex_component]
  nlinarith

/-- Convexity upgrades the finite linear certificate to the actual entire domain. -/
theorem dualFlagDomain_order_of_certificate {n : ℕ} {P : Set (Space n)}
    {F : FullFlagWithTop P} {G : FullFlagWithTop (coordinatePolar P)}
    {σ : Equiv.Perm (Fin n)} {a : Space n} (hc : FlagOrderCertificate F G σ a)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    {u : Space n} (hu : u ∈ dualFlagDomain τ F G) :
    Antitone (fun i => a i * u (σ i)) := by
  rw [dualFlagDomain_eq_convexHull] at hu
  intro i j hij
  have hv : Set.range (fun k => dualCoordinates (flagMatrix G) (τ • flagPoint F k)) ⊆
      {u : Space n | a j * u (σ j) ≤ a i * u (σ i)} := by
    rintro _ ⟨k, rfl⟩
    exact flagOrderCertificate_scaled_vertices hc hτ0 hτ1 k i j hij
  have hconv : Convex ℝ {u : Space n | a j * u (σ j) ≤ a i * u (σ i)} := by
    intro x hx y hy s t hs ht _
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left hx hs, mul_le_mul_of_nonneg_left hy ht]
  exact convexHull_min hv hconv hu

theorem dualLogDomain_order_of_certificate {n : ℕ} {P : Set (Space n)}
    {F : FullFlagWithTop P} {G : FullFlagWithTop (coordinatePolar P)}
    {σ : Equiv.Perm (Fin n)} {a : Space n} (ha : ∀ i, 0 < a i) (hc : FlagOrderCertificate F G σ a)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    {z : Space n} (hz : z ∈ dualLogDomain τ F G) :
    Antitone (fun i => Real.log (a i) + z (σ i)) := by
  have ho := dualFlagDomain_order_of_certificate hc hτ0 hτ1 hz
  intro i j hij
  have h := Real.log_le_log (mul_pos (ha j) (expCoordinates_pos z (σ j))) (ho hij)
  simpa only [expCoordinates, Real.log_mul (ha j).ne' (Real.exp_pos _).ne',
    Real.log_mul (ha i).ne' (Real.exp_pos _).ne', Real.log_exp] using h

/-- Actual geometric integration domain, with only finite order/scale witnesses supplied. -/
theorem dualLogDomain_subset_ordered_certificate {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P))
    {σ : Equiv.Perm (Fin n)} {a : Space n} (ha : ∀ i, 0 < a i) (hc : FlagOrderCertificate F G σ a)
    {lo hi R : ℝ} (hlo : ∀ i, lo ≤ Real.log (a i))
    (hhi : ∀ i, Real.log (a i) ≤ hi) (hR : 0 < R) :
    dualLogDomain (radius R) F G ⊆
      orderedLogTranslate (fun i => -R + lo - Real.log (a i)) σ
        (R + Real.log 2 + hi - lo) := by
  intro z hz
  have ho := dualLogDomain_order_of_certificate ha hc (radius_pos hR).le
    (radius_lt_one R).le hz
  change (∀ i, 0 ≤ z (σ i) - (-R + lo - Real.log (a i))) ∧
    (∀ i, z (σ i) - (-R + lo - Real.log (a i)) ≤ R + Real.log 2 + hi - lo) ∧
    Antitone (fun i => z (σ i) - (-R + lo - Real.log (a i)))
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hb := (dualLogDomain_radius_bounds hp hP hR F G hz (σ i)).1
    linarith [hlo i]
  · intro i
    have hb := dualFlagDomain_radius_bounds hp hP hR F G hz (σ i)
    have he : Real.exp (z (σ i)) ≤ 2 := by
      change expCoordinates z (σ i) ≤ 2
      linarith [hb.2, Real.exp_pos (-R)]
    have hl : z (σ i) ≤ Real.log 2 := (Real.le_log_iff_exp_le (by norm_num)).mpr he
    linarith [hhi i]
  · intro i j hij
    linarith [ho hij]

/-- The sharp two-factorial form is obtained from a finite certificate.
Existence of this certificate for matching actual flags remains a separate geometric theorem. -/
theorem dualFlag_integral_le_ordered_certificate {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P))
    {σ : Equiv.Perm (Fin n)} {a : Space n} (ha : ∀ i, 0 < a i) (hc : FlagOrderCertificate F G σ a)
    {lo hi R : ℝ} (hlo : ∀ i, lo ≤ Real.log (a i))
    (hhi : ∀ i, Real.log (a i) ≤ hi) (hR : 0 < R)
    (hw : 0 ≤ R + Real.log 2 + hi - lo) :
    (∫⁻ u in dualFlagDomain (radius R) F G, dualProductKernel u) ≤
      ENNReal.ofReal ((R + Real.log 2 + hi - lo) ^ n / (n.factorial : ℝ) ^ 2) := by
  rw [dualFlag_integral_eq_log_volume hp hP (radius_pos hR).le (radius_lt_one R)]
  calc
    _ ≤ ENNReal.ofReal (1 / (n.factorial : ℝ)) *
        volume (orderedLogTranslate (fun i => -R + lo - Real.log (a i)) σ
          (R + Real.log 2 + hi - lo)) :=
      mul_le_mul_right (measure_mono
        (dualLogDomain_subset_ordered_certificate hp hP F G ha hc hlo hhi hR)) _
    _ = _ := by
      rw [volume_orderedLogTranslate _ σ hw, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end
end Funk
