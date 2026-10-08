import Funk.MainTheorems
import Funk.HalfspaceFaceConvention

/-! Explicit geometric statements for target review and external export.
The polar incidence is a closed relation between genuine primal/dual points.
The product integral uses product Lebesgue measure, without dividing by the
Euclidean unit-ball volume. This module does not certify an independent
human mathematical review or the complete Lean-Eval sandbox pipeline. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

/-- The literal translated-polar relation, expressed without an integral kernel. -/
def polarIncidence {n : ℕ} (K : Set (Space n)) : Set (Space n × Space n) :=
  {p | ∀ z ∈ K, dotProduct p.2 (z - p.1) ≤ 1}

theorem mem_polarIncidence {n : ℕ} (K : Set (Space n)) (x y : Space n) :
    (x, y) ∈ polarIncidence K ↔ y ∈ coordinatePolar (translate K x) := by
  constructor
  · intro h _ hv
    rcases hv with ⟨z, hz, rfl⟩
    exact h z hz
  · intro h z hz
    exact h _ ⟨z, hz, rfl⟩

/-- No compactness premise is needed: every defining pairing inequality is closed. -/
theorem isClosed_polarIncidence {n : ℕ} (K : Set (Space n)) :
    IsClosed (polarIncidence K) := by
  simp only [polarIncidence, ofPred_forall]
  apply isClosed_iInter
  intro z
  apply isClosed_iInter
  intro _
  have hc : Continuous (fun p : Space n × Space n => dotProduct p.2 (z - p.1)) := by
    unfold dotProduct
    fun_prop
  exact isClosed_le hc continuous_const

theorem isClosed_translated_coordinatePolar {n : ℕ} (K : Set (Space n)) (x : Space n) :
    IsClosed (coordinatePolar (translate K x)) := by
  have h := (isClosed_polarIncidence K).preimage
    (show Continuous (fun y : Space n => (x, y)) from continuous_const.prodMk continuous_id)
  convert h using 1
  ext y
  exact (mem_polarIncidence K x y).symm

theorem polarIncidence_indicator_section {n : ℕ} (K : Set (Space n)) (x : Space n) :
    (fun y : Space n => (polarIncidence K).indicator (fun _ => (1 : ℝ≥0∞)) (x, y)) =
      (coordinatePolar (translate K x)).indicator (fun _ => 1) := by
  classical
  funext y
  simp only [indicator_apply, mem_polarIncidence]

/-- The actual polar-volume kernel is Borel measurable, not an arbitrary scalar function. -/
theorem measurable_polarVolume_kernel {n : ℕ} (K : Set (Space n)) :
    Measurable (fun x : Space n => volume (coordinatePolar (translate K x))) := by
  have h : Measurable ((polarIncidence K).indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator (isClosed_polarIncidence K).measurableSet
  have hi : (fun x : Space n => ∫⁻ y : Space n,
      (polarIncidence K).indicator (fun _ => (1 : ℝ≥0∞)) (x, y)) =
      (fun x : Space n => volume (coordinatePolar (translate K x))) := by
    funext x
    rw [polarIncidence_indicator_section]
    simpa only [Pi.one_apply] using lintegral_indicator_fun_one
      (isClosed_translated_coordinatePolar K x).measurableSet
  rw [← hi]
  exact h.lintegral_prod_right'

/-- Unnormalized Holmes--Thompson volume as the literal primal/dual product integral. -/
theorem funkVolume_eq_polarIncidence_integral {n : ℕ} (K : Set (Space n)) (τ : ℝ) :
    funkVolume K τ = ∫⁻ p : Space n × Space n,
      (polarIncidence K).indicator (fun _ => (1 : ℝ≥0∞)) p
      ∂((volume.restrict ((fun y : Space n => τ • y) '' K)).prod volume) := by
  have h : Measurable ((polarIncidence K).indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator (isClosed_polarIncidence K).measurableSet
  rw [lintegral_prod _ h.aemeasurable]
  unfold funkVolume
  congr 1
  funext x
  rw [polarIncidence_indicator_section]
  simpa only [Pi.one_apply] using (lintegral_indicator_fun_one
    (isClosed_translated_coordinatePolar K x).measurableSet).symm

/-- The full Funk conclusion with literal hypotheses and the actual polar integral. -/
theorem symmetricFunk_explicit {n : ℕ} (hn : 1 ≤ n) (K : Set (Space n))
    (hc : IsCompact K) (hv : Convex ℝ K) (hs : ∀ x ∈ K, -x ∈ K)
    (hi : 0 ∈ interior K) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    (∫⁻ x in ((fun y : Space n => τ • y) '' K),
      volume {y : Space n | ∀ z ∈ K, dotProduct y (z - x) ≤ 1}) < ⊤ ∧
    ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) ≤
      ∫⁻ x in ((fun y : Space n => τ • y) '' K),
        volume {y : Space n | ∀ z ∈ K, dotProduct y (z - x) ≤ 1} := by
  have he (x : Space n) : coordinatePolar (translate K x) =
      {y : Space n | ∀ z ∈ K, dotProduct y (z - x) ≤ 1} := by
    ext y
    exact (mem_polarIncidence K x y).symm
  have h := symmetricFunk_lower_bound n hn K ⟨hc, hv, hs, hi⟩ τ hτ0 hτ1
  simpa only [funkVolume, he] using h

/-- The metric-radius convention R>0, with the correct factor 2^n/n!. -/
theorem symmetricFunk_metric_radius {n : ℕ} (hn : 1 ≤ n) (K : Set (Space n))
    (hK : IsSymmetricConvexBody K) {R : ℝ} (hR : 0 < R) :
    funkVolume K (1 - Real.exp (-R)) < ⊤ ∧
    ENNReal.ofReal (((2 : ℝ) ^ n / (n.factorial : ℝ)) *
      (Real.log (2 * Real.exp R - 1)) ^ n) ≤ funkVolume K (1 - Real.exp (-R)) := by
  have h := symmetricFunk_lower_bound n hn K hK (radius R) (radius_pos hR) (radius_lt_one R)
  refine ⟨h.1, ?_⟩
  calc
    _ = ENNReal.ofReal ((4 * Real.artanh (radius R)) ^ n / (n.factorial : ℝ)) := by
      congr 1
      rw [four_artanh_radius hR, mul_pow]
      ring
    _ ≤ _ := h.2

/-- Kalai's count in the literal closed-halfspace convention, including the top face. -/
theorem kalai_halfspace_full_flags {n : ℕ} (hn : 1 ≤ n) (P : Set (Space n))
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P) :
    Finite (HalfspaceFullFlag P) ∧
      2 ^ n * n.factorial ≤ Nat.card (HalfspaceFullFlag P) := by
  exact ⟨halfspaceFullFlag_finite hp hP,
    by rw [halfspaceFullFlag_card_eq hp hP]; exact (kalai_full_flags n hn P hp hP).2⟩

end
end Funk
