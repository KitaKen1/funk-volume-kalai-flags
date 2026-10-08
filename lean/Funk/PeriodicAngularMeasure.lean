import Funk.UnsignedBoundaryCover
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Full-period transport for the literal normalized lens angular measure.
No equality of the distinct real-line measures is asserted: their pushforwards
through periodic observables agree. Open polar endpoints are removed by the
null-singleton theorem. -/

open Set MeasureTheory Function
open scoped BigOperators ENNReal

namespace Funk
noncomputable section

/-- Lower integrals of arbitrary periodic functions agree on all full periods. -/
theorem lintegral_periodic_full_period {T : ℝ} (hT : 0 < T) {f : ℝ → ℝ≥0∞}
    (hf : Periodic f T) (a b : ℝ) :
    (∫⁻ x in Ioc a (a+T), f x) = ∫⁻ x in Ioc b (b+T), f x := by
  let : Fact (0 < T) := ⟨hT⟩
  have ha := AddCircle.lintegral_preimage T a hf.lift
  have hb := AddCircle.lintegral_preimage T b hf.lift
  simp only [Periodic.lift_coe] at ha hb
  exact ha.trans hb.symm

/-- Normalized law on the standard open polar interval. -/
def lensStandardAngular : Measure ℝ :=
  ENNReal.ofReal (1/(2*Real.pi)) • volume.restrict (Ioo (-Real.pi) Real.pi)

/-- The two different angular intervals give exactly the same periodic lower integral. -/
theorem lintegral_lensStandardAngular_eq_lensAngular {f : ℝ → ℝ≥0∞}
    (hf : Periodic f (2*Real.pi)) :
    (∫⁻ θ, f θ ∂lensStandardAngular) = ∫⁻ θ, f θ ∂lensAngular := by
  rw [lensStandardAngular, lensAngular, lintegral_smul_measure, lintegral_smul_measure,
    restrict_Ioo_eq_restrict_Ioc]
  congr 1
  have ha : -Real.pi + 2*Real.pi = Real.pi := by ring
  have hb : -Real.pi/2 + 2*Real.pi = 3*Real.pi/2 := by ring
  simpa only [ha, hb] using
    lintegral_periodic_full_period Real.two_pi_pos hf (-Real.pi) (-Real.pi/2)

theorem lensStandardAngular_univ : lensStandardAngular univ = 1 := by
  have h := lintegral_lensStandardAngular_eq_lensAngular (f := fun _ => 1) (fun _ => rfl)
  simpa using h

instance lensStandardAngular_isProbabilityMeasure : IsProbabilityMeasure lensStandardAngular :=
  ⟨lensStandardAngular_univ⟩

/-- Pushforward equality for every measurable periodic observable. -/
theorem lensStandardAngular_map_eq_lensAngular {E : Type*} [MeasurableSpace E]
    {f : ℝ → E} (hf : Measurable f) (hp : Periodic f (2*Real.pi)) :
    lensStandardAngular.map f = lensAngular.map f := by
  ext s hs
  rw [Measure.map_apply hf hs, Measure.map_apply hf hs]
  have h := lintegral_lensStandardAngular_eq_lensAngular
    (f := fun θ => s.indicator (fun _ => (1 : ℝ≥0∞)) (f θ))
    (fun θ => by dsimp only; rw [hp θ])
  have he : (fun θ => s.indicator (fun _ => (1 : ℝ≥0∞)) (f θ)) =
      (f ⁻¹' s).indicator (fun _ => 1) := by
    funext θ
    by_cases hm : f θ ∈ s <;> simp [Set.indicator, hm]
  rw [he, lintegral_indicator_const (hf hs), lintegral_indicator_const (hf hs)] at h
  simpa only [one_mul] using h

theorem lensStandardAngular_map_circleMap (r : ℝ) :
    lensStandardAngular.map (circleMap 0 r) =
      lensAngular.map (circleMap 0 r) :=
  lensStandardAngular_map_eq_lensAngular (by fun_prop) (periodic_circleMap 0 r)

/-- Product of normalized standard angular laws. -/
def lensStandardAngularRows (n : ℕ) : Measure (Space n) :=
  Measure.pi (fun _ => lensStandardAngular)

theorem lensStandardAngularRows_isProbability (n : ℕ) :
    IsProbabilityMeasure (lensStandardAngularRows n) := by
  unfold lensStandardAngularRows
  infer_instance

/-- Independent periodic observables agree under the literal old and new angular laws. -/
theorem lensStandardAngularRows_map_eq_lensAngularRows {n : ℕ} {E : Type*}
    [MeasurableSpace E] {f : Fin n → ℝ → E}
    (hf : ∀ i, Measurable (f i)) (hp : ∀ i, Periodic (f i) (2*Real.pi)) :
    (lensStandardAngularRows n).map (fun θ i => f i (θ i)) =
      (lensAngularRows n).map (fun θ i => f i (θ i)) := by
  rw [lensStandardAngularRows, lensAngularRows, Measure.pi_map_pi (fun i => (hf i).aemeasurable),
    Measure.pi_map_pi (fun i => (hf i).aemeasurable)]
  congr 1
  funext i
  exact lensStandardAngular_map_eq_lensAngular (hf i) (hp i)

/-- Measurable observations of any fixed radial circle vector have identical laws. -/
theorem lintegral_lensStandardAngularRows_circleMap {n : ℕ} (r : Space n)
    {g : (Fin n → ℂ) → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ θ, g (fun i => circleMap 0 (r i) (θ i)) ∂lensStandardAngularRows n) =
      ∫⁻ θ, g (fun i => circleMap 0 (r i) (θ i)) ∂lensAngularRows n := by
  have hm : Measurable (fun θ : Space n => fun i => circleMap 0 (r i) (θ i)) :=
    Measurable.of_eval (fun i => (by fun_prop : Measurable (circleMap 0 (r i))).comp
      (measurable_pi_apply i))
  rw [← lintegral_map hg hm, ← lintegral_map hg hm,
    lensStandardAngularRows_map_eq_lensAngularRows
      (fun i => by fun_prop) (fun i => periodic_circleMap 0 (r i))]

end
end Funk
