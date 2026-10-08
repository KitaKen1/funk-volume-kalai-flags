import Funk.PeriodicAngularMeasure

/-! The standard polar angular probability samples exactly the existing actual
closed-boundary interpolation event. The lensRadialTrace itself is periodic,
so the real-line interval mismatch is resolved at the actual pushforward. -/

open Set MeasureTheory Function
open scoped BigOperators ENNReal

namespace Funk
noncomputable section

theorem lensRadialTrace_periodic (τ r : ℝ) :
    Periodic (lensRadialTrace τ r) (2*Real.pi) := by
  intro θ
  unfold lensRadialTrace
  rw [periodic_circleMap 0 r θ]

/-- Both angular presentations sample the same actual lens boundary measure. -/
theorem lensStandardAngularRows_map_trace (n : ℕ) (τ : ℝ) :
    (lensStandardAngularRows n).map (lensBoundaryTraceRows n τ) = lensBoundaryRows n τ := by
  rw [← lensAngularRows_map_trace n τ]
  exact lensStandardAngularRows_map_eq_lensAngularRows
    (fun _ => (lensBoundary_continuous τ).measurable) (fun _ => lensRadialTrace_periodic τ 1)

theorem boundaryInterpolation_probability_eq_standard_angular {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (s : Fin n → Fin m) :
    lensBoundaryRows n τ (boundaryInterpolationEvent τ rows s) =
      lensStandardAngularRows n
        ((lensBoundaryTraceRows n τ) ⁻¹' boundaryInterpolationEvent τ rows s) := by
  rw [← lensStandardAngularRows_map_trace n τ, Measure.map_apply
    (measurable_lensBoundaryTraceRows n τ)
    (isClosed_boundaryInterpolationEvent hτ0 hτ1 rows s).measurableSet]

end
end Funk
