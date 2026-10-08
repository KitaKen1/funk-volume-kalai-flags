import Funk.Targets
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.DiscreteSubset

/-! Regular zeros on real lines are isolated, countable and Lebesgue null.
No analyticity, continuity of the derivative, or measurability of the zero set
is required for this one-dimensional assertion. -/

open Set Filter MeasureTheory
open scoped Topology

namespace Funk
noncomputable section

theorem countable_of_regular_zeros (f : ℝ → ℝ) (s : Set ℝ)
    (hz : ∀ x ∈ s, f x = 0)
    (hd : ∀ x ∈ s, ∃ d : ℝ, HasDerivAt f d x ∧ d ≠ 0) : s.Countable := by
  have hs : IsDiscrete s := by
    apply isDiscrete_iff_nhdsNE.mpr
    intro x hx
    obtain ⟨d, hd, hne⟩ := hd x hx
    rw [inf_principal_eq_bot]
    filter_upwards [hd.eventually_ne (c := 0) hne] with y hy
    exact fun hys => hy (hz y hys)
  exact (HereditarilyLindelofSpace.isLindelof s).countable_of_isDiscrete hs

theorem volume_regular_zeros_eq_zero (f : ℝ → ℝ) (s : Set ℝ)
    (hz : ∀ x ∈ s, f x = 0)
    (hd : ∀ x ∈ s, ∃ d : ℝ, HasDerivAt f d x ∧ d ≠ 0) : volume s = 0 :=
  (countable_of_regular_zeros f s hz hd).measure_zero volume

end
end Funk
