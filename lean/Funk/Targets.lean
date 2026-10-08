import Funk.Polar
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! Specifications only. `FunkLowerBoundGoal` and `KalaiFullFlagsGoal` are
propositions to be proved, not proved theorems. Geometry is not replaced by free
volume or flag-count parameters. All volumes below are product Lebesgue measure.
-/

open MeasureTheory
open scoped ENNReal

namespace Funk

noncomputable section

def IsSymmetricConvexBody {n : ℕ} (K : Set (Space n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (∀ x ∈ K, -x ∈ K) ∧ 0 ∈ interior K

def IsFinitePolytope {n : ℕ} (P : Set (Space n)) : Prop :=
  ∃ vertices : Finset (Space n), P = convexHull ℝ (vertices : Set (Space n))

/-- The `n` proper faces have dimensions `0,…,n-1`; append `P` for the convention
that includes the full polytope. Nonemptiness excludes the empty face. -/
structure FullFlag {n : ℕ} (P : Set (Space n)) where
  faces : Fin n → Set (Space n)
  nonempty : ∀ i, (faces i).Nonempty
  convex : ∀ i, Convex ℝ (faces i)
  extreme : ∀ i, IsExtreme ℝ P (faces i)
  proper : ∀ i, faces i ⊂ P
  dimension : ∀ i, Module.finrank ℝ (affineSpan ℝ (faces i)).direction = i.val
  chain : StrictMono faces

/-- No `toReal` is used: an infinite quantity cannot silently become zero. -/
def funkVolume {n : ℕ} (K : Set (Space n)) (τ : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in ((fun y => τ • y) '' K), volume (coordinatePolar (translate K x))

/-- Target A includes finiteness as well as the lower bound. UNPROVED. -/
def FunkLowerBoundGoal : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (K : Set (Space n)), IsSymmetricConvexBody K →
    ∀ τ : ℝ, 0 < τ → τ < 1 →
      funkVolume K τ < ⊤ ∧
      ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) ≤ funkVolume K τ

/-- Target B counts actual face chains. Finiteness remains a proof obligation,
so `Nat.card` on an infinite type is never accepted as an enumeration. UNPROVED. -/
def KalaiFullFlagsGoal : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (P : Set (Space n)),
    IsFinitePolytope P → IsSymmetricConvexBody P →
      Finite (FullFlag P) ∧ 2 ^ n * n.factorial ≤ Nat.card (FullFlag P)

end
end Funk
