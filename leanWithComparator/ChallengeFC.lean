-- Generated from the pinned PR snapshot. Mathematical body is verbatim.
import Mathlib
import FormalConjecturesUtil.Answer
import FormalConjecturesUtil.Attributes.Basic

-- Match the proof's instance path; checked against RawPRFC by ModelAuditFC.
attribute [-instance] CompletePartialOrder.toPartialOrder

namespace Funk.FormalConjectures

/-- A compact convex body, symmetric about the origin, with nonempty interior. -/
def IsSymmetricConvexBody {n : ℕ} (K : Set (Fin n → ℝ)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (∀ x ∈ K, -x ∈ K) ∧ 0 ∈ interior K

/-- A polytope is the convex hull of finitely many points. -/
def IsFinitePolytope {n : ℕ} (P : Set (Fin n → ℝ)) : Prop :=
  ∃ vertices : Finset (Fin n → ℝ), P = convexHull ℝ (vertices : Set (Fin n → ℝ))

/-- A complete flag consists of one nonempty proper face in each dimension,
ordered by strict inclusion. Nonemptiness excludes the empty face. -/
structure FullFlag {n : ℕ} (P : Set (Fin n → ℝ)) where
  faces : Fin n → Set (Fin n → ℝ)
  nonempty : ∀ i, (faces i).Nonempty
  convex : ∀ i, Convex ℝ (faces i)
  extreme : ∀ i, IsExtreme ℝ P (faces i)
  proper : ∀ i, faces i ⊂ P
  dimension : ∀ i, Module.finrank ℝ (affineSpan ℝ (faces i)).direction = i.val
  chain : StrictMono faces

/-- Kalai's full flag conjecture [FVW23, Section 1]: does every centrally symmetric
$n$-dimensional convex polytope have at least $2^n n!$ complete flags?
The answer is affirmative [Ki26]. -/
@[category research solved, AMS 52,
    formal_proof using lean4 at "https://github.com/KitaKen1/funk-volume-kalai-flags/blob/5b92194f6b5ed49f380a6412b120ad256d850740/lean/FinalTheorems.lean#L90-L106"]
theorem kalaiFullFlags :
    answer(True) ↔
      ∀ (n : ℕ), 1 ≤ n → ∀ (P : Set (Fin n → ℝ)),
        IsFinitePolytope P → IsSymmetricConvexBody P →
          Finite (FullFlag P) ∧
            2 ^ n * n.factorial ≤ Nat.card (FullFlag P) := by
  sorry

end Funk.FormalConjectures
