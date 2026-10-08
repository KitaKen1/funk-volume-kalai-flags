/-
Copyright 2026 Kenta Kitamura (KitaKen1).
-/
module

public import Mathlib
public import FormalConjecturesUtil.Answer
public meta import FormalConjecturesUtil.Attributes.Basic

/-!
# Kalai's full flag conjecture

Kalai conjectured that every centrally symmetric n-dimensional convex polytope
has at least 2^n n! complete flags [SZ08, p. 21]. A complete flag is a nested
chain of nonempty proper faces of dimensions 0, ..., n-1; appending the whole
polytope gives the equivalent convention that includes the top face.

The answer is affirmative [Ki26]. The proof first establishes the numerical
lower bound in the symmetric Funk-volume conjecture of [FVW23], then compares
volume growth with the number of complete flags.

*References:*
- [SZ08] M. Schmitt and G. M. Ziegler, *Ten Problems in Geometry* (2008), p. 21,
  https://www.mi.fu-berlin.de/math/groups/discgeom/ziegler/Preprintfiles/127PREPRINT.pdf.
- [FVW23] D. Faifman, C. Vernicos and C. Walsh,
  *Volume growth of Funk geometry and the flags of polytopes*,
  https://arxiv.org/abs/2306.09268.
- [Ki26] Kenta Kitamura, *Kalai's full flag conjecture in Lean 4* (2026),
  https://github.com/KitaKen1/funk-volume-kalai-flags.
-/

@[expose] public section

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

/-- Kalai's full flag conjecture [SZ08, p. 21]: does every centrally symmetric
n-dimensional convex polytope have at least 2^n n! complete flags?
The answer is affirmative [Ki26]. -/
@[category research solved, AMS 52,
    formal_proof using lean4 at "https://github.com/KitaKen1/funk-volume-kalai-flags/blob/main/lean/FinalTheorems.lean"]
theorem kalaiFullFlags :
    answer(True) ↔
      ∀ (n : ℕ), 1 ≤ n → ∀ (P : Set (Fin n → ℝ)),
        IsFinitePolytope P → IsSymmetricConvexBody P →
          Finite (FullFlag P) ∧
            2 ^ n * n.factorial ≤ Nat.card (FullFlag P) := by
  sorry

end Funk.FormalConjectures
