import SolutionFC

-- Independently spell out the requested type, including answer=True,
-- finiteness, quantifiers and the numeric bound.
example : True ↔
    ∀ (n : ℕ), 1 ≤ n → ∀ (P : Set (Fin n → ℝ)),
      Funk.FormalConjectures.IsFinitePolytope P →
      Funk.FormalConjectures.IsSymmetricConvexBody P →
        Finite (Funk.FormalConjectures.FullFlag P) ∧
          2 ^ n * n.factorial ≤ Nat.card (Funk.FormalConjectures.FullFlag P) :=
  Funk.FormalConjectures.kalaiFullFlags

#check Funk.FormalConjectures.kalaiFullFlags
#print axioms Funk.FormalConjectures.kalaiFullFlags
