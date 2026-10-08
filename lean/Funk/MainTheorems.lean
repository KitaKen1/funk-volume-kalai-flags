import Funk.LensPoweredReverseFatou

/-! Completed proofs of the unchanged target specifications. The local Lean
proofs do not certify the separate semantic review or independent replay. -/

namespace Funk

/-- Both literal frozen specifications, with no supplied cover premise. -/
theorem symmetricFunk_and_kalai_full_flags : FunkLowerBoundGoal ∧ KalaiFullFlagsGoal := by
  apply funkAndKalaiGoals_of_angular_interpolation_covers
  intro n hn m rows _hir hK τ hτ0 hτ1
  exact lensBoundary_angular_interpolation_cover hn hτ0 hτ1 rows hK.1

/-- Finiteness and sharp lower bound for every symmetric convex body in every positive dimension. -/
theorem symmetricFunk_lower_bound : FunkLowerBoundGoal :=
  symmetricFunk_and_kalai_full_flags.1

/-- Finiteness and the sharp lower bound for actual complete face flags. -/
theorem kalai_full_flags : KalaiFullFlagsGoal :=
  symmetricFunk_and_kalai_full_flags.2

end Funk
