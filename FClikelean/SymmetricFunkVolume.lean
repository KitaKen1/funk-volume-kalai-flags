/-
Copyright 2026 Kenta Kitamura (KitaKen1).
-/
module

public import Mathlib
public import FormalConjecturesUtil.Answer
public meta import FormalConjecturesUtil.Attributes.Basic

/-!
# Symmetric Funk-volume lower bound

For an origin-symmetric convex body K in ℝⁿ and 0 < τ < 1, the unnormalized
Holmes–Thompson Funk volume of τK is at least (4 artanh τ)ⁿ / n! [FVW23].
This is the numerical inequality in Conjecture 1.1, without the Hanner-volume
equality or equality-case classification. The answer is affirmative [Ki26].

*References:*
- [FVW23] D. Faifman, C. Vernicos and C. Walsh,
  *Volume growth of Funk geometry and the flags of polytopes*,
  https://arxiv.org/abs/2306.09268.
- [Ki26] Kenta Kitamura, *Kalai's full flag conjecture in Lean 4* (2026),
  https://github.com/KitaKen1/funk-volume-kalai-flags.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FunkVolume

/-- A compact convex body, symmetric about the origin, with nonempty interior. -/
def IsSymmetricConvexBody {n : ℕ} (K : Set (Fin n → ℝ)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (∀ x ∈ K, -x ∈ K) ∧ 0 ∈ interior K

/-- The polar body with respect to the ordinary coordinate pairing. -/
def coordinatePolar {n : ℕ} (K : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {y | ∀ x ∈ K, dotProduct y x ≤ 1}

/-- The translated body K - x. -/
def translate {n : ℕ} (K : Set (Fin n → ℝ)) (x : Fin n → ℝ) : Set (Fin n → ℝ) :=
  (fun z => z - x) '' K

/-- Unnormalized Holmes–Thompson Funk volume, using product Lebesgue measure. -/
noncomputable def funkVolume {n : ℕ} (K : Set (Fin n → ℝ)) (τ : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in ((fun y => τ • y) '' K), volume (coordinatePolar (translate K x))

/-- The numerical lower bound in the symmetric Funk-volume conjecture
[FVW23, Conjecture 1.1], together with finiteness. The answer is affirmative [Ki26]. -/
@[category research solved, AMS 52,
    formal_proof using lean4 at "https://github.com/KitaKen1/funk-volume-kalai-flags/blob/main/lean/FinalTheorems.lean"]
theorem symmetricFunkVolume :
    answer(True) ↔
      ∀ (n : ℕ), 1 ≤ n → ∀ (K : Set (Fin n → ℝ)),
        IsSymmetricConvexBody K → ∀ τ : ℝ, 0 < τ → τ < 1 →
          funkVolume K τ < ⊤ ∧
            ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) ≤
              funkVolume K τ := by
  sorry

end FunkVolume
