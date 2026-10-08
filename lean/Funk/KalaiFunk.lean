import Funk.ConvexFunk
import Funk.FlagConvention
import Funk.Radius

/-! Actual-volume / actual-flag bridges into the frozen Kalai goal.
All conversions through toReal use proved finiteness. The FVW upper bound and
the probability cover are explicit, unproved geometric inputs. -/

open Set Filter
open scoped ENNReal Topology

namespace Funk
noncomputable section

/-- A one-sided FVW envelope for the exact volume and exact frozen flag count. -/
def FVWEpsilonUpper {n : ℕ} (P : Set (Space n)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
    funkVolume P (radius R) ≤ ENNReal.ofReal
      (((Nat.card (FullFlag P) : ℝ) / (n.factorial : ℝ) ^ 2 + ε) * R ^ n)

/-- The correctly normalized leading limit, not a theorem establishing that limit. -/
def FVWLeadingLimit {n : ℕ} (P : Set (Space n)) : Prop :=
  Tendsto (fun R : ℝ => (funkVolume P (radius R)).toReal / R ^ n) atTop
    (𝓝 ((Nat.card (FullFlag P) : ℝ) / (n.factorial : ℝ) ^ 2))

theorem funkVolume_toReal_lower_iff {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) {τ a : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ENNReal.ofReal a ≤ funkVolume P τ ↔ a ≤ (funkVolume P τ).toReal :=
  ENNReal.ofReal_le_iff_le_toReal
    (funkVolume_symmetricConvexBody_finite hP hτ0 hτ1).ne

theorem fvwEpsilonUpper_iff_real_upper {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) :
    FVWEpsilonUpper P ↔ ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      (funkVolume P (radius R)).toReal ≤
        ((Nat.card (FullFlag P) : ℝ) / (n.factorial : ℝ) ^ 2 + ε) * R ^ n := by
  constructor
  · intro h ε hε
    obtain ⟨R, hR, hb⟩ := h ε hε
    refine ⟨R, hR, ?_⟩
    exact (ENNReal.le_ofReal_iff_toReal_le
      (funkVolume_symmetricConvexBody_finite hP (radius_pos hR) (radius_lt_one R)).ne
      (by positivity)).mp hb
  · intro h ε hε
    obtain ⟨R, hR, hb⟩ := h ε hε
    refine ⟨R, hR, ?_⟩
    exact (ENNReal.le_ofReal_iff_toReal_le
      (funkVolume_symmetricConvexBody_finite hP (radius_pos hR) (radius_lt_one R)).ne
      (by positivity)).mpr hb

/-- Only an upper envelope at one positive radius for each epsilon is needed. -/
theorem fvwEpsilonUpper_of_leadingLimit {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) (hlim : FVWLeadingLimit P) : FVWEpsilonUpper P := by
  apply (fvwEpsilonUpper_iff_real_upper hP).mpr
  intro ε hε
  have he : ∀ᶠ R : ℝ in atTop,
      (funkVolume P (radius R)).toReal / R ^ n <
        (Nat.card (FullFlag P) : ℝ) / (n.factorial : ℝ) ^ 2 + ε :=
    hlim.eventually_lt_const (by linarith)
  obtain ⟨R, hb, hR⟩ := (he.and (eventually_gt_atTop (0 : ℝ))).exists
  exact ⟨R, hR, ((div_lt_iff₀ (pow_pos hR n)).mp hb).le⟩

/-- This uses the actual geometric quantities, not arbitrary scalar W and N. -/
theorem kalai_fullFlag_lower_of_funk_lower_and_fvw_upper {n : ℕ}
    {P : Set (Space n)} (hP : IsSymmetricConvexBody P)
    (lower : ∀ τ : ℝ, 0 < τ → τ < 1 →
      ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) ≤ funkVolume P τ)
    (upper : FVWEpsilonUpper P) : 2 ^ n * n.factorial ≤ Nat.card (FullFlag P) := by
  apply count_bound_of_funk_lower_and_upper (W := fun τ => (funkVolume P τ).toReal)
  · intro τ hτ0 hτ1
    exact (funkVolume_toReal_lower_iff hP hτ0 hτ1).mp (lower τ hτ0 hτ1)
  · exact (fvwEpsilonUpper_iff_real_upper hP).mp upper

/-- Polytope lower bounds suffice: the general-body approximation is not needed for B. -/
theorem kalaiFullFlagsGoal_of_polytope_lower_and_fvw_upper
    (lower : ∀ (n : ℕ), 1 ≤ n → ∀ P : Set (Space n),
      IsFinitePolytope P → IsSymmetricConvexBody P → ∀ τ : ℝ, 0 < τ → τ < 1 →
        ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) ≤ funkVolume P τ)
    (upper : ∀ (n : ℕ), 1 ≤ n → ∀ P : Set (Space n),
      IsFinitePolytope P → IsSymmetricConvexBody P → FVWEpsilonUpper P) :
    KalaiFullFlagsGoal := by
  intro n hn P hp hP
  exact ⟨fullFlag_finite hp,
    kalai_fullFlag_lower_of_funk_lower_and_fvw_upper hP (lower n hn P hp hP)
      (upper n hn P hp hP)⟩

theorem kalaiFullFlagsGoal_of_funk_and_fvw_upper (funk : FunkLowerBoundGoal)
    (upper : ∀ (n : ℕ), 1 ≤ n → ∀ P : Set (Space n),
      IsFinitePolytope P → IsSymmetricConvexBody P → FVWEpsilonUpper P) :
    KalaiFullFlagsGoal := by
  apply kalaiFullFlagsGoal_of_polytope_lower_and_fvw_upper _ upper
  intro n hn P _ hP τ hτ0 hτ1
  exact (funk n hn P hP τ hτ0 hτ1).2

/-- Exactly two explicit geometric inputs now suffice for both frozen goals.
Neither the covering family nor the FVW upper envelope is proved in this file. -/
theorem funkAndKalaiGoals_of_covers_and_fvw_upper
    (cover : ∀ (n : ℕ), 1 ≤ n → ∀ (m : ℕ) (rows : Fin m → Space n),
      SignedIrredundant rows → IsSymmetricConvexBody (stripBody rows) →
      ∀ τ : ℝ, 0 < τ → τ < 1 →
        1 ≤ ∑ k ∈ canonicalBasisIndices rows, lensBoundaryRows n τ
          (basisBoundaryEvent τ k.2 (fun i => rows (k.1 i))
            (basisFeasibleRegion τ rows k.1 k.2)))
    (upper : ∀ (n : ℕ), 1 ≤ n → ∀ P : Set (Space n),
      IsFinitePolytope P → IsSymmetricConvexBody P → FVWEpsilonUpper P) :
    FunkLowerBoundGoal ∧ KalaiFullFlagsGoal := by
  have funk := funkLowerBoundGoal_of_irredundant_covers cover
  exact ⟨funk, kalaiFullFlagsGoal_of_funk_and_fvw_upper funk upper⟩

/-- Adding the unique top face does not alter the coefficient of the upper envelope. -/
theorem fvwEpsilonUpper_iff_topFlag_upper {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) :
    FVWEpsilonUpper P ↔ ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      funkVolume P (radius R) ≤ ENNReal.ofReal
        (((Nat.card (FullFlagWithTop P) : ℝ) / (n.factorial : ℝ) ^ 2 + ε) * R ^ n) := by
  rw [fullFlagWithTop_card_eq hP]
  rfl

/-- The leading-limit coefficient also survives appending the top face. -/
theorem fvwLeadingLimit_iff_topFlag_limit {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) :
    FVWLeadingLimit P ↔
      Tendsto (fun R : ℝ => (funkVolume P (radius R)).toReal / R ^ n) atTop
        (𝓝 ((Nat.card (FullFlagWithTop P) : ℝ) / (n.factorial : ℝ) ^ 2)) := by
  rw [fullFlagWithTop_card_eq hP]
  rfl

/-- A fully proved calibration of the actual epsilon upper envelope in dimension one. -/
theorem unit_interval_fvwEpsilonUpper : FVWEpsilonUpper (coordinateInterval (-1) 1) := by
  intro ε hε
  let R : ℝ := 2 * Real.log 2 / ε + 1
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨R, hR, ?_⟩
  rw [funkVolume_unit_interval (radius_pos hR) (radius_lt_one R), four_artanh_radius hR,
    fullFlag_interval_card (by norm_num : (-1 : ℝ) < 1)]
  apply ENNReal.ofReal_le_ofReal
  have he : 1 < Real.exp R := Real.one_lt_exp_iff.mpr hR
  have hb : Real.log (2 * Real.exp R - 1) ≤ Real.log 2 + R := by
    have hl := Real.log_le_log (by linarith : 0 < 2 * Real.exp R - 1)
      (by linarith : 2 * Real.exp R - 1 ≤ 2 * Real.exp R)
    simpa only [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero R),
      Real.log_exp] using hl
  have hc : 2 * Real.log 2 ≤ ε * R := by
    dsimp [R]
    have heq : ε * (2 * Real.log 2 / ε) = 2 * Real.log 2 := by field_simp
    nlinarith
  norm_num only [Nat.factorial, Nat.cast_one, Nat.cast_ofNat, one_pow, div_one, pow_one]
  nlinarith

end
end Funk
