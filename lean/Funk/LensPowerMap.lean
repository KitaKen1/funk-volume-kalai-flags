import Funk.LensComplexRows

/-! The actual holomorphic power map for the remaining mass argument.
These are concrete source objects, not an assumed mass or probability inequality.
The domain, zero and analyticity hypotheses are proved in complex Euclidean space. -/

open Set Metric
open scoped BigOperators

namespace Funk
noncomputable section

theorem tiltedLensInverse_zero {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    tiltedLensInverse τ 0 = 0 := by
  simpa only [tiltedLens_zero] using tiltedLensInverse_left hτ0 hτ1
    (show (0 : ℂ) ∈ ball 0 1 by simp)

theorem tiltedLensInverse_eq_zero_iff {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {w : ℂ} (hw : w ∈ interior (lensGraphBody τ)) :
    tiltedLensInverse τ w = 0 ↔ w = 0 := by
  constructor
  · intro hz
    have h := tiltedLensInverse_right hτ0 hτ1 hw
    rw [hz, tiltedLens_zero] at h
    exact h.symm
  · rintro rfl
    exact tiltedLensInverse_zero hτ0 hτ1

/-- One actual inverse-coordinate power; this is f_{k,j} in the mass argument. -/
def lensPowerComponent {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n) (k : ℕ) (j : Fin m)
    (z : LensComplexSpace n) : ℂ := (tiltedLensInverse τ (lensComplexRow (rows j) z)) ^ k

/-- Assemble the components with the Euclidean norm convention of the upstream. -/
def lensPowerMap {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n) (k : ℕ)
    (z : LensComplexSpace n) : LensComplexSpace m :=
  WithLp.toLp 2 (fun j => lensPowerComponent τ rows k j z)

/-- The literal squared Euclidean norm of the power vector. -/
def lensPowerEnergy {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n) (k : ℕ)
    (z : LensComplexSpace n) : ℝ := ∑ j : Fin m, ‖lensPowerComponent τ rows k j z‖ ^ 2

theorem lensPowerComponent_zero {n m : ℕ} {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (rows : Fin m → Space n) {k : ℕ} (hk : 0 < k) (j : Fin m) :
    lensPowerComponent τ rows k j 0 = 0 := by
  simp [lensPowerComponent, tiltedLensInverse_zero hτ0 hτ1, hk.ne']

theorem lensPowerComponent_eq_zero_iff {n m : ℕ} {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (rows : Fin m → Space n) {k : ℕ} (hk : 0 < k) (j : Fin m)
    {z : LensComplexSpace n} (hz : z ∈ lensComplexDomain τ rows) :
    lensPowerComponent τ rows k j z = 0 ↔ lensComplexRow (rows j) z = 0 := by
  unfold lensPowerComponent
  rw [pow_eq_zero_iff hk.ne', tiltedLensInverse_eq_zero_iff hτ0 hτ1 (hz j)]

/-- The actual powered row map has exactly one common zero in its actual domain. -/
theorem lensPowerComponents_eq_zero_iff {n m : ℕ} {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (rows : Fin m → Space n) (hK : IsCompact (stripBody rows)) {k : ℕ} (hk : 0 < k)
    {z : LensComplexSpace n} (hz : z ∈ lensComplexDomain τ rows) :
    (∀ j, lensPowerComponent τ rows k j z = 0) ↔ z = 0 := by
  simp_rw [lensPowerComponent_eq_zero_iff hτ0 hτ1 rows hk _ hz]
  exact lensComplexRows_eq_zero_iff rows hK z

theorem lensPowerComponent_analyticOnNhd {n m : ℕ} {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (rows : Fin m → Space n) (k : ℕ) (j : Fin m) :
    AnalyticOnNhd ℂ (lensPowerComponent τ rows k j) (lensComplexDomain τ rows) := by
  intro z hz
  exact (((tiltedLensInverse_analyticOnNhd hτ0 hτ1) _ (hz j)).comp
    ((lensComplexRow (rows j)).analyticAt z)).pow k

theorem lensPowerComponent_differentiableOn {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ) (j : Fin m) :
    DifferentiableOn ℂ (lensPowerComponent τ rows k j) (lensComplexDomain τ rows) :=
  (lensPowerComponent_analyticOnNhd hτ0 hτ1 rows k j).differentiableOn

theorem lensPowerMap_differentiableOn {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ) :
    DifferentiableOn ℂ (lensPowerMap τ rows k) (lensComplexDomain τ rows) := by
  exact (EuclideanSpace.equiv (Fin m) ℂ).symm.toContinuousLinearMap.differentiable.comp_differentiableOn
    (differentiableOn_pi.mpr (lensPowerComponent_differentiableOn hτ0 hτ1 rows k))

theorem lensPowerEnergy_nonneg {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n) (k : ℕ)
    (z : LensComplexSpace n) : 0 ≤ lensPowerEnergy τ rows k z := by
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem lensPowerEnergy_continuousOn {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ) :
    ContinuousOn (lensPowerEnergy τ rows k) (lensComplexDomain τ rows) := by
  apply continuousOn_finsetSum
  intro j _
  exact ((lensPowerComponent_differentiableOn hτ0 hτ1 rows k j).continuousOn.norm).pow 2

/-- A strict sublevel below one forces every inverse row coordinate inside the disk. -/
theorem lensPowerEnergy_component_lt_one {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n)
    {k : ℕ} {z : LensComplexSpace n} {R : ℝ}
    (hR : R < 1) (hz : lensPowerEnergy τ rows k z < R) (j : Fin m) :
    ‖tiltedLensInverse τ (lensComplexRow (rows j) z)‖ < 1 := by
  have he : ‖lensPowerComponent τ rows k j z‖ ^ 2 ≤ lensPowerEnergy τ rows k z := by
    unfold lensPowerEnergy
    exact Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) =>
      sq_nonneg ‖lensPowerComponent τ rows k l z‖) (Finset.mem_univ j)
  have hp : ‖tiltedLensInverse τ (lensComplexRow (rows j) z)‖ ^ (2 * k) < 1 := by
    simpa only [lensPowerComponent, norm_pow, ← pow_mul, mul_comm k 2] using he.trans_lt (hz.trans hR)
  by_contra hn
  have hu : 1 ≤ ‖tiltedLensInverse τ (lensComplexRow (rows j) z)‖ ^ (2 * k) :=
    one_le_pow₀ (show 1 ≤ ‖tiltedLensInverse τ (lensComplexRow (rows j) z)‖ from le_of_not_gt hn)
  exact (not_lt_of_ge hu) hp

end
end Funk
