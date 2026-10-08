import Funk.LensPowerMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Compact sublevel closures of the actual tilted-lens power map.
A sublevel forces every inverse row coordinate into a common smaller closed disk.
Its actual F-image is compact inside the open lens. The injective finite row map
is proper, so the closure is compact and stays inside the actual open domain.
No boundary extension of the inverse and no mass inequality is assumed. -/

open Set Metric
open scoped BigOperators

namespace Funk
noncomputable section

/-- The common inverse-coordinate cutoff for the literal squared power energy. -/
def lensSublevelRadius (R : ℝ) (k : ℕ) : ℝ := R ^ (((2 * k : ℕ) : ℝ)⁻¹)

theorem lensSublevelRadius_pos {R : ℝ} (hR : 0 < R) (k : ℕ) :
    0 < lensSublevelRadius R k := Real.rpow_pos_of_pos hR _

theorem lensSublevelRadius_lt_one {R : ℝ} (hR : 0 < R) (hR1 : R < 1)
    {k : ℕ} (hk : 0 < k) : lensSublevelRadius R k < 1 := by
  apply Real.rpow_lt_one hR.le hR1
  positivity

theorem lensSublevelRadius_pow {R : ℝ} (hR : 0 ≤ R) {k : ℕ} (hk : 0 < k) :
    lensSublevelRadius R k ^ (2 * k) = R :=
  Real.rpow_inv_natCast_pow hR (by omega)

/-- The exact sublevel gives a uniform cutoff strictly smaller than one. -/
theorem lensPowerEnergy_component_lt_radius {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n)
    {k : ℕ} (hk : 0 < k) {R : ℝ} (hR : 0 < R) {z : LensComplexSpace n}
    (hz : lensPowerEnergy τ rows k z < R) (j : Fin m) :
    ‖tiltedLensInverse τ (lensComplexRow (rows j) z)‖ < lensSublevelRadius R k := by
  have he : ‖lensPowerComponent τ rows k j z‖ ^ 2 ≤ lensPowerEnergy τ rows k z := by
    unfold lensPowerEnergy
    exact Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) =>
      sq_nonneg ‖lensPowerComponent τ rows k l z‖) (Finset.mem_univ j)
  have hp : ‖tiltedLensInverse τ (lensComplexRow (rows j) z)‖ ^ (2 * k) <
      lensSublevelRadius R k ^ (2 * k) := by
    rw [lensSublevelRadius_pow hR.le hk]
    simpa only [lensPowerComponent, norm_pow, ← pow_mul, mul_comm k 2] using he.trans_lt hz
  exact lt_of_pow_lt_pow_left₀ _ (lensSublevelRadius_pos hR k).le hp

/-- Simultaneous row membership in the image of a fixed smaller closed disk. -/
def lensInnerRowDomain {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n) (r : ℝ) :
    Set (LensComplexSpace n) :=
  {z | ∀ j, lensComplexRow (rows j) z ∈ tiltedLens τ '' closedBall 0 r}

theorem isCompact_lens_inner_image (τ : ℝ) {r : ℝ} (hr : r ≤ 1) :
    IsCompact (tiltedLens τ '' closedBall 0 r) := by
  apply (isCompact_closedBall (0 : ℂ) r).image_of_continuousOn
  apply (tiltedLens_continuousOn τ).mono
  intro z hz
  exact (mem_closedBall_zero_iff.mp hz).trans hr

/-- The actual row map supplies properness; no nonsingular selection is an extra input. -/
theorem isCompact_lensInnerRowDomain {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n)
    (hK : IsCompact (stripBody rows)) {r : ℝ} (hr : r ≤ 1) :
    IsCompact (lensInnerRowDomain τ rows r) := by
  let C := tiltedLens τ '' closedBall (0 : ℂ) r
  have hc : IsCompact (univ.pi (fun _ : Fin m => C)) :=
    isCompact_univ_pi (fun _ => isCompact_lens_inner_image τ hr)
  have ht : IsCompact ((EuclideanSpace.equiv (Fin m) ℂ) ⁻¹' univ.pi (fun _ => C)) :=
    (EuclideanSpace.equiv (Fin m) ℂ).toHomeomorph.isCompact_preimage.mpr hc
  have hp := (lensComplexMeasurements_isClosedEmbedding rows hK).isCompact_preimage ht
  convert hp using 1
  ext z
  simp [lensInnerRowDomain, C, lensComplexMeasurements_apply]

theorem lensInnerRowDomain_subset_domain {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) {r : ℝ} (hr : r < 1) :
    lensInnerRowDomain τ rows r ⊆ lensComplexDomain τ rows := by
  intro z hz j
  obtain ⟨u, hu, he⟩ := hz j
  rw [← he]
  exact tiltedLens_mapsTo_ball_interior hτ0 hτ1
    (mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hu).trans_lt hr))

/-- The original strict energy sublevel is inside that fixed compact inner domain. -/
theorem lensPower_sublevel_subset_inner {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) {k : ℕ} (hk : 0 < k)
    {R : ℝ} (hR : 0 < R) :
    {z | z ∈ lensComplexDomain τ rows ∧ lensPowerEnergy τ rows k z < R} ⊆
      lensInnerRowDomain τ rows (lensSublevelRadius R k) := by
  rintro z ⟨hz, he⟩ j
  exact ⟨tiltedLensInverse τ (lensComplexRow (rows j) z),
    mem_closedBall_zero_iff.mpr (lensPowerEnergy_component_lt_radius τ rows hk hR he j).le,
    tiltedLensInverse_right hτ0 hτ1 (hz j)⟩

/-- The literal compact-sublevels field of the remaining mass application. -/
theorem lensPower_sublevel_compact_closure {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n)
    (hK : IsCompact (stripBody rows)) {k : ℕ} (hk : 0 < k)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1) :
    IsCompact (closure {z | z ∈ lensComplexDomain τ rows ∧ lensPowerEnergy τ rows k z < R}) ∧
      closure {z | z ∈ lensComplexDomain τ rows ∧ lensPowerEnergy τ rows k z < R} ⊆
        lensComplexDomain τ rows := by
  have hr := lensSublevelRadius_lt_one hR hR1 hk
  have hc := isCompact_lensInnerRowDomain τ rows hK hr.le
  have hs := closure_minimal (lensPower_sublevel_subset_inner hτ0 hτ1 rows hk hR) hc.isClosed
  exact ⟨hc.of_isClosed_subset isClosed_closure hs,
    hs.trans (lensInnerRowDomain_subset_domain hτ0 hτ1 rows hr)⟩

end
end Funk
