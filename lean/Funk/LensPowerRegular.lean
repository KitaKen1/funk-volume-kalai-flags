import Funk.LensPowerMassInput
import Funk.LensRadialPositive
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! Every positive level of the actual Euclidean power-map energy is regular.
The outward radial derivative is strictly positive away from the unique zero. -/

open Set Complex
open scoped BigOperators

namespace Funk
noncomputable section

theorem lensPowerEnergy_eq_sum_normSq_pow {n m : ℕ} (τ : ℝ)
    (rows : Fin m → Space n) (k : ℕ) (z : LensComplexSpace n) :
    lensPowerEnergy τ rows k z =
      ∑ j, normSq (tiltedLensInverse τ (lensComplexRow (rows j) z)) ^ k := by
  simp only [lensPowerEnergy, lensPowerComponent, norm_pow, normSq_eq_norm_sq, ← pow_mul,
    mul_comm k 2]

theorem lensComplexRow_real_smul {n : ℕ} (row : Space n) (t : ℝ)
    (z : LensComplexSpace n) :
    lensComplexRow row (t • z) = (t : ℂ) * lensComplexRow row z := by
  have h := ((lensComplexRow row).restrictScalars ℝ).map_smul t z
  change lensComplexRow row (t • z) = t • lensComplexRow row z at h
  simpa only [Complex.real_smul] using h

/-- Sum of the actual scalar radial derivatives after taking kth powers. -/
def lensPowerRadialSlope {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n) (k : ℕ)
    (z : LensComplexSpace n) : ℝ :=
  ∑ j, (k : ℝ) * normSq (tiltedLensInverse τ (lensComplexRow (rows j) z)) ^ (k-1) *
    lensInverseRadiusSlope τ (lensComplexRow (rows j) z)

theorem lensPowerEnergy_hasDerivAt_radial {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ)
    {z : LensComplexSpace n} (hz : z ∈ lensComplexDomain τ rows) :
    HasDerivAt (fun t : ℝ => lensPowerEnergy τ rows k (t • z))
      (lensPowerRadialSlope τ rows k z) 1 := by
  simp_rw [lensPowerEnergy_eq_sum_normSq_pow, lensComplexRow_real_smul]
  unfold lensPowerRadialSlope
  convert HasDerivAt.sum (u := Finset.univ) (fun j _ =>
    (lensInverseRadius_hasDerivAt hτ0 hτ1 (hz j)).pow k) using 1
  · ext t
    simp
  · simp

theorem lensPowerRadialSlope_pos {n m : ℕ} {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (rows : Fin m → Space n) (hK : IsCompact (stripBody rows)) {k : ℕ} (hk : 0 < k)
    {z : LensComplexSpace n} (hz : z ∈ lensComplexDomain τ rows) (hz0 : z ≠ 0) :
    0 < lensPowerRadialSlope τ rows k z := by
  have hn : ∃ j, lensComplexRow (rows j) z ≠ 0 := by
    by_contra h
    push Not at h
    exact hz0 ((lensComplexRows_eq_zero_iff rows hK z).mp h)
  obtain ⟨j, hj⟩ := hn
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (normSq_nonneg _) _))
      (lensInverseRadiusSlope_nonneg hτ0 hτ1 (hz i))
  · refine ⟨j, Finset.mem_univ j, ?_⟩
    exact mul_pos (mul_pos (by exact_mod_cast hk)
      (pow_pos (normSq_pos.mpr ((tiltedLensInverse_eq_zero_iff hτ0 hτ1 (hz j)).not.mpr hj)) _))
      (lensInverseRadiusSlope_pos hτ0 hτ1 (hz j) hj)

theorem lensPowerEnergy_differentiableAt_real {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ)
    {z : LensComplexSpace n} (hz : z ∈ lensComplexDomain τ rows) :
    DifferentiableAt ℝ (lensPowerEnergy τ rows k) z := by
  have hinv : ∀ j, DifferentiableAt ℝ
      (fun z => tiltedLensInverse τ (lensComplexRow (rows j) z)) z := by
    intro j
    exact ((hasDerivAt_tiltedLensInverse hτ0 hτ1 (hz j)).differentiableAt.restrictScalars ℝ).comp z
      ((lensComplexRow (rows j)).restrictScalars ℝ).differentiableAt
  have he : lensPowerEnergy τ rows k = fun z =>
      ∑ j, normSq (tiltedLensInverse τ (lensComplexRow (rows j) z)) ^ k :=
    funext (lensPowerEnergy_eq_sum_normSq_pow τ rows k)
  rw [he]
  have hs : ∀ j, DifferentiableAt ℝ
      (fun z => normSq (tiltedLensInverse τ (lensComplexRow (rows j) z)) ^ k) z := by
    intro j
    have h := hinv j
    simp only [normSq_apply]
    fun_prop
  convert DifferentiableAt.sum (u := Finset.univ) (fun j _ => hs j) using 1
  ext x
  simp

theorem lensPowerEnergy_zero {n m : ℕ} {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (rows : Fin m → Space n) {k : ℕ} (hk : 0 < k) :
    lensPowerEnergy τ rows k 0 = 0 := by
  simp [lensPowerEnergy, lensPowerComponent_zero hτ0 hτ1 rows hk]

/-- Surjectivity of the real Frechet derivative is the regular-value condition. -/
theorem lensPowerEnergy_positive_regular {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n)
    (hK : IsCompact (stripBody rows)) {k : ℕ} (hk : 0 < k)
    {R : ℝ} (hR : 0 < R) {z : LensComplexSpace n}
    (hz : z ∈ lensComplexDomain τ rows) (hlevel : lensPowerEnergy τ rows k z = R) :
    Function.Surjective (fderiv ℝ (lensPowerEnergy τ rows k) z) := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    rw [lensPowerEnergy_zero hτ0 hτ1 rows hk] at hlevel
    linarith
  have hl : HasDerivAt (fun t : ℝ => t • z) z 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const z
  have hf : HasFDerivAt (lensPowerEnergy τ rows k)
      (fderiv ℝ (lensPowerEnergy τ rows k) z) ((1 : ℝ) • z) := by
    simpa using (lensPowerEnergy_differentiableAt_real hτ0 hτ1 rows k hz).hasFDerivAt
  have hd := hf.comp_hasDerivAt 1 hl
  have he : (fderiv ℝ (lensPowerEnergy τ rows k) z) z = lensPowerRadialSlope τ rows k z := by
    simpa using hd.unique (lensPowerEnergy_hasDerivAt_radial hτ0 hτ1 rows k hz)
  have hp := lensPowerRadialSlope_pos hτ0 hτ1 rows hK hk hz hz0
  intro y
  refine ⟨(y / lensPowerRadialSlope τ rows k z) • z, ?_⟩
  rw [map_smul, he]
  change y / lensPowerRadialSlope τ rows k z * lensPowerRadialSlope τ rows k z = y
  exact div_mul_cancel₀ y hp.ne'

/-- Exact nonzero-derivative formulation used by the source Stokes interface. -/
theorem lensPowerEnergy_positive_fderiv_ne_zero {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n)
    (hK : IsCompact (stripBody rows)) {k : ℕ} (hk : 0 < k)
    {R : ℝ} (hR : 0 < R) {z : LensComplexSpace n}
    (hz : z ∈ lensComplexDomain τ rows) (hlevel : lensPowerEnergy τ rows k z = R) :
    fderiv ℝ (lensPowerEnergy τ rows k) z ≠ 0 := by
  intro he
  obtain ⟨v, hv⟩ := lensPowerEnergy_positive_regular hτ0 hτ1 rows hK hk hR hz hlevel (1 : ℝ)
  rw [he] at hv
  simp at hv

end
end Funk
