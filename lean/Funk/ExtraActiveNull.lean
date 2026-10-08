import Funk.CollisionNull
import Funk.CanonicalWitness
import Funk.IrredundantCompactRows
import Funk.StripNull

/-! Genuine extra active rows form a null set. Combined with the already
proved endpoint nullity, signed-irredundant nonzero row families are simple
almost everywhere. Pointwise simplicity is neither assumed nor concluded. -/

open Set MeasureTheory

namespace Funk
noncomputable section

theorem volume_extra_active_strict_zero {n : ℕ} {ι : Type*} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : ι → Space n)
    (hirr : SignedIrredundant rows) (s : Fin n → ι)
    (hB : Matrix.det (fun k => rows (s k)) ≠ 0) {a : ι} (ha : a ∉ range s)
    (ha0 : rows a ≠ 0) (b : Fin n → Bool) :
    volume {X : Space n | (∀ k, |dotProduct (rows (s k)) X| < 1) ∧
      |dotProduct (rows a) X| < 1 ∧
      complexRow (rows a) (basisRealWitness τ b (fun k => rows (s k)) X) X ∈
        frontier (lensGraphBody τ)} = 0 := by
  let B : Matrix (Fin n) (Fin n) ℝ := fun k => rows (s k)
  let coeff := rowBasisCoefficients B (rows a)
  obtain ⟨i, j, hij, hi, hj⟩ := extra_row_coefficients_two_nonzero rows hirr s hB ha ha0
  have hz (σ : Bool) : volume (basisMap B ⁻¹'
      {t ∈ collisionHeightDomain coeff | branchCollisionResidual τ b σ coeff t = 0}) = 0 :=
    volume_basisMap_preimage_null hB (volume_collision_residual_zero hτ0 hτ1 b σ
      coeff i j hij hi hj)
  apply measure_mono_null (t := ⋃ σ : Bool, basisMap B ⁻¹'
      {t ∈ collisionHeightDomain coeff | branchCollisionResidual τ b σ coeff t = 0}) ?_
    (measure_iUnion_null (fun σ => hz σ))
  intro X hX
  have hstrip : X ∈ stripBody B := fun k => (hX.1 k).le
  obtain ⟨σ, hσ⟩ := (extra_active_iff_residual_zero hτ0 hτ1 b hB (rows a)
    hstrip hX.2.1.le).mp hX.2.2
  apply mem_iUnion.mpr
  refine ⟨σ, ⟨?_, hσ⟩⟩
  constructor
  · exact fun k => abs_lt.mp (hX.1 k)
  · change dotProduct (rowBasisCoefficients B (rows a)) (basisMap B X) ∈ Ioo (-1) 1
    rw [rowBasisCoefficients_dot hB]
    exact abs_lt.mp hX.2.1

/-- The conclusion does not require feasibility: strict heights and
irredundancy alone make genuine extra activity negligible. -/
theorem ae_noExtraActive_of_strict_heights {n : ℕ} {ι : Type*} [Countable ι]
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : ι → Space n)
    (hirr : SignedIrredundant rows) (hnonzero : ∀ a, rows a ≠ 0)
    (s : Fin n → ι) (hB : Matrix.det (fun k => rows (s k)) ≠ 0) (b : Fin n → Bool) :
    ∀ᵐ X ∂(volume : Measure (Space n)),
      (∀ a, |dotProduct (rows a) X| < 1) → NoExtraActive τ rows s b X := by
  have hrow (a : ι) : ∀ᵐ X ∂(volume : Measure (Space n)),
      (∀ k, |dotProduct (rows (s k)) X| < 1) → |dotProduct (rows a) X| < 1 →
        complexRow (rows a) (basisRealWitness τ b (fun k => rows (s k)) X) X ∈
          frontier (lensGraphBody τ) → a ∈ range s := by
    by_cases ha : a ∈ range s
    · exact Filter.Eventually.of_forall (fun _ _ _ _ => ha)
    · have hz := volume_extra_active_strict_zero hτ0 hτ1 rows hirr s hB ha (hnonzero a) b
      have he : ∀ᵐ X ∂(volume : Measure (Space n)),
          X ∉ {X : Space n | (∀ k, |dotProduct (rows (s k)) X| < 1) ∧
            |dotProduct (rows a) X| < 1 ∧
            complexRow (rows a) (basisRealWitness τ b (fun k => rows (s k)) X) X ∈
              frontier (lensGraphBody τ)} := by
        apply ae_iff.mpr
        simpa only [not_not, mem_ofPred_eq] using hz
      filter_upwards [he] with X hX hS haX hactive
      exact (hX ⟨hS, haX, hactive⟩).elim
  filter_upwards [ae_all_iff.mpr hrow] with X hX hstrict
  intro a ha
  exact hX a (fun k => hstrict (s k)) (hstrict a) ha

theorem ae_noExtraActive_signedIrredundant {n : ℕ} {ι : Type*} [Countable ι]
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : ι → Space n)
    (hirr : SignedIrredundant rows) (hnonzero : ∀ a, rows a ≠ 0)
    (s : Fin n → ι) (hB : Matrix.det (fun k => rows (s k)) ≠ 0) (b : Fin n → Bool) :
    ∀ᵐ X ∂volume.restrict (stripBody rows), NoExtraActive τ rows s b X := by
  filter_upwards [ae_restrict_of_ae
    (ae_noExtraActive_of_strict_heights hτ0 hτ1 rows hirr hnonzero s hB b),
    ae_strict_strip_heights rows] with X hX hs
  exact hX hs

theorem ae_noExtraActive_irredundant_compact {n : ℕ} [Nonempty (Fin n)]
    {ι : Type*} [Countable ι] {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (rows : ι → Space n) (hirr : SignedIrredundant rows) (hK : IsCompact (stripBody rows))
    (s : Fin n → ι) (hB : Matrix.det (fun k => rows (s k)) ≠ 0) (b : Fin n → Bool) :
    ∀ᵐ X ∂volume.restrict (stripBody rows), NoExtraActive τ rows s b X :=
  ae_noExtraActive_signedIrredundant hτ0 hτ1 rows hirr
    (signedIrredundant_nonzero_of_compact rows hirr hK) s hB b

end
end Funk
