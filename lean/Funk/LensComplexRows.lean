import Funk.LensInverse
import Funk.UnsignedBoundaryCover
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Actual complex Euclidean coordinates for the remaining holomorphic mass input.
The finite real row family is complexified without changing its real/imaginary
row evaluations. Compactness of its actual strip body supplies injectivity. -/

open Set Metric
open scoped BigOperators

namespace Funk
noncomputable section

abbrev LensComplexSpace (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- Complex linear evaluation of a real row in the upstream Euclidean convention. -/
def lensComplexRow {n : ℕ} (row : Space n) : LensComplexSpace n →L[ℂ] ℂ :=
  ∑ i : Fin n, (row i : ℂ) • EuclideanSpace.proj i

theorem lensComplexRow_apply {n : ℕ} (row : Space n) (z : LensComplexSpace n) :
    lensComplexRow row z = ∑ i : Fin n, (row i : ℂ) * z i := by
  simp [lensComplexRow]

theorem lensComplexRow_re {n : ℕ} (row : Space n) (z : LensComplexSpace n) :
    (lensComplexRow row z).re = dotProduct row (fun i => (z i).re) := by
  simp [lensComplexRow_apply, dotProduct]

theorem lensComplexRow_im {n : ℕ} (row : Space n) (z : LensComplexSpace n) :
    (lensComplexRow row z).im = dotProduct row (fun i => (z i).im) := by
  simp [lensComplexRow_apply, dotProduct]

/-- Exact identification with the complex row used by the completed boundary adapter. -/
theorem lensComplexRow_eq_complexRow {n : ℕ} (row : Space n) (z : LensComplexSpace n) :
    lensComplexRow row z = complexRow row (fun i => (z i).re) (fun i => (z i).im) := by
  apply Complex.ext
  · exact lensComplexRow_re row z
  · exact lensComplexRow_im row z

/-- A real kernel direction would give a whole noncompact line in the actual body. -/
theorem rows_kernel_eq_zero_of_compact {n m : ℕ} (rows : Fin m → Space n)
    (hK : IsCompact (stripBody rows)) (x : Space n)
    (hx : ∀ j, dotProduct (rows j) x = 0) : x = 0 := by
  by_contra hne
  have hc := (isClosedEmbedding_smul_left (𝕜 := ℝ) hne).isCompact_preimage hK
  have he : (fun t : ℝ => t • x) ⁻¹' stripBody rows = univ := by
    ext t
    simp [stripBody, dotProduct_smul, hx]
  rw [he] at hc
  exact hc.ne_univ rfl

/-- All complex row evaluations vanish exactly at zero, with no selected basis input. -/
theorem lensComplexRows_eq_zero_iff {n m : ℕ} (rows : Fin m → Space n)
    (hK : IsCompact (stripBody rows)) (z : LensComplexSpace n) :
    (∀ j, lensComplexRow (rows j) z = 0) ↔ z = 0 := by
  constructor
  · intro hz
    have hr : (fun i => (z i).re) = (0 : Space n) :=
      rows_kernel_eq_zero_of_compact rows hK _ (fun j => by
        simpa only [lensComplexRow_re, Complex.zero_re] using congrArg Complex.re (hz j))
    have hi : (fun i => (z i).im) = (0 : Space n) :=
      rows_kernel_eq_zero_of_compact rows hK _ (fun j => by
        simpa only [lensComplexRow_im, Complex.zero_im] using congrArg Complex.im (hz j))
    ext i
    apply Complex.ext
    · exact congrFun hr i
    · exact congrFun hi i
  · rintro rfl j
    exact map_zero _

/-- The complex measurement map, still in Euclidean coordinates. -/
def lensComplexMeasurements {n m : ℕ} (rows : Fin m → Space n) :
    LensComplexSpace n →L[ℂ] LensComplexSpace m :=
  (EuclideanSpace.equiv (Fin m) ℂ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j => lensComplexRow (rows j)))

theorem lensComplexMeasurements_apply {n m : ℕ} (rows : Fin m → Space n)
    (z : LensComplexSpace n) (j : Fin m) :
    lensComplexMeasurements rows z j = lensComplexRow (rows j) z := rfl

theorem lensComplexMeasurements_injective {n m : ℕ} (rows : Fin m → Space n)
    (hK : IsCompact (stripBody rows)) : Function.Injective (lensComplexMeasurements rows) := by
  apply (lensComplexMeasurements rows).toLinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro z hz
  apply (lensComplexRows_eq_zero_iff rows hK z).mp
  intro j
  exact congrArg (fun w : LensComplexSpace m => w j) hz

/-- Properness needed to obtain compact simultaneous row constraints. -/
theorem lensComplexMeasurements_isClosedEmbedding {n m : ℕ} (rows : Fin m → Space n)
    (hK : IsCompact (stripBody rows)) : Topology.IsClosedEmbedding (lensComplexMeasurements rows) :=
  LinearMap.isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr (lensComplexMeasurements_injective rows hK))

/-- The actual open domain for powers of the tilted-lens inverse. -/
def lensComplexDomain {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n) : Set (LensComplexSpace n) :=
  {z | ∀ j, lensComplexRow (rows j) z ∈ interior (lensGraphBody τ)}

theorem isOpen_lensComplexDomain {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n) :
    IsOpen (lensComplexDomain τ rows) := by
  unfold lensComplexDomain
  rw [ofPred_forall]
  exact isOpen_iInter_of_finite (fun j => isOpen_interior.preimage (lensComplexRow (rows j)).continuous)

theorem zero_mem_lensComplexDomain {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) :
    (0 : LensComplexSpace n) ∈ lensComplexDomain τ rows := by
  intro j
  rw [map_zero]
  exact lensGraphBody_zero_mem_interior hτ0 hτ1

end
end Funk
