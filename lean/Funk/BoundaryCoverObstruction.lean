import Funk.UnsignedBoundaryCover

/-! A pointwise shortcut to the probability-cover inequality is false.
For three irredundant directions of a real hexagon, one genuine boundary sample
fails every increasing two-row interpolation basis. This does not refute the
probability-sum inequality, almost-everywhere simplicity, or either main goal. -/

open Set

namespace Funk
noncomputable section

def hexagonCoverRows : Fin 3 → Space 2 := ![![1, 0], ![0, 1], ![1, 1]]

/-- The obstruction survives the exact signed-convex irredundancy preprocessing. -/
theorem hexagonCoverRows_signedIrredundant : SignedIrredundant hexagonCoverRows := by
  intro j hj
  let witnesses : Fin 3 → Space 2 := ![![2, -1], ![-1, 2], ![1, 1]]
  have hX : witnesses j ∈ stripBody
      (fun k : {k : Fin 3 // k ≠ j} => hexagonCoverRows k.val) := by
    intro k
    obtain ⟨k, hk⟩ := k
    fin_cases j <;> fin_cases k
    all_goals first | exact (hk rfl).elim |
      norm_num [witnesses, hexagonCoverRows, dotProduct, Fin.sum_univ_two]
  have hb := strip_constraint_of_mem_signedRowHull _ hX hj
  fin_cases j <;> norm_num [witnesses, hexagonCoverRows, dotProduct, Fin.sum_univ_two] at hb

def hexagonBoundarySample (τ : ℝ) : Fin 3 → ℂ :=
  ![lensRightPoint τ 0, lensRightPoint τ 0, -lensRightPoint τ 0]

/-- The horizontal section of the actual lens has endpoints ±profile(0). -/
theorem lens_horizontal_mem_iff {τ : ℝ} {z : ℂ} (hz : z.im = 0) :
    z ∈ lensGraphBody τ ↔ -lensProfile τ 0 ≤ z.re ∧ z.re ≤ lensProfile τ 0 := by
  simp [lensGraphBody, lensChordCoordinate, hz]
  intro _
  constructor <;> intro h <;> linarith

theorem lensRightPoint_zero_eq_profile {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    lensRightPoint τ 0 = (lensProfile τ 0 : ℂ) := by
  have hi := lensRightPoint_im hτ0 hτ1 (show (0 : ℝ) ∈ Icc (-1) 1 by norm_num)
  have hc := lensRightPoint_chord τ 0
  apply Complex.ext
  · simpa [lensChordCoordinate, hi] using hc
  · simpa using hi

/-- These are actual frontier samples, rather than an arbitrary rational model. -/
theorem hexagonBoundarySample_frontier {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (j : Fin 3) :
    hexagonBoundarySample τ j ∈ frontier (lensGraphBody τ) := by
  have hr := lensBranchPoint_mem_frontier (t := 0) hτ0 hτ1 true
  have hl := lensBranchPoint_mem_frontier (t := 0) hτ0 hτ1 false
  fin_cases j
  · exact hr
  · exact hr
  · simpa [hexagonBoundarySample, lensBranchPoint, lensLeftPoint] using hl

/-- No increasing nonsingular basis covers this one common three-row sample. -/
theorem hexagonBoundarySample_all_bases_fail {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (s : Fin 2 → Fin 3) (hs : StrictMono s)
    (hB : Matrix.det (fun i => hexagonCoverRows (s i)) ≠ 0) :
    (fun i => hexagonBoundarySample τ (s i)) ∉
      boundaryInterpolationEvent τ hexagonCoverRows s := by
  intro he
  obtain ⟨Y, X, hY, hall⟩ := (mem_boundaryInterpolationEvent_iff τ hexagonCoverRows s hB _).mp he
  have hp := lensProfile_pos hτ0 hτ1 (show (0 : ℝ) ∈ Ioo (-1) 1 by norm_num)
  have hw := lensRightPoint_zero_eq_profile hτ0 hτ1
  have hr0 := congrArg Complex.re (hY 0)
  have hr1 := congrArg Complex.re (hY 1)
  have hi0 := congrArg Complex.im (hY 0)
  have hi1 := congrArg Complex.im (hY 1)
  have hsel : s 0 < s 1 := hs (by decide)
  generalize h0 : s 0 = a at hsel hr0 hi0
  generalize h1 : s 1 = b at hsel hr1 hi1
  fin_cases a <;> fin_cases b <;> norm_num at hsel
  all_goals
    simp [hexagonCoverRows, hexagonBoundarySample, complexRow, dotProduct,
      Fin.sum_univ_two, hw] at hr0 hr1 hi0 hi1
  · have hz : (complexRow (hexagonCoverRows 2) Y X).im = 0 := by
      simp [hexagonCoverRows, complexRow, dotProduct, Fin.sum_univ_two, hi0, hi1]
    have hb := (lens_horizontal_mem_iff hz).mp (hall 2)
    simp [hexagonCoverRows, complexRow, dotProduct, Fin.sum_univ_two] at hb
    linarith
  · have hz : (complexRow (hexagonCoverRows 1) Y X).im = 0 := by
      simp [hexagonCoverRows, complexRow, dotProduct, Fin.sum_univ_two]
      linarith
    have hb := (lens_horizontal_mem_iff hz).mp (hall 1)
    simp [hexagonCoverRows, complexRow, dotProduct, Fin.sum_univ_two] at hb
    linarith
  · have hz : (complexRow (hexagonCoverRows 0) Y X).im = 0 := by
      simp [hexagonCoverRows, complexRow, dotProduct, Fin.sum_univ_two]
      linarith
    have hb := (lens_horizontal_mem_iff hz).mp (hall 0)
    simp [hexagonCoverRows, complexRow, dotProduct, Fin.sum_univ_two] at hb
    linarith

/-- A genuine common sample fails every actual unsigned canonical basis. -/
theorem exists_boundary_sample_all_unsigned_bases_fail {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ∃ z : Fin 3 → ℂ, (∀ j, z j ∈ frontier (lensGraphBody τ)) ∧
      ∀ s ∈ unsignedBasisIndices hexagonCoverRows,
        (fun i => z (s i)) ∉ boundaryInterpolationEvent τ hexagonCoverRows s := by
  refine ⟨hexagonBoundarySample τ, hexagonBoundarySample_frontier hτ0 hτ1, ?_⟩
  intro s hs
  obtain ⟨hmono, hB⟩ := (mem_unsignedBasisIndices hexagonCoverRows s).mp hs
  exact hexagonBoundarySample_all_bases_fail hτ0 hτ1 s hmono hB

end
end Funk
