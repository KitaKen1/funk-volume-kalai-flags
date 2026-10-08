import Funk.FunkFinite
import Funk.FeasibleRegion
import Funk.BasisCubeCertificate

/-! The explicit geometric regions and general finiteness theorem close the
analytic part of the reduction. Coverage and active non-overlap remain explicit
hypotheses. The cube calibration discharges them without assuming either goal. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

/-- Both requirements of the Funk target, conditional only on the displayed
basis, covering and packing data for the specified symmetric strip body. -/
theorem funkVolume_strip_target_of_feasible_cover {n : ℕ} {ι κ : Type*} [Countable ι]
    (rows : ι → Space n) (hK : IsSymmetricConvexBody (stripBody rows))
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (indices : Finset κ)
    (selected : κ → Fin n → ι) (b : κ → Fin n → Bool)
    (hB : ∀ k ∈ indices, Matrix.det (fun i => rows (selected k i) : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hd : ∀ᵐ X ∂volume.restrict (stripBody rows), ∀ k ∈ indices, ∀ l ∈ indices,
      k ≠ l → X ∈ basisFeasibleRegion τ rows (selected k) (b k) →
      X ∈ basisFeasibleRegion τ rows (selected l) (b l) →
      Disjoint (interior (rowSimplex (vertexMatrix τ (fun i => branchSign (b k i))
          (fun i => rows (selected k i)) X)))
        (interior (rowSimplex (vertexMatrix τ (fun i => branchSign (b l i))
          (fun i => rows (selected l i)) X))))
    (hcover : 1 ≤ ∑ k ∈ indices, lensBoundaryRows n τ
      (basisBoundaryEvent τ (b k) (fun i => rows (selected k i))
        (basisFeasibleRegion τ rows (selected k) (b k)))) :
    funkVolume (stripBody rows) τ < ⊤ ∧
      ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) ≤
        funkVolume (stripBody rows) τ := by
  refine ⟨funkVolume_symmetricConvexBody_finite hK hτ0 hτ1, ?_⟩
  exact funkVolume_strip_lower_of_basis_cover_ae rows (measurableSet_stripBody rows)
    hτ0 hτ1 indices selected b (fun k => basisFeasibleRegion τ rows (selected k) (b k)) hB
    (fun k _ => measurableSet_basisFeasibleRegion hτ0 hτ1 rows (selected k) (b k))
    (fun k _ => basisFeasibleRegion_subset τ rows (selected k) (b k)) hd hcover

/-- An end-to-end application using actual feasible regions and general finiteness. -/
theorem cube_funk_target_via_feasible_regions (n : ℕ) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    funkVolume (coordinateCube n) τ < ⊤ ∧
      ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) ≤
        funkVolume (coordinateCube n) τ := by
  classical
  have hB : Matrix.det (1 : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by simp
  have he (b : Fin n → Bool) :
      basisFeasibleRegion τ (1 : Matrix (Fin n) (Fin n) ℝ) id b = coordinateCube n :=
    basisFeasibleRegion_basis hτ0 hτ1 b hB
  apply funkVolume_strip_target_of_feasible_cover (1 : Matrix (Fin n) (Fin n) ℝ)
    (coordinateCube_isSymmetricConvexBody n) hτ0 hτ1 Finset.univ
    (fun _ : Fin n → Bool => id) id
  · exact fun _ _ => hB
  · filter_upwards [ae_restrict_mem (μ := volume)
      (measurableSet_stripBody (1 : Matrix (Fin n) (Fin n) ℝ))] with X hX
    intro b _ c _ hbc _ _
    exact cube_vertexSimplex_interior_disjoint hτ0.le hτ1 hX hbc
  · change 1 ≤ ∑ b : Fin n → Bool,
      lensBoundaryRows n τ (basisBoundaryEvent τ b (1 : Matrix (Fin n) (Fin n) ℝ)
        (basisFeasibleRegion τ (1 : Matrix (Fin n) (Fin n) ℝ) id b))
    simp only [he]
    exact (cube_basis_event_sum n hτ0 hτ1).ge

end
end Funk
