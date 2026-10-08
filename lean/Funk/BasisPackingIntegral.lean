import Funk.FunkScaling
import Funk.SimplexPacking

/-! Combining finitely many genuine basis-event probabilities with geometric
packing. Both the probability covering bound and active-simplex non-overlap
remain explicit mathematical hypotheses. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

theorem activeSimplex_sum_le_polar {n : ℕ} {ι κ : Type*} {rows : ι → Space n}
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (indices : Finset κ)
    (selected : κ → Fin n → ι) (b : κ → Fin n → Bool) (s : κ → Set (Space n))
    {X : Space n} (hX : X ∈ stripBody rows)
    (hd : ∀ k ∈ indices, ∀ l ∈ indices, k ≠ l → X ∈ s k → X ∈ s l →
      Disjoint (interior (rowSimplex (vertexMatrix τ (fun i => branchSign (b k i))
          (fun i => rows (selected k i)) X)))
        (interior (rowSimplex (vertexMatrix τ (fun i => branchSign (b l i))
          (fun i => rows (selected l i)) X)))) :
    ∑ k ∈ indices, (s k).indicator (fun Y => volume (rowSimplex
      (vertexMatrix τ (fun i => branchSign (b k i)) (fun i => rows (selected k i)) Y))) X ≤
        volume (coordinatePolar (translate (stripBody rows) (τ • X))) := by
  classical
  have h := convex_sum_volume_le (indices.filter (fun k => X ∈ s k))
    (fun k => rowSimplex (vertexMatrix τ (fun i => branchSign (b k i))
      (fun i => rows (selected k i)) X))
    (coordinatePolar (translate (stripBody rows) (τ • X)))
    (fun _ _ => convex_rowSimplex _)
    (by
      intro k hk l hl hkl
      exact hd k (Finset.mem_filter.mp hk).1 l (Finset.mem_filter.mp hl).1 hkl
        (Finset.mem_filter.mp hk).2 (Finset.mem_filter.mp hl).2)
    (fun k _ => feasibleHull_subset_polar hτ0 hτ1 hX (selected k)
      (fun i => branchSign (b k i)) (fun i => branchSign_cases (b k i)))
  simpa only [Finset.sum_filter, Set.indicator_apply] using h

/-- The complete probability-to-integrated-polar estimate with geometric hypotheses. -/
theorem basis_probabilities_le_polar_integral_ae {n : ℕ} {ι κ : Type*}
    (rows : ι → Space n) (hC : MeasurableSet (stripBody rows))
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (indices : Finset κ)
    (selected : κ → Fin n → ι) (b : κ → Fin n → Bool) (s : κ → Set (Space n))
    (hB : ∀ k ∈ indices, Matrix.det (fun i => rows (selected k i) : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hs : ∀ k ∈ indices, MeasurableSet (s k))
    (hsub : ∀ k ∈ indices, s k ⊆ stripBody rows)
    (hd : ∀ᵐ X ∂volume.restrict (stripBody rows), ∀ k ∈ indices, ∀ l ∈ indices,
      k ≠ l → X ∈ s k → X ∈ s l →
      Disjoint (interior (rowSimplex (vertexMatrix τ (fun i => branchSign (b k i))
          (fun i => rows (selected k i)) X)))
        (interior (rowSimplex (vertexMatrix τ (fun i => branchSign (b l i))
          (fun i => rows (selected l i)) X)))) :
    ∑ k ∈ indices, lensBoundaryRows n τ
      (basisBoundaryEvent τ (b k) (fun i => rows (selected k i)) (s k)) ≤
      basisVolumeFactor n τ * ∫⁻ X in stripBody rows,
        volume (coordinatePolar (translate (stripBody rows) (τ • X))) := by
  let V (k : κ) (X : Space n) := volume (rowSimplex
    (vertexMatrix τ (fun i => branchSign (b k i)) (fun i => rows (selected k i)) X))
  have he (k : κ) (hk : k ∈ indices) : lensBoundaryRows n τ
      (basisBoundaryEvent τ (b k) (fun i => rows (selected k i)) (s k)) =
      basisVolumeFactor n τ * ∫⁻ X in stripBody rows, (s k).indicator (V k) X := by
    rw [basisBoundaryEvent_probability_volume hτ0 hτ1 (b k) (hB k hk) (hs k hk)
      (fun _ hx i => hsub k hk hx (selected k i)), setLIntegral_indicator (hs k hk),
      inter_eq_left.mpr (hsub k hk)]
  have hv (k : κ) : Measurable (V k) :=
    measurable_vertexSimplex_volume τ (b k) (fun i => rows (selected k i))
  rw [Finset.sum_congr rfl he, ← Finset.mul_sum,
    ← lintegral_finsetSum (μ := volume.restrict (stripBody rows)) indices
      (fun k hk => (hv k).indicator (hs k hk))]
  apply mul_le_mul_right
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hC, hd] with X hX hdX
  exact activeSimplex_sum_le_polar hτ0.le hτ1 indices selected b s hX hdX

theorem basis_probabilities_le_polar_integral {n : ℕ} {ι κ : Type*}
    (rows : ι → Space n) (hC : MeasurableSet (stripBody rows))
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (indices : Finset κ)
    (selected : κ → Fin n → ι) (b : κ → Fin n → Bool) (s : κ → Set (Space n))
    (hB : ∀ k ∈ indices, Matrix.det (fun i => rows (selected k i) : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hs : ∀ k ∈ indices, MeasurableSet (s k))
    (hsub : ∀ k ∈ indices, s k ⊆ stripBody rows)
    (hd : ∀ X ∈ stripBody rows, ∀ k ∈ indices, ∀ l ∈ indices,
      k ≠ l → X ∈ s k → X ∈ s l →
      Disjoint (interior (rowSimplex (vertexMatrix τ (fun i => branchSign (b k i))
          (fun i => rows (selected k i)) X)))
        (interior (rowSimplex (vertexMatrix τ (fun i => branchSign (b l i))
          (fun i => rows (selected l i)) X)))) :
    ∑ k ∈ indices, lensBoundaryRows n τ
      (basisBoundaryEvent τ (b k) (fun i => rows (selected k i)) (s k)) ≤
      basisVolumeFactor n τ * ∫⁻ X in stripBody rows,
        volume (coordinatePolar (translate (stripBody rows) (τ • X))) := by
  apply basis_probabilities_le_polar_integral_ae rows hC hτ0 hτ1 indices selected b s hB hs hsub
  filter_upwards [ae_restrict_mem hC] with X hX
  exact hd X hX

/-- Full sharp lower bound for strip bodies, conditional on the two unresolved
geometric inputs. This theorem does not prove finiteness or either input. -/
theorem funkVolume_strip_lower_of_basis_cover {n : ℕ} {ι κ : Type*}
    (rows : ι → Space n) (hC : MeasurableSet (stripBody rows))
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (indices : Finset κ)
    (selected : κ → Fin n → ι) (b : κ → Fin n → Bool) (s : κ → Set (Space n))
    (hB : ∀ k ∈ indices, Matrix.det (fun i => rows (selected k i) : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hs : ∀ k ∈ indices, MeasurableSet (s k))
    (hsub : ∀ k ∈ indices, s k ⊆ stripBody rows)
    (hd : ∀ X ∈ stripBody rows, ∀ k ∈ indices, ∀ l ∈ indices,
      k ≠ l → X ∈ s k → X ∈ s l →
      Disjoint (interior (rowSimplex (vertexMatrix τ (fun i => branchSign (b k i))
          (fun i => rows (selected k i)) X)))
        (interior (rowSimplex (vertexMatrix τ (fun i => branchSign (b l i))
          (fun i => rows (selected l i)) X))))
    (hcover : 1 ≤ ∑ k ∈ indices, lensBoundaryRows n τ
      (basisBoundaryEvent τ (b k) (fun i => rows (selected k i)) (s k))) :
    ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) ≤
      funkVolume (stripBody rows) τ := by
  apply funkVolume_lower_of_mass_integral hC hτ0 hτ1
  exact hcover.trans (basis_probabilities_le_polar_integral rows hC hτ0 hτ1
    indices selected b s hB hs hsub hd)

/-- Null exceptional sets of parameters are allowed in the packing hypothesis. -/
theorem funkVolume_strip_lower_of_basis_cover_ae {n : ℕ} {ι κ : Type*}
    (rows : ι → Space n) (hC : MeasurableSet (stripBody rows))
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (indices : Finset κ)
    (selected : κ → Fin n → ι) (b : κ → Fin n → Bool) (s : κ → Set (Space n))
    (hB : ∀ k ∈ indices, Matrix.det (fun i => rows (selected k i) : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hs : ∀ k ∈ indices, MeasurableSet (s k))
    (hsub : ∀ k ∈ indices, s k ⊆ stripBody rows)
    (hd : ∀ᵐ X ∂volume.restrict (stripBody rows), ∀ k ∈ indices, ∀ l ∈ indices,
      k ≠ l → X ∈ s k → X ∈ s l →
      Disjoint (interior (rowSimplex (vertexMatrix τ (fun i => branchSign (b k i))
          (fun i => rows (selected k i)) X)))
        (interior (rowSimplex (vertexMatrix τ (fun i => branchSign (b l i))
          (fun i => rows (selected l i)) X))))
    (hcover : 1 ≤ ∑ k ∈ indices, lensBoundaryRows n τ
      (basisBoundaryEvent τ (b k) (fun i => rows (selected k i)) (s k))) :
    ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) ≤
      funkVolume (stripBody rows) τ := by
  apply funkVolume_lower_of_mass_integral hC hτ0 hτ1
  exact hcover.trans (basis_probabilities_le_polar_integral_ae rows hC hτ0 hτ1
    indices selected b s hB hs hsub hd)

end
end Funk
