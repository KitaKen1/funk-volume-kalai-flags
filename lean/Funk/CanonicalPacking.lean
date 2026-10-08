import Funk.CanonicalWitness
import Funk.StripNull

/-! General geometric separation and canonical basis indices feed the actual
Funk integral. The remaining simplicity and covering hypotheses are displayed
explicitly; they are not proved for arbitrary polytopes here. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

theorem feasible_simplex_disjoint_of_noExtraActive {n : ℕ} {ι : Type*} [LinearOrder ι]
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : ι → Space n)
    (s t : Fin n → ι) (b c : Fin n → Bool)
    (hs : StrictMono s) (ht : StrictMono t)
    (hB : Matrix.det (fun i => rows (s i)) ≠ 0)
    (hC : Matrix.det (fun i => rows (t i)) ≠ 0) {X : Space n}
    (hS : X ∈ basisFeasibleRegion τ rows s b)
    (hT : X ∈ basisFeasibleRegion τ rows t c)
    (hX : ∀ j, |dotProduct (rows j) X| < 1)
    (hactive : NoExtraActive τ rows s b X) (hne : (s, b) ≠ (t, c)) :
    Disjoint
      (interior (rowSimplex (vertexMatrix τ (fun i => branchSign (b i)) (fun i => rows (s i)) X)))
      (interior (rowSimplex (vertexMatrix τ (fun i => branchSign (c i)) (fun i => rows (t i)) X))) := by
  apply feasible_simplex_interior_disjoint_of_witness_ne hτ0 hτ1 rows s t b c hB hC hS hT
  intro he
  have hc := canonical_basis_eq_of_witness_eq hτ0 hτ1 rows s t b c hs ht hB hC hT hX hactive he
  exact hne (Prod.ext hc.1 hc.2)

/-- Non-overlap and height-endpoint nullity are now proved internally.
Simplicity and the actual boundary probability cover remain explicit inputs. -/
theorem funkVolume_strip_target_of_simple_cover {n : ℕ} {ι κ : Type*}
    [LinearOrder ι] [Countable ι] (rows : ι → Space n)
    (hK : IsSymmetricConvexBody (stripBody rows)) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (indices : Finset κ)
    (selected : κ → Fin n → ι) (b : κ → Fin n → Bool)
    (hB : ∀ k ∈ indices, Matrix.det (fun i => rows (selected k i) : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hs : ∀ k ∈ indices, StrictMono (selected k))
    (hchoices : Set.InjOn (fun k => (selected k, b k)) (indices : Set κ))
    (hsimple : ∀ᵐ X ∂volume.restrict (stripBody rows), ∀ k ∈ indices,
      X ∈ basisFeasibleRegion τ rows (selected k) (b k) →
        NoExtraActive τ rows (selected k) (b k) X)
    (hcover : 1 ≤ ∑ k ∈ indices, lensBoundaryRows n τ
      (basisBoundaryEvent τ (b k) (fun i => rows (selected k i))
        (basisFeasibleRegion τ rows (selected k) (b k)))) :
    funkVolume (stripBody rows) τ < ⊤ ∧
      ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) ≤
        funkVolume (stripBody rows) τ := by
  apply funkVolume_strip_target_of_feasible_cover rows hK hτ0 hτ1 indices selected b hB
  · filter_upwards [hsimple, ae_strict_strip_heights rows] with X hsimpleX hX
    intro k hk l hl hkl hS hT
    apply feasible_simplex_disjoint_of_noExtraActive hτ0 hτ1 rows (selected k) (selected l)
      (b k) (b l) (hs k hk) (hs l hl) (hB k hk) (hB l hl) hS hT hX (hsimpleX k hk hS)
    exact fun he => hkl (hchoices hk hl he)
  · exact hcover

/-- The new geometric separator, simplicity criterion and nullity layer have an
all-dimensional application with every hypothesis discharged. -/
theorem cube_funk_target_via_canonical_basis (n : ℕ) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    funkVolume (coordinateCube n) τ < ⊤ ∧
      ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) ≤
        funkVolume (coordinateCube n) τ := by
  classical
  have hB : Matrix.det (1 : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by simp
  have he (b : Fin n → Bool) :
      basisFeasibleRegion τ (1 : Matrix (Fin n) (Fin n) ℝ) id b = coordinateCube n :=
    basisFeasibleRegion_basis hτ0 hτ1 b hB
  apply funkVolume_strip_target_of_simple_cover (1 : Matrix (Fin n) (Fin n) ℝ)
    (coordinateCube_isSymmetricConvexBody n) hτ0 hτ1 Finset.univ
    (fun _ : Fin n → Bool => id) id
  · exact fun _ _ => hB
  · exact fun _ _ => strictMono_id
  · intro b _ c _ h
    exact congr_arg Prod.snd h
  · filter_upwards [] with X
    intro b _ _ j _
    exact ⟨j, rfl⟩
  · change 1 ≤ ∑ b : Fin n → Bool,
      lensBoundaryRows n τ (basisBoundaryEvent τ b (1 : Matrix (Fin n) (Fin n) ℝ)
        (basisFeasibleRegion τ (1 : Matrix (Fin n) (Fin n) ℝ) id b))
    simp only [he]
    exact (cube_basis_event_sum n hτ0 hτ1).ge

end
end Funk
