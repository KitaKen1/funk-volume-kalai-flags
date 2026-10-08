import Funk.SimplexCertificate
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology

/-! Finite packing after interior non-overlap has been proved.
The non-overlap hypothesis is explicit; this file does not establish it for the
candidate lens construction. Boundary nullity follows from convexity. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk

noncomputable section

theorem convex_rowSimplex {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) :
    Convex ℝ (rowSimplex V) := convex_convexHull ℝ _

theorem isCompact_rowSimplex {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) :
    IsCompact (rowSimplex V) :=
  ((Set.finite_range V).insert 0).isCompact_convexHull ℝ

theorem volume_frontier_rowSimplex {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) :
    volume (frontier (rowSimplex V)) = 0 :=
  (convex_rowSimplex V).addHaar_frontier volume

theorem convex_aedisjoint_of_disjoint_interior {n : ℕ} {S T : Set (Space n)}
    (hS : Convex ℝ S) (hT : Convex ℝ T)
    (hd : Disjoint (interior S) (interior T)) : AEDisjoint volume S T := by
  apply measure_mono_null (t := frontier S ∪ frontier T)
  · intro x hx
    by_cases hs : x ∈ interior S
    · right
      refine ⟨subset_closure hx.2, ?_⟩
      intro ht
      exact Set.disjoint_left.mp hd hs ht
    · left
      exact ⟨subset_closure hx.1, hs⟩
  · exact measure_union_null (hS.addHaar_frontier volume) (hT.addHaar_frontier volume)

/-- General finite packing with interior disjointness, even for degenerate convex sets. -/
theorem convex_sum_volume_le {n : ℕ} {ι : Type*} (indices : Finset ι)
    (S : ι → Set (Space n)) (K : Set (Space n))
    (hc : ∀ i ∈ indices, Convex ℝ (S i))
    (hd : (indices : Set ι).Pairwise (fun i j => Disjoint (interior (S i)) (interior (S j))))
    (hsub : ∀ i ∈ indices, S i ⊆ K) :
    ∑ i ∈ indices, volume (S i) ≤ volume K := by
  have ha : (indices : Set ι).Pairwise (fun i j => AEDisjoint volume (S i) (S j)) := by
    intro i hi j hj hij
    exact convex_aedisjoint_of_disjoint_interior (hc i hi) (hc j hj) (hd hi hj hij)
  rw [← measure_biUnion_finset₀ ha (fun i hi => (hc i hi).nullMeasurableSet volume)]
  exact measure_mono (by
    intro x hx
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp hx
    exact hsub i hi hx)

theorem rowSimplex_sum_volume_le {n : ℕ} {ι : Type*} (indices : Finset ι)
    (V : ι → Matrix (Fin n) (Fin n) ℝ) (K : Set (Space n))
    (hd : (indices : Set ι).Pairwise
      (fun i j => Disjoint (interior (rowSimplex (V i))) (interior (rowSimplex (V j)))))
    (hsub : ∀ i ∈ indices, rowSimplex (V i) ⊆ K) :
    ∑ i ∈ indices, ENNReal.ofReal (|(V i).det| / (n.factorial : ℝ)) ≤ volume K := by
  simpa only [volume_rowSimplex] using
    convex_sum_volume_le indices (fun i => rowSimplex (V i)) K
      (fun i _ => convex_rowSimplex (V i)) hd hsub

/-- The scalar denominators can be summed once geometric non-overlap is supplied. -/
theorem vertexSimplex_sum_bound_polar {n : ℕ} {ι κ : Type*} {rows : ι → Space n}
    {τ : ℝ} {X : Space n} (hτ₀ : 0 ≤ τ) (hτ₁ : τ < 1)
    (hX : X ∈ stripBody rows) (indices : Finset κ)
    (selected : κ → Fin n → ι) (signs : κ → Fin n → ℝ)
    (hs : ∀ k ∈ indices, ∀ i, signs k i = 1 ∨ signs k i = -1)
    (hd : (indices : Set κ).Pairwise (fun k l =>
      Disjoint (interior (rowSimplex (vertexMatrix τ (signs k) (fun i => rows (selected k i)) X)))
        (interior (rowSimplex (vertexMatrix τ (signs l) (fun i => rows (selected l i)) X))))) :
    ∑ k ∈ indices, ENNReal.ofReal
      (|Matrix.det (fun i => rows (selected k i) : Matrix (Fin n) (Fin n) ℝ)| /
        ((n.factorial : ℝ) * ∏ i, (1 - signs k i * τ * dotProduct (rows (selected k i)) X))) ≤
          volume (coordinatePolar (translate (stripBody rows) (τ • X))) := by
  have he : ∀ k ∈ indices,
      volume (rowSimplex (vertexMatrix τ (signs k) (fun i => rows (selected k i)) X)) =
      ENNReal.ofReal (|Matrix.det (fun i => rows (selected k i) : Matrix (Fin n) (Fin n) ℝ)| /
        ((n.factorial : ℝ) * ∏ i, (1 - signs k i * τ * dotProduct (rows (selected k i)) X))) := by
    intro k hk
    exact volume_vertexSimplex hτ₀ hτ₁ (hs k hk) (fun i => hX (selected k i))
  rw [← Finset.sum_congr rfl he]
  exact convex_sum_volume_le indices _ _
    (fun k _ => convex_rowSimplex _) hd
    (fun k hk => feasibleHull_subset_polar hτ₀ hτ₁ hX (selected k) (signs k) (hs k hk))

/-- Reindexing the same vertices does not create a new geometric simplex. -/
theorem rowSimplex_reindex {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ)
    (e : Equiv.Perm (Fin n)) : rowSimplex (fun i => V (e i)) = rowSimplex V := by
  unfold rowSimplex
  rw [show Set.range (fun i => V (e i)) = Set.range V from e.surjective.range_comp V]

/-- This rules out a tempting but invalid shortcut: count different ordered bases
as disjoint simplices. For nonzero determinant, their common volume is positive. -/
theorem rowSimplex_not_aedisjoint_reindex {n : ℕ}
    (V : Matrix (Fin n) (Fin n) ℝ) (e : Equiv.Perm (Fin n)) (hV : V.det ≠ 0) :
    ¬ AEDisjoint volume (rowSimplex V) (rowSimplex (fun i => V (e i))) := by
  rw [rowSimplex_reindex]
  intro h
  have hz := h.eq
  rw [Set.inter_self, volume_rowSimplex] at hz
  have hp : 0 < |V.det| / (n.factorial : ℝ) :=
    div_pos (abs_pos.mpr hV) (by exact_mod_cast n.factorial_pos)
  exact (ENNReal.ofReal_pos.mpr hp).ne' hz

end
end Funk
