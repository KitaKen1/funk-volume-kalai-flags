import Funk.HalfspaceVertices
import Funk.CoordinateBipolar
import Funk.IrredundantCover

/-! Finite vertices to finite strips for the original symmetric convex body.
The rows are obtained from a finite vertex presentation of its actual polar.
Probability covering is not assumed or proved by this representation theorem. -/

open Set MeasureTheory

namespace Funk
noncomputable section

theorem coordinatePolar_finset_hull_eq_halfspace {n : ℕ} (vertices : Finset (Space n)) :
    coordinatePolar (convexHull ℝ (vertices : Set (Space n))) =
      halfspaceBody (fun v : vertices => v.val) (fun _ => 1) := by
  rw [coordinatePolar_convexHull]
  ext y
  constructor
  · intro hy v
    exact (dotProduct_comm _ _).trans_le (hy v.val v.property)
  · intro hy v hv
    exact (dotProduct_comm _ _).trans_le (hy ⟨v, hv⟩)

theorem coordinatePolar_isFinitePolytope {n : ℕ} {P : Set (Space n)}
    (hP : IsFinitePolytope P) (hv : Convex ℝ P) (hi : 0 ∈ interior P) :
    IsFinitePolytope (coordinatePolar P) := by
  obtain ⟨vertices, rfl⟩ := hP
  have he := coordinatePolar_finset_hull_eq_halfspace vertices
  rw [he]
  apply halfspaceBody_isFinitePolytope
  rw [← he]
  exact isCompact_coordinatePolar hv hi

/-- All origin-symmetric finite polytopes with interior admit a finite strip presentation. -/
theorem finitePolytope_exists_strip_presentation {n : ℕ} {P : Set (Space n)}
    (hP : IsFinitePolytope P) (hK : IsSymmetricConvexBody P) :
    ∃ m : ℕ, ∃ rows : Fin m → Space n, P = stripBody rows := by
  classical
  obtain ⟨vertices, hv⟩ := coordinatePolar_isFinitePolytope hP hK.2.1 hK.2.2.2
  have he : P = coordinatePolar (vertices : Set (Space n)) := by
    calc
      P = coordinatePolar (coordinatePolar P) :=
        (coordinatePolar_bipolar hK.1.isClosed hK.2.1 (interior_subset hK.2.2.2)).symm
      _ = coordinatePolar (convexHull ℝ (vertices : Set (Space n))) := by rw [hv]
      _ = coordinatePolar (vertices : Set (Space n)) := coordinatePolar_convexHull _
  let e : Fin vertices.card ≃ vertices := vertices.equivFin.symm
  refine ⟨vertices.card, fun i => (e i).val, ?_⟩
  ext x
  constructor
  · intro hx i
    have hp := (he ▸ hx) (e i).val (e i).property
    have hm := (he ▸ hK.2.2.1 x hx) (e i).val (e i).property
    rw [dotProduct_comm] at hp
    rw [dotProduct_comm, dotProduct_neg] at hm
    exact abs_le.mpr ⟨by linarith, hp⟩
  · intro hx
    rw [he]
    intro v hv
    obtain ⟨i, hi⟩ := e.surjective ⟨v, hv⟩
    have h := (abs_le.mp (hx i)).2
    have hvi : (e i).val = v := congrArg Subtype.val hi
    change dotProduct (e i).val x ≤ 1 at h
    rw [hvi, dotProduct_comm] at h
    exact h

/-- Finite vertex input now reaches the proved a.e. simplicity layer directly. -/
theorem finitePolytope_exists_ae_simple_strips {n : ℕ} (hn : 1 ≤ n)
    {P : Set (Space n)} (hP : IsFinitePolytope P) (hK : IsSymmetricConvexBody P)
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ∃ m : ℕ, ∃ rows : Fin m → Space n,
      P = stripBody rows ∧ SignedIrredundant rows ∧
      ∀ᵐ X ∂volume.restrict P, ∀ c ∈ canonicalBasisIndices rows,
        NoExtraActive τ rows c.1 c.2 X := by
  obtain ⟨m, rows, he⟩ := finitePolytope_exists_strip_presentation hP hK
  obtain ⟨k, _, selected, hirr, _, hbody, hs⟩ :=
    exists_ae_simple_row_presentation hn hτ0 hτ1 rows (he ▸ hK.1)
  refine ⟨k, fun i => rows (selected i), he.trans hbody.symm, hirr, ?_⟩
  rwa [← he] at hs

end
end Funk
