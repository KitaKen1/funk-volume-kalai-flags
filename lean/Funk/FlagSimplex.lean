import Funk.FlagInterior
import Funk.SimplexCertificate
import Mathlib.LinearAlgebra.Matrix.Nonsingular

/-! One coherent point per actual face, with the origin on the top face.
Every actual complete flag gives a nondegenerate full-dimensional simplex.
This does not yet prove that the collection covers P or is a triangulation. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

/-- The choice depends on the geometric face, not on the flag containing it. -/
def faceInteriorPoint {n : ℕ} {P : Set (Space n)} (F : PolytopeFace P) : Space n := by
  classical
  exact if F.val = P then 0 else if hn : F.val.Nonempty then
    Classical.choose (hn.intrinsicInterior F.property.1) else 0

theorem faceInteriorPoint_mem_intrinsicInterior {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) (F : PolytopeFace P) (hn : F.val.Nonempty) :
    faceInteriorPoint F ∈ intrinsicInterior ℝ F.val := by
  classical
  by_cases ht : F.val = P
  · simp only [faceInteriorPoint, ite_eq_left ht]
    rw [ht]
    exact interior_subset_intrinsicInterior hP.2.2.2
  · simp only [faceInteriorPoint, ite_eq_right ht, dite_eq_left hn]
    exact Classical.choose_spec (hn.intrinsicInterior F.property.1)

theorem faceInteriorPoint_eq_zero_of_top {n : ℕ} {P : Set (Space n)}
    (F : PolytopeFace P) (ht : F.val = P) : faceInteriorPoint F = 0 := by
  simp [faceInteriorPoint, ht]

/-- A complete geometric flag uses the common face choices. -/
def flagPoint {n : ℕ} {P : Set (Space n)} (F : FullFlagWithTop P)
    (i : Fin (n + 1)) : Space n :=
  faceInteriorPoint ⟨F.faces i, F.convex i, F.extreme i⟩

theorem flagPoint_mem_intrinsicInterior {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) (F : FullFlagWithTop P) (i : Fin (n + 1)) :
    flagPoint F i ∈ intrinsicInterior ℝ (F.faces i) :=
  faceInteriorPoint_mem_intrinsicInterior hP
    ⟨F.faces i, F.convex i, F.extreme i⟩ (F.nonempty i)

theorem flagPoint_mem_face {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) (F : FullFlagWithTop P) (i : Fin (n + 1)) :
    flagPoint F i ∈ F.faces i :=
  intrinsicInterior_subset (flagPoint_mem_intrinsicInterior hP F i)

theorem flagPoint_mem_polytope {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) (F : FullFlagWithTop P) (i : Fin (n + 1)) :
    flagPoint F i ∈ P := (F.extreme i).subset (flagPoint_mem_face hP F i)

theorem flagPoint_top {n : ℕ} {P : Set (Space n)} (F : FullFlagWithTop P) :
    flagPoint F (Fin.last n) = 0 :=
  faceInteriorPoint_eq_zero_of_top _ F.top

/-- Flags sharing a face use exactly the same point there. -/
theorem flagPoint_eq_of_face_eq {n : ℕ} {P : Set (Space n)}
    (F G : FullFlagWithTop P) (i j : Fin (n + 1)) (h : F.faces i = G.faces j) :
    flagPoint F i = flagPoint G j := by
  unfold flagPoint
  congr 1
  exact Subtype.ext h

theorem flagPoint_notMem_earlier_affineSpan {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) (F : FullFlagWithTop P)
    {i j : Fin (n + 1)} (hij : i < j) :
    flagPoint F j ∉ affineSpan ℝ (F.faces i) := by
  have he : IsExtreme ℝ (F.faces j) (F.faces i) :=
    (F.extreme i).mono (F.extreme j).subset (F.chain hij).subset
  exact Set.disjoint_left.mp
    (intrinsicInterior_disjoint_face_affineSpan (F.convex i) he (F.chain hij))
      (flagPoint_mem_intrinsicInterior hP F j)

/-- The face dimensions and intrinsic-interior choices force affine independence. -/
theorem flagPoints_affineIndependent {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) (F : FullFlagWithTop P) :
    AffineIndependent ℝ (flagPoint F) := by
  apply affineIndependent_of_ordered_notMem
  intro i hi
  by_cases hi0 : i = 0
  · subst i
    simp only [Fin.not_lt_zero, Set.ofPred_false, Set.image_empty, AffineSubspace.span_empty] at hi
    exact hi
  have hpos : 0 < i.val := by
    have hne : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
    omega
  let j : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  have hji : j < i := by change i.val - 1 < i.val; omega
  apply flagPoint_notMem_earlier_affineSpan hP F hji
  apply affineSpan_mono ℝ _ hi
  rintro _ ⟨k, hk, rfl⟩
  have hkj : k ≤ j := by change k.val ≤ i.val - 1; have hk' : k.val < i.val := hk; omega
  exact F.chain.monotone hkj (flagPoint_mem_face hP F k)

/-- Proper flag points as rows; the omitted top point is exactly zero. -/
def flagMatrix {n : ℕ} {P : Set (Space n)} (F : FullFlagWithTop P) :
    Matrix (Fin n) (Fin n) ℝ := fun i => flagPoint F i.castSucc

theorem flagMatrix_linearIndependent {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) (F : FullFlagWithTop P) :
    LinearIndependent ℝ (flagMatrix F) := by
  have ha := (affineIndependent_iff_linearIndependent_vsub ℝ (flagPoint F) (Fin.last n)).mp
    (flagPoints_affineIndependent hP F)
  have hc := ha.comp (finSuccAboveEquiv (Fin.last n)) (finSuccAboveEquiv (Fin.last n)).injective
  simpa [flagMatrix, finSuccAboveEquiv_apply, Fin.succAbove_last, flagPoint_top,
    vsub_eq_sub, Function.comp_def] using! hc

theorem flagMatrix_det_ne_zero {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) (F : FullFlagWithTop P) : (flagMatrix F).det ≠ 0 :=
  Matrix.nonsingular_iff_det_ne_zero.mp
    (Matrix.Nonsingular.of_linearIndependent_row (flagMatrix_linearIndependent hP F))

/-- The actual simplex in the original coordinate space. -/
def flagSimplex {n : ℕ} {P : Set (Space n)} (F : FullFlagWithTop P) : Set (Space n) :=
  convexHull ℝ (Set.range (flagPoint F))

theorem flagSimplex_eq_rowSimplex {n : ℕ} {P : Set (Space n)} (F : FullFlagWithTop P) :
    flagSimplex F = rowSimplex (flagMatrix F) := by
  unfold flagSimplex rowSimplex
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    cases i using Fin.lastCases with
    | last =>
      rw [flagPoint_top]
      exact Set.mem_insert 0 _
    | cast i => exact Set.mem_insert_of_mem _ ⟨i, rfl⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨Fin.last n, flagPoint_top F⟩
    · exact ⟨i.castSucc, rfl⟩

theorem flagSimplex_subset_polytope {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) (F : FullFlagWithTop P) : flagSimplex F ⊆ P :=
  convexHull_min (Set.range_subset_iff.mpr (flagPoint_mem_polytope hP F)) hP.2.1

theorem flagSimplex_isCompact {n : ℕ} {P : Set (Space n)} (F : FullFlagWithTop P) :
    IsCompact (flagSimplex F) := (Set.finite_range _).isCompact_convexHull ℝ

theorem volume_flagSimplex {n : ℕ} {P : Set (Space n)} (F : FullFlagWithTop P) :
    volume (flagSimplex F) = ENNReal.ofReal (|(flagMatrix F).det| / (n.factorial : ℝ)) := by
  rw [flagSimplex_eq_rowSimplex, volume_rowSimplex]

theorem volume_flagSimplex_pos {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) (F : FullFlagWithTop P) :
    0 < volume (flagSimplex F) := by
  rw [volume_flagSimplex]
  exact ENNReal.ofReal_pos.mpr (div_pos (abs_pos.mpr (flagMatrix_det_ne_zero hP F))
    (Nat.cast_pos.mpr (Nat.factorial_pos n)))

theorem volume_flagSimplex_finite {n : ℕ} {P : Set (Space n)} (F : FullFlagWithTop P) :
    volume (flagSimplex F) < ⊤ := by
  rw [volume_flagSimplex]
  exact ENNReal.ofReal_lt_top

end
end Funk
