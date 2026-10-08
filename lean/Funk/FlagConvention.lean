import Funk.PolytopeFlags
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Data.Fin.Tuple.Basic

/-! Add and remove the unique top face in a dimension-labelled geometric flag.
FVW section 2.2 includes dimensions 0,...,n. This file reconciles that indexing
convention using the same convex/extreme-face predicate. The face-predicate correspondence is completed separately in PolytopeExposed,
SupportingFlagConvention and HalfspaceFaceConvention. -/

open Set

namespace Funk
noncomputable section

theorem affineSpan_eq_top_of_zero_interior {n : ℕ} {P : Set (Space n)}
    (h0 : 0 ∈ interior P) : affineSpan ℝ P = ⊤ := by
  have ht : affineSpan ℝ (interior P) = ⊤ :=
    isOpen_interior.affineSpan_eq_top ⟨0, h0⟩
  exact top_unique (ht ▸ affineSpan_mono ℝ interior_subset)

theorem body_affine_dimension {n : ℕ} {P : Set (Space n)}
    (h0 : 0 ∈ interior P) : Module.finrank ℝ (affineSpan ℝ P).direction = n := by
  rw [affineSpan_eq_top_of_zero_interior h0, AffineSubspace.direction_top,
    finrank_top]
  exact Module.finrank_fin_fun ℝ

/-- Geometric flag including the full body as its n-dimensional final face. -/
structure FullFlagWithTop {n : ℕ} (P : Set (Space n)) where
  faces : Fin (n + 1) → Set (Space n)
  nonempty : ∀ i, (faces i).Nonempty
  convex : ∀ i, Convex ℝ (faces i)
  extreme : ∀ i, IsExtreme ℝ P (faces i)
  dimension : ∀ i, Module.finrank ℝ (affineSpan ℝ (faces i)).direction = i.val
  chain : StrictMono faces
  top : faces (Fin.last n) = P

theorem fullFlagWithTop_ext {n : ℕ} {P : Set (Space n)} {F G : FullFlagWithTop P}
    (h : F.faces = G.faces) : F = G := by
  cases F
  cases G
  cases h
  rfl

def fullFlagAppendTop {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) (F : FullFlag P) : FullFlagWithTop P where
  faces := Fin.snoc F.faces P
  nonempty := by
    intro i
    cases i using Fin.lastCases with
    | last => simpa using (show P.Nonempty from ⟨0, interior_subset hP.2.2.2⟩)
    | cast i => simpa using F.nonempty i
  convex := by
    intro i
    cases i using Fin.lastCases with
    | last => simpa using hP.2.1
    | cast i => simpa using F.convex i
  extreme := by
    intro i
    cases i using Fin.lastCases with
    | last => simpa using IsExtreme.refl ℝ P
    | cast i => simpa using F.extreme i
  dimension := by
    intro i
    cases i using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last]
      exact body_affine_dimension hP.2.2.2
    | cast i =>
      rw [Fin.snoc_castSucc]
      exact F.dimension i
  chain := by
    intro i j hij
    cases i using Fin.lastCases with
    | last => exact False.elim (by have := j.isLt; change n < j.val at hij; omega)
    | cast i =>
      cases j using Fin.lastCases with
      | last => simpa using F.proper i
      | cast j => simpa using F.chain (show i < j from hij)
  top := by simp

def fullFlagDropTop {n : ℕ} {P : Set (Space n)} (F : FullFlagWithTop P) :
    FullFlag P where
  faces := fun i => F.faces i.castSucc
  nonempty := fun i => F.nonempty i.castSucc
  convex := fun i => F.convex i.castSucc
  extreme := fun i => F.extreme i.castSucc
  proper := fun i => by simpa only [F.top] using F.chain i.castSucc_lt_last
  dimension := fun i => F.dimension i.castSucc
  chain := fun _ _ hij => F.chain hij

theorem fullFlagDropTop_append {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) (F : FullFlag P) :
    fullFlagDropTop (fullFlagAppendTop hP F) = F := by
  apply fullFlag_ext
  funext i
  simp only [fullFlagDropTop, fullFlagAppendTop, Fin.snoc_castSucc]

theorem fullFlagAppendTop_drop {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) (F : FullFlagWithTop P) :
    fullFlagAppendTop hP (fullFlagDropTop F) = F := by
  apply fullFlagWithTop_ext
  funext i
  cases i using Fin.lastCases with
  | last => simpa only [fullFlagAppendTop, Fin.snoc_last] using F.top.symm
  | cast i =>
    simp only [fullFlagAppendTop, fullFlagDropTop, Fin.snoc_castSucc]

def fullFlagWithTopEquiv {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) : FullFlag P ≃ FullFlagWithTop P where
  toFun := fullFlagAppendTop hP
  invFun := fullFlagDropTop
  left_inv := fullFlagDropTop_append hP
  right_inv := fullFlagAppendTop_drop hP

theorem fullFlagWithTop_finite {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P) :
    Finite (FullFlagWithTop P) := by
  let : Finite (FullFlag P) := fullFlag_finite hp
  exact Finite.of_injective (fullFlagWithTopEquiv hP).symm
    (fullFlagWithTopEquiv hP).symm.injective

theorem fullFlagWithTop_card_eq {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) : Nat.card (FullFlagWithTop P) = Nat.card (FullFlag P) :=
  Nat.card_congr (fullFlagWithTopEquiv hP).symm

end
end Funk
