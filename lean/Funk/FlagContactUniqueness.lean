import Funk.FlagContactClassification
import Funk.BoundaryFaces
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! At most one polar flag per primal flag has the standard contact code.
A surjective partial dot-coordinate map bounds the affine dimension of the contact set.
Only this uniqueness is needed for the one-sided sharp flag count; dual-flag existence is omitted. -/

open Set

namespace Funk
noncomputable section

/-- Retain any embedded set of coordinates after an invertible actual dot-coordinate map. -/
def partialBasisMap {n m : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (e : Fin m ↪ Fin n) :
    Space n →ₗ[ℝ] Space m :=
  LinearMap.pi (fun k => (LinearMap.proj (e k)).comp (basisMap Q).toLinearMap)

theorem partialBasisMap_apply {n m : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (e : Fin m ↪ Fin n) (q : Space n) (k : Fin m) :
    partialBasisMap Q e q k = dotProduct (Q (e k)) q := rfl

/-- A known inverse and extension of coordinates prove surjectivity, without rank search. -/
theorem partialBasisMap_surjective {n m : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.det ≠ 0) (e : Fin m ↪ Fin n) : Function.Surjective (partialBasisMap Q e) := by
  intro w
  obtain ⟨y, hy⟩ := (show Function.Surjective (fun y : Space n => fun k : Fin m => y (e k))
    from e.injective.surjective_comp_right) w
  refine ⟨basisMap Q⁻¹ y, ?_⟩
  ext k
  change basisMap Q (basisMap Q⁻¹ y) (e k) = w k
  rw [basisMap_inverse_right hQ]
  exact congrFun hy k

theorem partialBasisMap_ker_finrank {n m : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.det ≠ 0) (e : Fin m ↪ Fin n) :
    Module.finrank ℝ (LinearMap.ker (partialBasisMap Q e)) = n - m := by
  have h := (partialBasisMap Q e).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (partialBasisMap_surjective Q hQ e), finrank_top] at h
  simp only [Module.finrank_fin_fun] at h
  omega

/-- A nonempty set in one fibre has affine dimension at most the kernel dimension. -/
theorem affine_dimension_le_kernel_of_constant {n m : ℕ} (A : Space n →ₗ[ℝ] Space m)
    (C : Set (Space n)) (hn : C.Nonempty) (w : Space m) (hc : ∀ q ∈ C, A q = w) :
    Module.finrank ℝ (affineSpan ℝ C).direction ≤ Module.finrank ℝ (LinearMap.ker A) := by
  obtain ⟨q₀, hq₀⟩ := hn
  have hspan : affineSpan ℝ C ≤ AffineSubspace.mk' q₀ (LinearMap.ker A) := by
    apply affineSpan_le.mpr
    intro q hq
    change q ∈ AffineSubspace.mk' q₀ (LinearMap.ker A)
    rw [AffineSubspace.mem_mk']
    change A (q - q₀) = 0
    rw [map_sub, hc q hq, hc q₀ hq₀, sub_self]
  have hdim := Submodule.finrank_mono (AffineSubspace.direction_le hspan)
  change Module.finrank ℝ (affineSpan ℝ C).direction ≤
    Module.finrank ℝ (AffineSubspace.mk' q₀ (LinearMap.ker A)).direction at hdim
  rw [AffineSubspace.direction_mk'] at hdim
  exact hdim

/-- The contact set is specified entirely by the original primal flag. -/
def primalFlagContactSet {n : ℕ} {P : Set (Space n)} (F : FullFlagWithTop P)
    (i : Fin n) : Set (Space n) :=
  {q ∈ coordinatePolar P | ∀ k : Fin n, k.val + i.val < n → dotProduct (flagMatrix F k) q = 1}

/-- Standard contact propagates from the chosen polar point to its entire face. -/
theorem polar_flag_face_subset_contactSet {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P))
    (hc : FlagTriangularContactCode F G) (i : Fin n) :
    G.faces i.castSucc ⊆ primalFlagContactSet F i := by
  intro q hq
  refine ⟨(G.extreme i.castSucc).subset hq, ?_⟩
  intro k hk
  have he := (flagTriangularContactCode_iff_contacts hp hP F G).mp hc k.castSucc i
  have hb := he.mpr hk
  have h := polar_contact_on_face (G.extreme i.castSucc).subset
    (flagPoint_mem_polytope hP F k.castSucc)
    (flagPoint_mem_intrinsicInterior (coordinatePolar_isSymmetricConvexBody hp hP) G i.castSucc)
    hb q hq
  simpa only [flagMatrix, dotProduct_comm] using h

/-- The actual contact set has dimension at most the desired polar-face dimension. -/
theorem primalFlagContactSet_dimension_le {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) (F : FullFlagWithTop P) (i : Fin n)
    (hn : (primalFlagContactSet F i).Nonempty) :
    Module.finrank ℝ (affineSpan ℝ (primalFlagContactSet F i)).direction ≤ i.val := by
  let e : Fin (n - i.val) ↪ Fin n := ⟨fun k => ⟨k.val, lt_of_lt_of_le k.isLt (Nat.sub_le n i.val)⟩,
    fun _ _ h => Fin.ext (congrArg (fun x : Fin n => x.val) h)⟩
  have hc : ∀ q ∈ primalFlagContactSet F i, partialBasisMap (flagMatrix F) e q = 1 := by
    intro q hq
    ext k
    rw [partialBasisMap_apply]
    exact hq.2 (e k) (by have := k.isLt; have := i.isLt; change k.val + i.val < n; omega)
  have hd := affine_dimension_le_kernel_of_constant (partialBasisMap (flagMatrix F) e)
    (primalFlagContactSet F i) hn 1 hc
  rw [partialBasisMap_ker_finrank _ (flagMatrix_det_ne_zero hP F)] at hd
  have := i.isLt
  omega

/-- Equal dimensions force the polar face to be the contact set, without constructing a dual map. -/
theorem polar_flag_face_eq_contactSet {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P))
    (hc : FlagTriangularContactCode F G) (i : Fin n) :
    G.faces i.castSucc = primalFlagContactSet F i := by
  have hsub := polar_flag_face_subset_contactSet hp hP F G hc i
  have hdle := primalFlagContactSet_dimension_le hP F i ((G.nonempty i.castSucc).mono hsub)
  have hdge := Submodule.finrank_mono (AffineSubspace.direction_le (affineSpan_mono ℝ hsub))
  rw [G.dimension i.castSucc] at hdge
  apply face_eq_of_subset_of_dimension_eq (G.convex i.castSucc) (G.extreme i.castSucc)
    (G.nonempty i.castSucc) hsub (fun _ h => h.1)
  rw [G.dimension i.castSucc]
  exact le_antisymm hdge hdle

/-- The only counting input needed: for a fixed primal flag there is at most one standard polar flag. -/
theorem flagTriangularContactCode_unique {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G H : FullFlagWithTop (coordinatePolar P))
    (hG : FlagTriangularContactCode F G) (hH : FlagTriangularContactCode F H) : G = H := by
  apply fullFlagWithTop_ext
  funext k
  cases k using Fin.lastCases with
  | last => rw [G.top, H.top]
  | cast i => rw [polar_flag_face_eq_contactSet hp hP F G hG i,
      polar_flag_face_eq_contactSet hp hP F H hH i]

end
end Funk
