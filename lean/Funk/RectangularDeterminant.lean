import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset

/-! A local rectangular determinant formula using the pinned Mathlib multilinear
row expansion. No external matrix representation or package is imported. -/

open Matrix Finset Function
open scoped BigOperators

namespace Funk
noncomputable section

/-- Expand the actual product matrix by multilinearity in its rows. -/
theorem rectangular_det_row_expansion {n m : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin n) R) :
    (A * B).det = ∑ f : Fin n → Fin m,
      (∏ i, A i (f i)) * (B.submatrix f id).det := by
  classical
  have h := (Matrix.detRowAlternating (R := R) (n := Fin n)).toMultilinearMap.map_sum
    (fun i j => A i j • B j)
  have hrows : (fun i => ∑ j, A i j • B j) = A * B := by
    ext i l
    simp [Matrix.mul_apply]
  rw [hrows] at h
  change (A * B).det = _ at h
  rw [h]
  apply Finset.sum_congr rfl
  intro f _
  exact (Matrix.detRowAlternating (R := R) (n := Fin n)).map_smul_univ
    (fun i => A i (f i)) (fun i => B (f i))

/-- Repeated selected rows contribute zero, in every dimension. -/
theorem selected_det_zero_of_not_injective {n m : ℕ} {R : Type*} [CommRing R]
    (B : Matrix (Fin m) (Fin n) R) {f : Fin n → Fin m}
    (hf : ¬Injective f) : (B.submatrix f id).det = 0 := by
  classical
  unfold Function.Injective at hf
  push Not at hf
  obtain ⟨i, j, he, hij⟩ := hf
  apply Matrix.det_zero_of_row_eq hij
  change B (f i) = B (f j)
  rw [he]

/-- An image fiber of injective selections is exactly the permutation fiber. -/
theorem sum_selected_image_eq_permutations {n m : ℕ} {R : Type*} [AddCommMonoid R]
    (S : Finset (Fin m)) (hS : S.card = n) (F : (Fin n → Fin m) → R) :
    (∑ f ∈ (Finset.univ.filter Injective).filter (fun f => Finset.univ.image f = S), F f) =
      ∑ σ : Equiv.Perm (Fin n), F (fun i => S.orderEmbOfFin hS (σ i)) := by
  classical
  let e := S.orderEmbOfFin hS
  have hei (x : Fin m) (hx : x ∈ S) :
      e ((S.orderIsoOfFin hS).symm ⟨x, hx⟩) = x :=
    congrArg Subtype.val ((S.orderIsoOfFin hS).apply_symm_apply ⟨x, hx⟩)
  symm
  refine Finset.sum_bij (fun σ _ => fun i => e (σ i)) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro σ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨e.injective.comp σ.injective, ?_⟩
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact S.orderEmbOfFin_mem hS (σ i)
    · intro hx
      exact ⟨σ.symm ((S.orderIsoOfFin hS).symm ⟨x, hx⟩), by
        simpa only [Equiv.apply_symm_apply] using hei x hx⟩
  · intro σ _ τ _ h
    exact Equiv.ext (fun i => e.injective (congrFun h i))
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    let p : Fin n → Fin n := fun i => (S.orderIsoOfFin hS).symm
      ⟨f i, by rw [← hf.2]; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
    have hep (i : Fin n) : e (p i) = f i := hei _ _
    have hp : Injective p := by
      intro i j h
      apply hf.1
      rw [← hep i, ← hep j, h]
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective p (Finite.injective_iff_bijective.mp hp)
    exact ⟨σ, Finset.mem_univ _, funext hep⟩

/-- Partition all injective selections by their increasing image. -/
theorem sum_injective_eq_subsets_permutations {n m : ℕ} {R : Type*} [AddCommMonoid R]
    (F : (Fin n → Fin m) → R) :
    (∑ f ∈ Finset.univ.filter Injective, F f) =
      ∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard n,
        if h : S.card = n then ∑ σ : Equiv.Perm (Fin n),
          F (fun i => S.orderEmbOfFin h (σ i)) else 0 := by
  classical
  have hm : ∀ f ∈ (Finset.univ : Finset (Fin n → Fin m)).filter Injective,
      Finset.univ.image f ∈ (Finset.univ : Finset (Fin m)).powersetCard n := by
    intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    simp [Finset.mem_powersetCard, Finset.card_image_of_injective _ hf]
  rw [← Finset.sum_fiberwise_of_maps_to hm F]
  apply Finset.sum_congr rfl
  intro S hS
  have hc : S.card = n := (Finset.mem_powersetCard.mp hS).2
  rw [dite_eq_left hc]
  exact sum_selected_image_eq_permutations S hc F

/-- A permutation fiber collapses to the two square minors. -/
theorem rectangular_det_permutation_fiber {n m : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin n) R)
    (e : Fin n → Fin m) :
    (∑ σ : Equiv.Perm (Fin n), (∏ i, A i (e (σ i))) *
      (B.submatrix (fun i => e (σ i)) id).det) =
      (A.submatrix id e).det * (B.submatrix e id).det := by
  classical
  have hr (σ : Equiv.Perm (Fin n)) :
      B.submatrix (fun i => e (σ i)) id = (B.submatrix e id).submatrix σ id := rfl
  simp_rw [hr, Matrix.det_permute]
  have hA : (A.submatrix id e).det = ∑ σ : Equiv.Perm (Fin n),
      (Equiv.Perm.sign σ : R) * ∏ i, A i (e (σ i)) := by
    rw [← Matrix.det_transpose (A.submatrix id e), Matrix.det_apply']
    rfl
  rw [hA, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  ring

/-- Cauchy--Binet over the exact finite, increasing image subsets. -/
theorem rectangular_det_eq_subset_minors {n m : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin n) R) :
    (A * B).det = ∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard n,
      if h : S.card = n then
        (A.submatrix id (S.orderEmbOfFin h)).det *
          (B.submatrix (S.orderEmbOfFin h) id).det else 0 := by
  classical
  rw [rectangular_det_row_expansion]
  calc
    _ = ∑ f ∈ Finset.univ.filter Injective,
        (∏ i, A i (f i)) * (B.submatrix f id).det := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro f _ hf
      have hn : ¬Injective f := by simpa using hf
      rw [selected_det_zero_of_not_injective B hn, mul_zero]
    _ = _ := by
      rw [sum_injective_eq_subsets_permutations]
      apply Finset.sum_congr rfl
      intro S hS
      simp only [dite_eq_left (Finset.mem_powersetCard.mp hS).2]
      exact rectangular_det_permutation_fiber A B _

/-- Increasing selections are the unique representatives of the n-element subsets. -/
theorem sum_subsets_eq_increasing_selections {n m : ℕ} {R : Type*} [AddCommMonoid R]
    (F : (Fin n → Fin m) → R) :
    (∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard n,
      if h : S.card = n then F (S.orderEmbOfFin h) else 0) =
      ∑ s ∈ Finset.univ.filter StrictMono, F s := by
  classical
  refine Finset.sum_bij (fun S hS => (S.orderEmbOfFin (Finset.mem_powersetCard.mp hS).2 :
    Fin n → Fin m)) ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (S.orderEmbOfFin (Finset.mem_powersetCard.mp hS).2).strictMono
  · intro S hS T hT he
    have h := congrArg (fun f : Fin n → Fin m => Finset.univ.image f) he
    simpa only [Finset.image_orderEmbOfFin_univ] using h
  · intro s hs
    have hm : StrictMono s := (Finset.mem_filter.mp hs).2
    let S := Finset.univ.image s
    have hc : S.card = n := by
      simp only [S, Finset.card_image_of_injective _ hm.injective, Finset.card_fin]
    have hS : S ∈ (Finset.univ : Finset (Fin m)).powersetCard n :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hc⟩
    refine ⟨S, hS, ?_⟩
    exact (S.orderEmbOfFin_unique hc (fun i =>
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩) hm).symm
  · intro S hS
    simp only [dite_eq_left (Finset.mem_powersetCard.mp hS).2]

/-- The rectangular determinant formula uses precisely increasing row selections. -/
theorem rectangular_det_eq_increasing_minors {n m : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin n) R) :
    (A * B).det = ∑ s ∈ Finset.univ.filter StrictMono,
      (A.submatrix id s).det * (B.submatrix s id).det := by
  rw [rectangular_det_eq_subset_minors]
  exact sum_subsets_eq_increasing_selections (fun s =>
    (A.submatrix id s).det * (B.submatrix s id).det)

end
end Funk
