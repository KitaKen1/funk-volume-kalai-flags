import Funk.HalfspaceFaceConvention
import Mathlib.Logic.Equiv.Fin.Basic

/-! Relative-interior separation and an ordered affine-independence certificate.
These lemmas construct genuine flag simplices without assuming generic points.
-/

open Set Topology

namespace Funk
noncomputable section

/-- An extreme subset containing a relative-interior point contains the entire set. -/
theorem extreme_eq_of_intrinsicInterior_mem {n : ℕ} {P F : Set (Space n)}
    (he : IsExtreme ℝ P F) {x : Space n}
    (hxP : x ∈ intrinsicInterior ℝ P) (hxF : x ∈ F) : F = P := by
  obtain ⟨x', hx', rfl⟩ := hxP
  let : Nonempty (affineSpan ℝ P) := ⟨x'⟩
  apply Set.Subset.antisymm he.subset
  intro y hy
  let y' : affineSpan ℝ P := ⟨y, subset_affineSpan ℝ P hy⟩
  obtain ⟨t, ht, hzt⟩ :=
    (AffineMap.lineMap_continuous.tendsto' _ _
      (AffineMap.lineMap_apply_zero (k := ℝ) x' y')).eventually_mem
        (mem_interior_iff_mem_nhds.mp hx') |>.exists_lt
  let z : Space n := (AffineMap.lineMap x' y' t : affineSpan ℝ P)
  have hzP : z ∈ P := hzt
  have hz : z = (1 - t) • (x' : Space n) + t • y := by
    change ((affineSpan ℝ P).subtype (AffineMap.lineMap x' y' t)) = _
    rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module]
    rfl
  apply he.left_mem_of_mem_openSegment hy hzP hxF
  have hd : 0 < 1 - t := by linarith
  have hn : 0 < -t := neg_pos.mpr ht
  refine ⟨-t / (1 - t), 1 / (1 - t), div_pos hn hd, div_pos zero_lt_one hd, ?_, ?_⟩
  · field_simp [ne_of_gt hd]
    ring
  · rw [hz]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [ne_of_gt hd]
    ring

/-- A proper convex face's affine span misses every relative-interior point of its parent. -/
theorem intrinsicInterior_disjoint_face_affineSpan {n : ℕ} {P F : Set (Space n)}
    (hc : Convex ℝ F) (he : IsExtreme ℝ P F) (hp : F ⊂ P) :
    Disjoint (intrinsicInterior ℝ P) (affineSpan ℝ F : Set (Space n)) := by
  apply Set.disjoint_left.mpr
  intro x hx hxA
  have hxF : x ∈ F := by
    rw [← face_inter_affineSpan hc he]
    exact ⟨intrinsicInterior_subset hx, hxA⟩
  exact hp.ne (extreme_eq_of_intrinsicInterior_mem he hx hxF)

/-- A sequential affine-span certificate, reusable for known point lists. -/
theorem affineIndependent_of_ordered_notMem {n m : ℕ} (p : Fin m → Space n)
    (hp : ∀ i, p i ∉ affineSpan ℝ (p '' {j | j < i})) : AffineIndependent ℝ p := by
  induction m with
  | zero => exact affineIndependent_of_subsingleton ℝ p
  | succ m ih =>
    let q : Fin m → Space n := fun i => p i.castSucc
    have hq : AffineIndependent ℝ q := by
      apply ih q
      intro i hi
      apply hp i.castSucc
      apply affineSpan_mono ℝ _ hi
      rintro _ ⟨j, hj, rfl⟩
      exact ⟨j.castSucc, hj, rfl⟩
    have hrest : AffineIndependent ℝ (fun j : {j : Fin (m + 1) // j ≠ Fin.last m} => p j) := by
      apply (affineIndependent_equiv (k := ℝ) (finSuccAboveEquiv (Fin.last m))).mp
      simpa [q, Function.comp_def, finSuccAboveEquiv_apply, Fin.succAbove_last] using hq
    apply hrest.affineIndependent_of_notMem_span
    intro hmem
    apply hp (Fin.last m)
    apply affineSpan_mono ℝ _ hmem
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨j, Fin.lt_last_iff_ne_last.mpr hj, rfl⟩

end
end Funk
