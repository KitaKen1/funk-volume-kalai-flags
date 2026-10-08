import Funk.PositiveSupportCertificate
import Mathlib.Data.Fin.Rev

/-! Actual polar-flag geometry supplies the support nesting required for positive scales.
This proves order-certificate existence for every actual flag pair. It does not identify
matching dual flags or prove the smaller leading contribution of different flag pairs. -/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

/-- Equality at a relative-interior maximizer propagates to the entire face. -/
theorem functional_eq_on_set_of_intrinsicInterior {n : ℕ} {A : Set (Space n)}
    (f : StrongDual ℝ (Space n)) (c : ℝ) (hb : ∀ y ∈ A, f y ≤ c)
    {x : Space n} (hx : x ∈ intrinsicInterior ℝ A) (he : f x = c) :
    ∀ y ∈ A, f y = c := by
  have hxA : x ∈ A := intrinsicInterior_subset hx
  have hxE : x ∈ f.toExposed A := ⟨hxA, fun y hy => (hb y hy).trans_eq he.symm⟩
  have hE := extreme_eq_of_intrinsicInterior_mem
    (ContinuousLinearMap.toExposed.isExposed (l := f) (A := A)).isExtreme hx hxE
  intro y hy
  have hyE : y ∈ f.toExposed A := hE.symm ▸ hy
  exact le_antisymm (hb y hy) (he ▸ hyE.2 x hxA)

/-- A polar contact at a relative-interior point is contact on the whole polar face. -/
theorem polar_contact_on_face {n : ℕ} {P A : Set (Space n)}
    (hA : A ⊆ coordinatePolar P) {x q : Space n} (hx : x ∈ P)
    (hq : q ∈ intrinsicInterior ℝ A) (he : dotProduct q x = 1) :
    ∀ y ∈ A, dotProduct y x = 1 := by
  let f := (dotProductBilin ℝ ℝ x).toContinuousLinearMap
  have hf (y : Space n) : f y = dotProduct y x := by
    change dotProduct x y = dotProduct y x
    exact dotProduct_comm _ _
  have hb : ∀ y ∈ A, f y ≤ 1 := fun y hy => (hf y).symm ▸ hA hy x hx
  have h := functional_eq_on_set_of_intrinsicInterior f 1 hb hq ((hf q).trans he)
  intro y hy
  exact (hf y).symm.trans (h y hy)

/-- Later polar faces can be in contact only if every earlier face is in contact. -/
theorem polar_flag_contact_descends {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (G : FullFlagWithTop (coordinatePolar P)) {x : Space n} (hx : x ∈ P)
    {i j : Fin n} (hij : i ≤ j)
    (he : dotProduct (flagMatrix G j) x = 1) :
    dotProduct (flagMatrix G i) x = 1 := by
  have hpolar := coordinatePolar_isSymmetricConvexBody hp hP
  apply polar_contact_on_face (G.extreme j.castSucc).subset hx
    (flagPoint_mem_intrinsicInterior hpolar G j.castSucc) he
  exact G.chain.monotone (show i.castSucc ≤ j.castSucc from hij)
    (flagPoint_mem_face hpolar G i.castSucc)

/-- Every actual unscaled flag vertex has nonnegative dual coordinates. -/
theorem flag_dual_vertex_nonneg {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P))
    (k : Fin (n + 1)) (i : Fin n) :
    0 ≤ dualCoordinates (flagMatrix G) (flagPoint F k) i := by
  rw [dualCoordinates_component]
  exact sub_nonneg.mpr
    (flagPoint_mem_polytope (coordinatePolar_isSymmetricConvexBody hp hP) G i.castSucc
      (flagPoint F k) (flagPoint_mem_polytope hP F k))

/-- In the original polar-face order, positive supports increase. -/
theorem flag_dual_positive_supports_monotone {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P))
    {i j : Fin n} (hij : i ≤ j) :
    positiveSupport (fun k => dualCoordinates (flagMatrix G) (flagPoint F k)) i ⊆
      positiveSupport (fun k => dualCoordinates (flagMatrix G) (flagPoint F k)) j := by
  intro k hk
  rw [mem_positiveSupport] at hk ⊢
  by_contra hj
  have hzero : dualCoordinates (flagMatrix G) (flagPoint F k) j = 0 :=
    le_antisymm (le_of_not_gt hj) (flag_dual_vertex_nonneg hp hP F G k j)
  have hcontact : dotProduct (flagMatrix G j) (flagPoint F k) = 1 := by
    rw [dualCoordinates_component] at hzero
    linarith
  have he := polar_flag_contact_descends hp hP G (flagPoint_mem_polytope hP F k) hij hcontact
  rw [dualCoordinates_component, he] at hk
  linarith

/-- Reversing the actual polar coordinates gives the required nested order. -/
theorem flag_dual_nested_supports_rev {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) :
    NestedPositiveSupports (fun k => dualCoordinates (flagMatrix G) (flagPoint F k)) Fin.revPerm := by
  intro i j hij
  exact flag_dual_positive_supports_monotone hp hP F G (Fin.rev_le_rev.mpr hij)

/-- The original geometric matrix, not a numerical substitute, admits positive scales. -/
theorem exists_flagOrderCertificate_rev {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) :
    ∃ a : Space n, (∀ i, 0 < a i) ∧ FlagOrderCertificate F G Fin.revPerm a := by
  exact exists_vertexOrderCertificate_of_nested _ (flag_dual_vertex_nonneg hp hP F G)
    Fin.revPerm (flag_dual_nested_supports_rev hp hP F G)

/-- Finite logarithms admit explicit symmetric bounds, including dimension zero. -/
theorem log_scale_bounds {n : ℕ} (a : Space n) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i, -B ≤ Real.log (a i) ∧ Real.log (a i) ≤ B := by
  classical
  refine ⟨∑ i, |Real.log (a i)|, Finset.sum_nonneg (fun i _ => abs_nonneg _), ?_⟩
  intro i
  have hsum := Finset.single_le_sum (fun j _ => abs_nonneg (Real.log (a j))) (Finset.mem_univ i)
  exact abs_le.mp hsum

/-- A fixed nonnegative additive constant controls every radius for each actual pair.
This gives one leading coefficient per pair, so it is not the sharp global FVW upper. -/
theorem exists_dualFlag_integral_ordered_upper {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      (∫⁻ u in dualFlagDomain (radius R) F G, dualProductKernel u) ≤
        ENNReal.ofReal ((R + C) ^ n / (n.factorial : ℝ) ^ 2) := by
  obtain ⟨a, ha, hc⟩ := exists_flagOrderCertificate_rev hp hP F G
  obtain ⟨B, hB, hb⟩ := log_scale_bounds a
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨Real.log 2 + B - (-B), by linarith, ?_⟩
  intro R hR
  simpa only [add_sub_assoc, add_assoc] using
    dualFlag_integral_le_ordered_certificate hp hP F G ha hc
    (fun i => (hb i).1) (fun i => (hb i).2) hR (by linarith)

end
end Funk
