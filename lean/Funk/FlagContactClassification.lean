import Funk.TailSupportClassification
import Funk.PositiveColumnDecay

/-! Every actual pair has ordered upper-tail supports. Nonstandard contact codes decay.
This gives a classification by actual contact data, without assuming a geometric dual-flag map.
The separate claim that at most one polar flag per primal flag has the standard code is not proved here. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace Funk
noncomputable section

/-- Contact at a primal relative-interior point is contact on its entire primal face. -/
theorem primal_contact_on_face {n : ℕ} {P A : Set (Space n)}
    (hA : A ⊆ P) {q x : Space n} (hq : q ∈ coordinatePolar P)
    (hx : x ∈ intrinsicInterior ℝ A) (he : dotProduct q x = 1) :
    ∀ y ∈ A, dotProduct q y = 1 := by
  let f := (dotProductBilin ℝ ℝ q).toContinuousLinearMap
  exact functional_eq_on_set_of_intrinsicInterior f 1 (fun y hy => hq y (hA hy)) hx he

/-- Along a primal flag, contact also propagates to all earlier faces. -/
theorem primal_flag_contact_descends {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) (F : FullFlagWithTop P)
    {q : Space n} (hq : q ∈ coordinatePolar P) {k l : Fin (n + 1)} (hkl : k ≤ l)
    (he : dotProduct q (flagPoint F l) = 1) :
    dotProduct q (flagPoint F k) = 1 := by
  apply primal_contact_on_face (F.extreme l).subset hq
    (flagPoint_mem_intrinsicInterior hP F l) he
  exact F.chain.monotone hkl (flagPoint_mem_face hP F k)

/-- Actual column positivity persists at later primal vertices. -/
theorem flag_dual_positive_rows_monotone {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P))
    (i : Fin n) {k l : Fin (n + 1)} (hkl : k ≤ l)
    (hk : 0 < dualCoordinates (flagMatrix G) (flagPoint F k) i) :
    0 < dualCoordinates (flagMatrix G) (flagPoint F l) i := by
  by_contra hl
  have hz : dualCoordinates (flagMatrix G) (flagPoint F l) i = 0 :=
    le_antisymm (le_of_not_gt hl) (flag_dual_vertex_nonneg hp hP F G l i)
  have he : dotProduct (flagMatrix G i) (flagPoint F l) = 1 := by
    rw [dualCoordinates_component] at hz
    linarith
  have hd := primal_flag_contact_descends hP F
    (flagPoint_mem_polytope (coordinatePolar_isSymmetricConvexBody hp hP) G i.castSucc) hkl he
  change dotProduct (flagMatrix G i) (flagPoint F k) = 1 at hd
  rw [dualCoordinates_component, hd] at hk
  linarith

theorem flag_dual_positiveTailSupports {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) :
    PositiveTailSupports (fun k => dualCoordinates (flagMatrix G) (flagPoint F k)) :=
  fun i _ _ hkl hk => flag_dual_positive_rows_monotone hp hP F G i hkl hk

theorem flag_dual_top_positive {n : ℕ} {P : Set (Space n)}
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) (i : Fin n) :
    0 < dualCoordinates (flagMatrix G) (flagPoint F (Fin.last n)) i := by
  simp [flagPoint_top, dualCoordinates_component]

/-- Standard contact pattern, defined on the genuine flag vertices. -/
def FlagTriangularContactCode {n : ℕ} {P : Set (Space n)}
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) : Prop :=
  TriangularPositiveCode (fun k => dualCoordinates (flagMatrix G) (flagPoint F k))

/-- Each actual positive support is exactly a final interval of primal vertex indices. -/
theorem exists_flag_dual_support_cutoffs {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) :
    ∃ c : Fin n → Fin (n + 1), Antitone c ∧ ∀ k i,
      0 < dualCoordinates (flagMatrix G) (flagPoint F k) i ↔ c i ≤ k := by
  let V := fun k => dualCoordinates (flagMatrix G) (flagPoint F k)
  exact ⟨positiveSupportCutoff V (flag_dual_top_positive F G),
    supportCutoff_antitone V (flag_dual_top_positive F G)
      (fun _ _ hij => flag_dual_positive_supports_monotone hp hP F G hij),
    positive_iff_supportCutoff_le V (flag_dual_top_positive F G)
      (flag_dual_positiveTailSupports hp hP F G)⟩

/-- The standard support code is equivalent to the literal zero/contact triangle. -/
theorem flagTriangularContactCode_iff_contacts {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) :
    FlagTriangularContactCode F G ↔ ∀ k i,
      dotProduct (flagMatrix G i) (flagPoint F k) = 1 ↔ k.val + i.val < n := by
  constructor
  · intro hc k i
    have hc' := hc k i
    change 0 < dualCoordinates (flagMatrix G) (flagPoint F k) i ↔ n ≤ k.val + i.val at hc'
    have hn := flag_dual_vertex_nonneg hp hP F G k i
    rw [dualCoordinates_component] at hc' hn
    constructor
    · intro he
      have hnot : ¬ n ≤ k.val + i.val := fun h => by
        have hpos := hc'.mpr h
        rw [he] at hpos
        linarith
      omega
    · intro hlt
      have hnot : ¬ 0 < 1 - dotProduct (flagMatrix G i) (flagPoint F k) :=
        fun h => by have := hc'.mp h; omega
      linarith
  · intro hc k i
    change 0 < dualCoordinates (flagMatrix G) (flagPoint F k) i ↔ n ≤ k.val + i.val
    have hn := flag_dual_vertex_nonneg hp hP F G k i
    rw [dualCoordinates_component] at hn ⊢
    constructor
    · intro hpos
      by_contra hlt
      have he := (hc k i).mpr (by omega)
      rw [he] at hpos
      linarith
    · intro hge
      have hne : dotProduct (flagMatrix G i) (flagPoint F k) ≠ 1 :=
        fun h => by have := (hc k i).mp h; omega
      exact lt_of_le_of_ne hn (by intro hzero; apply hne; linarith)

/-- All actual nonstandard codes satisfy one of the two locally proved decay conditions. -/
theorem flag_degeneration_of_not_triangularContactCode {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P))
    (hc : ¬ FlagTriangularContactCode F G) :
    (∃ i j : Fin n, i ≠ j ∧
      positiveSupport (fun k => dualCoordinates (flagMatrix G) (flagPoint F k)) i =
      positiveSupport (fun k => dualCoordinates (flagMatrix G) (flagPoint F k)) j) ∨
      ∃ i : Fin n, ∀ k, 0 < dualCoordinates (flagMatrix G) (flagPoint F k) i :=
  degeneration_of_not_triangularPositiveCode _ (flag_dual_top_positive F G)
    (flag_dual_positiveTailSupports hp hP F G)
    (fun _ _ hij => flag_dual_positive_supports_monotone hp hP F G hij) hc

/-- No decay witness is supplied: nonstandard actual contact alone gives the degree bound. -/
theorem exists_dualFlag_integral_lower_degree_of_not_triangularCode
    {n : ℕ} {P : Set (Space (n + 1))}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P))
    (hc : ¬ FlagTriangularContactCode F G) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 0 < R →
      (∫⁻ u in dualFlagDomain (radius R) F G, dualProductKernel u) ≤
        ENNReal.ofReal (K * (R + Real.log 2) ^ n) := by
  rcases flag_degeneration_of_not_triangularContactCode hp hP F G hc with
    ⟨i, j, hij, hs⟩ | ⟨i, hv⟩
  · rcases Fin.eq_self_or_eq_succAbove i j with he | ⟨k, rfl⟩
    · exact False.elim (hij he.symm)
    · exact exists_dualFlag_integral_lower_degree_of_equal_support hp hP F G i k hs
  · exact exists_dualFlag_integral_lower_degree_of_positive_column hp hP F G i hv

/-- Every nonstandard actual pair has normalized contribution zero. -/
theorem tendsto_dualFlag_integral_not_triangularCode_ratio_zero
    {n : ℕ} {P : Set (Space (n + 1))}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P))
    (hc : ¬ FlagTriangularContactCode F G) :
    Tendsto (fun R : ℝ =>
      (∫⁻ u in dualFlagDomain (radius R) F G, dualProductKernel u).toReal /
        R ^ (n + 1)) atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨K, hK, hb⟩ := exists_dualFlag_integral_lower_degree_of_not_triangularCode hp hP F G hc
  exact tendsto_dualFlag_integral_ratio_zero_of_lower_degree hp hP F G hK hb

/-- Nonstandard actual pairs obey the zero-leading epsilon envelope at every large radius. -/
theorem dualFlag_integral_not_triangularCode_epsilon_upper
    {n : ℕ} {P : Set (Space (n + 1))}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P))
    (hc : ¬ FlagTriangularContactCode F G) {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      (∫⁻ u in dualFlagDomain (radius R) F G, dualProductKernel u) ≤
        ENNReal.ofReal (ε * R ^ (n + 1)) := by
  obtain ⟨K, _, hK⟩ := exists_dualFlag_integral_lower_degree_of_not_triangularCode hp hP F G hc
  obtain ⟨b, hb⟩ := eventually_atTop.mp (eventually_lower_degree_le n K (Real.log 2) hε)
  refine ⟨max b 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro R hR
  have h := hb R ((le_max_left _ _).trans hR)
  exact (hK R h.1).trans (ENNReal.ofReal_le_ofReal h.2)

/-- An unconditional classification of all actual pairs by contact code or zero contribution. -/
theorem flag_pair_triangularCode_or_decay {n : ℕ} {P : Set (Space (n + 1))}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) :
    FlagTriangularContactCode F G ∨
      Tendsto (fun R : ℝ =>
        (∫⁻ u in dualFlagDomain (radius R) F G, dualProductKernel u).toReal /
          R ^ (n + 1)) atTop (𝓝 (0 : ℝ)) := by
  classical
  by_cases hc : FlagTriangularContactCode F G
  · exact Or.inl hc
  · exact Or.inr (tendsto_dualFlag_integral_not_triangularCode_ratio_zero hp hP F G hc)

end
end Funk
