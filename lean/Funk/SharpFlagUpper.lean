import Funk.FlagContactUniqueness

/-! The actual frozen Funk integral has the sharp one-sided flag-count coefficient.
Only uniqueness of standard polar contact codes and decay of all other pairs are required.
No dual-flag existence, disjoint triangulation, two-term expansion, or lower Funk bound is input. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace Funk
noncomputable section

/-- A predicate true at most once contributes at most one leading coefficient. -/
theorem sum_unique_predicate_coeff_le {γ : Type*} [Fintype γ] (p : γ → Prop) [DecidablePred p]
    (hp : ∀ g h, p g → p h → g = h) {a : ℝ} (ha : 0 ≤ a) (δ : ℝ) :
    (∑ g : γ, if p g then a + δ else δ) ≤ a + (Fintype.card γ : ℝ) * δ := by
  classical
  have hc : (Finset.univ.filter p).card ≤ 1 := Finset.card_le_one.mpr (by
    intro g hg h hh
    exact hp g h (Finset.mem_filter.mp hg).2 (Finset.mem_filter.mp hh).2)
  have hs : (∑ g : γ, if p g then a else 0) = ((Finset.univ.filter p).card : ℝ) * a := by
    rw [← Finset.sum_filter]
    simp
  have he : (∑ g : γ, if p g then a + δ else δ) =
      (∑ g : γ, if p g then a else 0) + ∑ _ : γ, δ := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro g _
    by_cases hg : p g <;> simp [hg]
  rw [he, hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc' : ((Finset.univ.filter p).card : ℝ) ≤ 1 := by exact_mod_cast hc
  nlinarith

/-- Apply the at-most-one estimate separately to every first index. -/
theorem sum_pair_unique_coeff_le {φ γ : Type*} [Fintype φ] [Fintype γ]
    (p : φ → γ → Prop) [DecidableRel p] (hp : ∀ f g h, p f g → p f h → g = h)
    {a : ℝ} (ha : 0 ≤ a) (δ : ℝ) :
    (∑ f : φ, ∑ g : γ, if p f g then a + δ else δ) ≤
      (Fintype.card φ : ℝ) * (a + (Fintype.card γ : ℝ) * δ) := by
  calc
    _ ≤ ∑ _ : φ, (a + (Fintype.card γ : ℝ) * δ) :=
      Finset.sum_le_sum (fun f _ => sum_unique_predicate_coeff_le (p f) (hp f) ha δ)
    _ = _ := by simp; ring

/-- The original actual volume has the sharp leading epsilon upper for every large radius. -/
theorem funkVolume_radius_eventually_le_flag_coefficient
    {n : ℕ} {P : Set (Space (n + 1))}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, 0 < R ∧ funkVolume P (radius R) ≤
      ENNReal.ofReal (((Nat.card (FullFlag P) : ℝ) / ((n + 1).factorial : ℝ) ^ 2 + ε) *
        R ^ (n + 1)) := by
  classical
  let : Finite (FullFlagWithTop P) := fullFlagWithTop_finite hp hP
  let : Fintype (FullFlagWithTop P) := Fintype.ofFinite (FullFlagWithTop P)
  let : Finite (FullFlagWithTop (coordinatePolar P)) := fullFlagWithTop_finite
    (coordinatePolar_isFinitePolytope hp hP.2.1 hP.2.2.2)
    (coordinatePolar_isSymmetricConvexBody hp hP)
  let : Fintype (FullFlagWithTop (coordinatePolar P)) := Fintype.ofFinite (FullFlagWithTop (coordinatePolar P))
  let a : ℝ := 1 / ((n + 1).factorial : ℝ) ^ 2
  let m : ℝ := (Fintype.card (FullFlagWithTop P) : ℝ) *
    (Fintype.card (FullFlagWithTop (coordinatePolar P)) : ℝ)
  let δ : ℝ := ε / (m + 1)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hδ : 0 < δ := div_pos hε (by linarith)
  let c := fun (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) =>
    if FlagTriangularContactCode F G then a + δ else δ
  have hc (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) : 0 ≤ c F G := by
    dsimp [c]
    split_ifs <;> linarith
  have hpair (F : FullFlagWithTop P) (G : FullFlagWithTop (coordinatePolar P)) :
      ∀ᶠ R : ℝ in atTop, 0 < R ∧
        (∫⁻ u in dualFlagDomain (radius R) F G, dualProductKernel u) ≤
          ENNReal.ofReal (c F G * R ^ (n + 1)) := by
    by_cases hcode : FlagTriangularContactCode F G
    · simpa only [c, hcode, ite_true, a] using
        dualFlag_integral_eventually_le_leading hp hP F G hδ
    · obtain ⟨R₀, hR₀, hb⟩ := dualFlag_integral_not_triangularCode_epsilon_upper hp hP F G hcode hδ
      filter_upwards [eventually_ge_atTop R₀] with R hR
      exact ⟨hR₀.trans_le hR, by simpa only [c, hcode, ite_false] using hb R hR⟩
  have hall : ∀ᶠ R : ℝ in atTop, ∀ F : FullFlagWithTop P,
      ∀ G : FullFlagWithTop (coordinatePolar P), 0 < R ∧
        (∫⁻ u in dualFlagDomain (radius R) F G, dualProductKernel u) ≤
          ENNReal.ofReal (c F G * R ^ (n + 1)) :=
    eventually_all.mpr (fun F => eventually_all.mpr (fun G => hpair F G))
  have hsum : (∑ F : FullFlagWithTop P, ∑ G : FullFlagWithTop (coordinatePolar P), c F G) ≤
      (Fintype.card (FullFlagWithTop P) : ℝ) * a + ε := by
    have hb := sum_pair_unique_coeff_le FlagTriangularContactCode
      (flagTriangularContactCode_unique hp hP) ha δ
    have he : δ * (m + 1) = ε := by
      dsimp [δ]
      field_simp [show m + 1 ≠ 0 by linarith]
    have hdm : δ * m ≤ ε := by nlinarith
    have hbound : (Fintype.card (FullFlagWithTop P) : ℝ) *
        (a + (Fintype.card (FullFlagWithTop (coordinatePolar P)) : ℝ) * δ) ≤
        (Fintype.card (FullFlagWithTop P) : ℝ) * a + ε := by
      dsimp [m] at hdm
      nlinarith
    exact hb.trans hbound
  have hcount : (Fintype.card (FullFlagWithTop P) : ℝ) = (Nat.card (FullFlag P) : ℝ) := by
    congr 1
    rw [← Nat.card_eq_fintype_card, fullFlagWithTop_card_eq hP]
  filter_upwards [hall, eventually_gt_atTop (0 : ℝ)] with R hR hRpos
  refine ⟨hRpos, ?_⟩
  calc
    funkVolume P (radius R) ≤ ∑ F : FullFlagWithTop P,
        ∑ G : FullFlagWithTop (coordinatePolar P),
          ∫⁻ u in dualFlagDomain (radius R) F G, dualProductKernel u :=
      funkVolume_radius_le_dualFlag_integrals hp hP hRpos
    _ ≤ ∑ F : FullFlagWithTop P, ∑ G : FullFlagWithTop (coordinatePolar P),
        ENNReal.ofReal (c F G * R ^ (n + 1)) :=
      Finset.sum_le_sum (fun F _ => Finset.sum_le_sum (fun G _ => (hR F G).2))
    _ = ENNReal.ofReal ((∑ F : FullFlagWithTop P,
        ∑ G : FullFlagWithTop (coordinatePolar P), c F G) * R ^ (n + 1)) := by
      have hi (F : FullFlagWithTop P) : (∑ G : FullFlagWithTop (coordinatePolar P),
          ENNReal.ofReal (c F G * R ^ (n + 1))) =
          ENNReal.ofReal (∑ G : FullFlagWithTop (coordinatePolar P), c F G * R ^ (n + 1)) :=
        (ENNReal.ofReal_sum_of_nonneg (fun G _ => mul_nonneg (hc F G) (pow_nonneg hRpos.le _))).symm
      simp_rw [hi]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun F _ =>
        Finset.sum_nonneg (fun G _ => mul_nonneg (hc F G) (pow_nonneg hRpos.le _)))]
      congr 1
      simp only [Finset.sum_mul]
    _ ≤ ENNReal.ofReal (((Nat.card (FullFlag P) : ℝ) / ((n + 1).factorial : ℝ) ^ 2 + ε) *
        R ^ (n + 1)) := by
      apply ENNReal.ofReal_le_ofReal
      have hb := mul_le_mul_of_nonneg_right hsum (pow_nonneg hRpos.le (n + 1))
      simpa only [hcount, a, mul_one_div] using hb

/-- A common positive threshold works for every larger radius of the actual polytope. -/
theorem funkVolume_radius_flag_epsilon_upper {n : ℕ} {P : Set (Space (n + 1))}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P) {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → funkVolume P (radius R) ≤
      ENNReal.ofReal (((Nat.card (FullFlag P) : ℝ) / ((n + 1).factorial : ℝ) ^ 2 + ε) *
        R ^ (n + 1)) := by
  obtain ⟨b, hb⟩ := eventually_atTop.mp (funkVolume_radius_eventually_le_flag_coefficient hp hP hε)
  refine ⟨max b 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro R hR
  exact (hb R ((le_max_left _ _).trans hR)).2

/-- The exact frozen FVW one-sided specification now has a proof. -/
theorem finitePolytope_fvwEpsilonUpper {n : ℕ} {P : Set (Space (n + 1))}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P) : FVWEpsilonUpper P := by
  intro ε hε
  obtain ⟨R₀, hR₀, hb⟩ := funkVolume_radius_flag_epsilon_upper hp hP hε
  exact ⟨R₀, hR₀, hb R₀ le_rfl⟩

/-- All positive dimensions, retaining actual geometry, actual radius and actual flag count. -/
theorem finitePolytope_fvwEpsilonUpper_of_pos_dimension {n : ℕ} (hn : 1 ≤ n)
    {P : Set (Space n)} (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P) :
    FVWEpsilonUpper P := by
  cases n with
  | zero => omega
  | succ n => exact finitePolytope_fvwEpsilonUpper hp hP

/-- Kalai now requires only the actual Funk lower theorem, with no FVW input. -/
theorem kalaiFullFlagsGoal_of_funk (funk : FunkLowerBoundGoal) : KalaiFullFlagsGoal := by
  apply kalaiFullFlagsGoal_of_funk_and_fvw_upper funk
  intro n hn P hp hP
  exact finitePolytope_fvwEpsilonUpper_of_pos_dimension hn hp hP

/-- Both frozen goals now require only the still-open actual boundary probability cover. -/
theorem funkAndKalaiGoals_of_irredundant_covers
    (cover : ∀ (n : ℕ), 1 ≤ n → ∀ (m : ℕ) (rows : Fin m → Space n),
      SignedIrredundant rows → IsSymmetricConvexBody (stripBody rows) →
      ∀ τ : ℝ, 0 < τ → τ < 1 →
        1 ≤ ∑ k ∈ canonicalBasisIndices rows, lensBoundaryRows n τ
          (basisBoundaryEvent τ k.2 (fun i => rows (k.1 i))
            (basisFeasibleRegion τ rows k.1 k.2))) :
    FunkLowerBoundGoal ∧ KalaiFullFlagsGoal := by
  have funk := funkLowerBoundGoal_of_irredundant_covers cover
  exact ⟨funk, kalaiFullFlagsGoal_of_funk funk⟩

end
end Funk
