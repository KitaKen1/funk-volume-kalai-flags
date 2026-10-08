import Funk.IntervalNormalization
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.SetTheory.Cardinal.Finite

/-! Exact enumeration of the actual face-chain type in dimension one.
The target specification is unchanged. -/

open Set

namespace Funk

noncomputable section

theorem fullFlag_ext {n : ℕ} {P : Set (Space n)} {F G : FullFlag P}
    (h : F.faces = G.faces) : F = G := by
  cases F
  cases G
  cases h
  rfl

theorem fullFlag_one_face_singleton {P : Set (Space 1)} (F : FullFlag P) :
    ∃ x : Space 1, F.faces 0 = {x} := by
  have hd : (affineSpan ℝ (F.faces 0)).direction = ⊥ := by
    apply Submodule.subsingleton_iff_eq_bot.mp
    exact Module.finrank_zero_iff.mp (F.dimension 0)
  have hs := AffineSubspace.direction_eq_bot_iff.mp hd
  obtain ⟨x, hx⟩ := F.nonempty 0
  refine ⟨x, ?_⟩
  apply Set.Subset.antisymm
  · intro y hy
    exact Set.mem_singleton_iff.mpr (hs (subset_affineSpan ℝ _ hy)
      (subset_affineSpan ℝ _ hx))
  · exact Set.singleton_subset_iff.mpr hx

theorem extremePoints_coordinateInterval {a b : ℝ} (hab : a ≤ b) :
    (coordinateInterval a b).extremePoints ℝ =
      {fun _ : Fin 1 => a, fun _ : Fin 1 => b} := by
  rw [coordinateInterval_eq_pi, extremePoints_pi]
  simp only [Set.extremePoints_Icc hab]
  ext x
  simp only [Set.mem_univ_pi, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hx
    rcases hx 0 with ha | hb
    · left
      funext i
      fin_cases i
      exact ha
    · right
      funext i
      fin_cases i
      exact hb
  · rintro (rfl | rfl) i <;> simp

/-- A flag supplied by a known endpoint; no vertex search is required. -/
def intervalEndpointFlag {a b : ℝ} (hab : a < b) (right : Bool) :
    FullFlag (coordinateInterval a b) where
  faces := fun _ => {fun _ : Fin 1 => if right then b else a}
  nonempty := fun _ => Set.singleton_nonempty _
  convex := fun _ => convex_singleton _
  extreme := by
    intro i
    rw [isExtreme_singleton, extremePoints_coordinateInterval hab.le]
    cases right <;> simp
  proper := by
    intro i
    apply Set.ssubset_iff_subset_ne.mpr
    constructor
    · apply Set.singleton_subset_iff.mpr
      cases right
      · exact ⟨le_rfl, hab.le⟩
      · exact ⟨hab.le, le_rfl⟩
    · intro h
      have hmem : (fun _ : Fin 1 => if right then a else b) ∈ coordinateInterval a b := by
        cases right
        · exact ⟨hab.le, le_rfl⟩
        · exact ⟨le_rfl, hab.le⟩
      rw [← h] at hmem
      have heq := congrFun (Set.mem_singleton_iff.mp hmem) 0
      cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] at heq
      · exact hab.ne' heq
      · exact hab.ne heq
  dimension := by
    intro i
    fin_cases i
    simp
  chain := by
    intro i j hij
    exact False.elim (by omega)

theorem fullFlag_interval_enumeration {a b : ℝ} (hab : a < b)
    (F : FullFlag (coordinateInterval a b)) :
    F = intervalEndpointFlag hab false ∨ F = intervalEndpointFlag hab true := by
  obtain ⟨x, hx⟩ := fullFlag_one_face_singleton F
  have he := F.extreme 0
  rw [hx, isExtreme_singleton, extremePoints_coordinateInterval hab.le] at he
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
  rcases he with ha | hb
  · left
    apply fullFlag_ext
    funext i
    fin_cases i
    simpa [intervalEndpointFlag, ha] using hx
  · right
    apply fullFlag_ext
    funext i
    fin_cases i
    simpa [intervalEndpointFlag, hb] using hx

theorem intervalEndpointFlag_ne {a b : ℝ} (hab : a < b) :
    intervalEndpointFlag hab false ≠ intervalEndpointFlag hab true := by
  intro h
  have he := congrArg (fun F => F.faces 0) h
  have he' : (fun _ : Fin 1 => a) = (fun _ : Fin 1 => b) := by
    simpa [intervalEndpointFlag] using he
  exact hab.ne (congrFun he' 0)

theorem fullFlag_interval_finite {a b : ℝ} (hab : a < b) :
    Finite (FullFlag (coordinateInterval a b)) := by
  have h : ({intervalEndpointFlag hab false, intervalEndpointFlag hab true} :
      Set (FullFlag (coordinateInterval a b))) = Set.univ := by
    ext F
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact fullFlag_interval_enumeration hab F
  exact Set.finite_univ_iff.mp (h ▸ (Set.finite_singleton _).insert _)

/-- Kalai's lower bound is sharp on each nondegenerate coordinate interval. -/
theorem fullFlag_interval_card {a b : ℝ} (hab : a < b) :
    Nat.card (FullFlag (coordinateInterval a b)) = 2 := by
  apply Nat.card_eq_two_iff.mpr
  refine ⟨intervalEndpointFlag hab false, intervalEndpointFlag hab true,
    intervalEndpointFlag_ne hab, ?_⟩
  ext F
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  exact fullFlag_interval_enumeration hab F

end
end Funk
