import Funk.PolytopeExposed
import Funk.KalaiFunk

/-! Supporting closed-halfspace faces, including the conventional empty/full faces,
and their dimension-labelled flags. The geometric sets are unchanged when
converting to the frozen convex/extreme flag type. -/

open Set Topology Filter

namespace Funk
noncomputable section

/-- Face cut out by a supporting halfspace; empty and full faces are included separately. -/
def IsSupportingFace {n : ℕ} (P F : Set (Space n)) : Prop :=
  F = ∅ ∨ F = P ∨ ∃ (l : StrongDual ℝ (Space n)) (c : ℝ),
    l ≠ 0 ∧ (∀ y ∈ P, l y ≤ c) ∧ F = {x ∈ P | l x = c}

theorem supportingFace_isExposed {n : ℕ} {P F : Set (Space n)}
    (h : IsSupportingFace P F) : IsExposed ℝ P F := by
  rcases h with rfl | rfl | ⟨l, c, _, hbound, hF⟩
  · exact isExposed_empty
  · exact IsExposed.refl _
  · intro hn
    obtain ⟨x, hx⟩ := hn
    rw [hF] at hx
    refine ⟨l, ?_⟩
    rw [hF]
    ext z
    constructor
    · rintro ⟨hz, heq⟩
      exact ⟨hz, fun y hy => (hbound y hy).trans_eq heq.symm⟩
    · rintro ⟨hz, hmax⟩
      exact ⟨hz, le_antisymm (hbound z hz) (hx.2 ▸ hmax x hx.1)⟩

theorem exposed_isSupportingFace {n : ℕ} {P F : Set (Space n)}
    (h : IsExposed ℝ P F) : IsSupportingFace P F := by
  obtain rfl | hn := F.eq_empty_or_nonempty
  · exact Or.inl rfl
  obtain ⟨l, hl⟩ := h hn
  obtain ⟨x, hx⟩ := hn
  have hx' : x ∈ P ∧ ∀ y ∈ P, l y ≤ l x := by rwa [hl] at hx
  have hF : F = {z ∈ P | l z = l x} := by
    rw [hl]
    ext z
    constructor
    · rintro ⟨hz, hmax⟩
      exact ⟨hz, le_antisymm (hx'.2 z hz) (hmax x hx'.1)⟩
    · rintro ⟨hz, heq⟩
      exact ⟨hz, fun y hy => (hx'.2 y hy).trans_eq heq.symm⟩
  by_cases hl0 : l = 0
  · exact Or.inr (Or.inl (by simpa [hl0] using hF))
  · exact Or.inr (Or.inr ⟨l, l x, hl0, hx'.2, hF⟩)

/-- Nonempty proper faces necessarily admit a nonzero supporting functional. -/
theorem polytopeFace_nonzero_support {n : ℕ} {P F : Set (Space n)}
    (hP : IsFinitePolytope P) (hc : Convex ℝ F) (he : IsExtreme ℝ P F)
    (hn : F.Nonempty) (hp : F ≠ P) :
    ∃ (l : StrongDual ℝ (Space n)) (c : ℝ),
      l ≠ 0 ∧ (∀ y ∈ P, l y ≤ c) ∧ F = {x ∈ P | l x = c} := by
  rcases exposed_isSupportingFace (polytopeFace_isExposed hP hc he) with h | h | h
  · exact False.elim (hn.ne_empty h)
  · exact False.elim (hp h)
  · exact h

theorem finitePolytope_face_iff_supporting {n : ℕ} {P F : Set (Space n)}
    (hP : IsFinitePolytope P) :
    (Convex ℝ F ∧ IsExtreme ℝ P F) ↔ IsSupportingFace P F :=
  (finitePolytope_face_iff_exposed hP).trans
    ⟨exposed_isSupportingFace, supportingFace_isExposed⟩

/-- FVW-style flag: dimensions0,...,n, supporting faces, and the unique full face. -/
structure SupportingFullFlag {n : ℕ} (P : Set (Space n)) where
  faces : Fin (n + 1) → Set (Space n)
  nonempty : ∀ i, (faces i).Nonempty
  supporting : ∀ i, IsSupportingFace P (faces i)
  dimension : ∀ i, Module.finrank ℝ (affineSpan ℝ (faces i)).direction = i.val
  chain : StrictMono faces
  top : faces (Fin.last n) = P

theorem supportingFullFlag_ext {n : ℕ} {P : Set (Space n)}
    {F G : SupportingFullFlag P} (h : F.faces = G.faces) : F = G := by
  cases F
  cases G
  cases h
  rfl

def fullFlagWithTopToSupporting {n : ℕ} {P : Set (Space n)}
    (hP : IsFinitePolytope P) (F : FullFlagWithTop P) : SupportingFullFlag P where
  faces := F.faces
  nonempty := F.nonempty
  supporting := fun i => (finitePolytope_face_iff_supporting hP).mp ⟨F.convex i, F.extreme i⟩
  dimension := F.dimension
  chain := F.chain
  top := F.top

def supportingToFullFlagWithTop {n : ℕ} {P : Set (Space n)}
    (hP : IsFinitePolytope P) (F : SupportingFullFlag P) : FullFlagWithTop P where
  faces := F.faces
  nonempty := F.nonempty
  convex := fun i => ((finitePolytope_face_iff_supporting hP).mpr (F.supporting i)).1
  extreme := fun i => ((finitePolytope_face_iff_supporting hP).mpr (F.supporting i)).2
  dimension := F.dimension
  chain := F.chain
  top := F.top

def fullFlagWithTopSupportingEquiv {n : ℕ} {P : Set (Space n)}
    (hP : IsFinitePolytope P) : FullFlagWithTop P ≃ SupportingFullFlag P where
  toFun := fullFlagWithTopToSupporting hP
  invFun := supportingToFullFlagWithTop hP
  left_inv := fun _ => fullFlagWithTop_ext rfl
  right_inv := fun _ => supportingFullFlag_ext rfl

/-- Exact convention equivalence, including both the face predicate and the top face. -/
def fullFlagSupportingEquiv {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P) :
    FullFlag P ≃ SupportingFullFlag P :=
  (fullFlagWithTopEquiv hP).trans (fullFlagWithTopSupportingEquiv hp)

theorem supportingFullFlag_finite {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P) :
    Finite (SupportingFullFlag P) :=
  let : Finite (FullFlag P) := fullFlag_finite hp
  Finite.of_equiv _ (fullFlagSupportingEquiv hp hP)

theorem supportingFullFlag_card_eq {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P) :
    Nat.card (SupportingFullFlag P) = Nat.card (FullFlag P) :=
  (Nat.card_congr (fullFlagSupportingEquiv hp hP)).symm

/-- FVW's supporting-face flag count gives the identical actual epsilon-upper specification. -/
theorem fvwEpsilonUpper_iff_supportingFlag_upper {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P) :
    FVWEpsilonUpper P ↔ ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      funkVolume P (radius R) ≤ ENNReal.ofReal
        (((Nat.card (SupportingFullFlag P) : ℝ) / (n.factorial : ℝ) ^ 2 + ε) * R ^ n) := by
  rw [supportingFullFlag_card_eq hp hP]
  rfl

theorem fvwLeadingLimit_iff_supportingFlag_limit {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P) :
    FVWLeadingLimit P ↔ Tendsto
      (fun R : ℝ => (funkVolume P (radius R)).toReal / R ^ n) Filter.atTop
      (𝓝 ((Nat.card (SupportingFullFlag P) : ℝ) / (n.factorial : ℝ) ^ 2)) := by
  rw [supportingFullFlag_card_eq hp hP]
  rfl

end
end Funk
