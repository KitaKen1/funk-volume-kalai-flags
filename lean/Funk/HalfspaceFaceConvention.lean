import Funk.SupportingFlagConvention

/-! Literal closed-halfspace/interior-boundary face condition from FVW section2.2.
For a full-dimensional convex body this matches supporting faces. A flag only
has a monotone dimension-labelled face sequence; strictness and the top face
are proved consequences. This reconciles the actual cardinal coefficient. -/

open Set Topology Filter

namespace Funk
noncomputable section

/-- Closed-halfspace intersection whose boundary misses the body's interior.
Empty and full faces are explicit conventional cases. -/
def IsHalfspaceFace {n : ℕ} (P F : Set (Space n)) : Prop :=
  F = ∅ ∨ F = P ∨ ∃ (l : StrongDual ℝ (Space n)) (c : ℝ),
    l ≠ 0 ∧ F = {x ∈ P | c ≤ l x} ∧ ∀ x ∈ interior P, l x ≠ c

/-- A nonzero functional bounded on P has a strict bound on its interior. -/
theorem functional_lt_on_interior {n : ℕ} {P : Set (Space n)}
    (l : StrongDual ℝ (Space n)) (hl : l ≠ 0) (c : ℝ)
    (hbound : ∀ x ∈ P, l x ≤ c) : ∀ x ∈ interior P, l x < c := by
  have him : l '' interior P ⊆ Iic c := by
    rintro _ ⟨x, hx, rfl⟩
    exact hbound x (interior_subset hx)
  have hi : l '' interior P ⊆ interior (Iic c) :=
    interior_maximal him (l.isOpenMap_of_ne_zero hl _ isOpen_interior)
  intro x hx
  simpa only [interior_Iic, mem_Iio] using hi (mem_image_of_mem l hx)

theorem supportingFace_isHalfspaceFace {n : ℕ} {P F : Set (Space n)}
    (h : IsSupportingFace P F) : IsHalfspaceFace P F := by
  rcases h with h | h | ⟨l, c, hl, hbound, hF⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨l, c, hl, ?_, ?_⟩)
    · rw [hF]
      ext x
      simp only [mem_ofPred_eq, and_congr_right_iff]
      intro hx
      exact ⟨fun heq => heq.ge, fun hge => le_antisymm (hbound x hx) hge⟩
    · exact fun x hx => (functional_lt_on_interior l hl c hbound x hx).ne

/-- Literal halfspace faces match supporting faces when the body has nonempty interior. -/
theorem halfspaceFace_isSupportingFace {n : ℕ} {P F : Set (Space n)}
    (hP : IsSymmetricConvexBody P) (h : IsHalfspaceFace P F) :
    IsSupportingFace P F := by
  rcases h with h | h | ⟨l, c, hl, hF, hboundary⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · have hclosure : closure (interior P) = P := by
      rw [hP.2.1.closure_interior_eq_closure_of_nonempty_interior ⟨0, hP.2.2.2⟩,
        hP.1.isClosed.closure_eq]
    rcases hP.2.1.interior.isPreconnected.mapsTo_Ioi_or_Iio
      l.continuous.continuousOn hboundary with hgt | hlt
    · have hge : P ⊆ {x | c ≤ l x} := by
        rw [← hclosure]
        exact closure_minimal (fun x hx => show c ≤ l x from le_of_lt (hgt hx))
          (isClosed_le continuous_const l.continuous)
      refine Or.inr (Or.inl ?_)
      rw [hF]
      ext x
      exact ⟨fun hx => hx.1, fun hx => ⟨hx, hge hx⟩⟩
    · have hle : ∀ x ∈ P, l x ≤ c := by
        have hsubset : P ⊆ {x | l x ≤ c} := by
          rw [← hclosure]
          exact closure_minimal (fun x hx => show l x ≤ c from le_of_lt (hlt hx))
            (isClosed_le l.continuous continuous_const)
        exact fun x hx => hsubset hx
      refine Or.inr (Or.inr ⟨l, c, hl, hle, ?_⟩)
      rw [hF]
      ext x
      simp only [mem_ofPred_eq, and_congr_right_iff]
      intro hx
      exact ⟨fun hge => le_antisymm (hle x hx) hge, fun heq => heq.ge⟩

theorem finitePolytope_face_iff_halfspace {n : ℕ} {P F : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P) :
    (Convex ℝ F ∧ IsExtreme ℝ P F) ↔ IsHalfspaceFace P F :=
  (finitePolytope_face_iff_supporting hp).trans
    ⟨supportingFace_isHalfspaceFace, halfspaceFace_isSupportingFace hP⟩

/-- An n-dimensional nonempty actual face in Space n is the whole polytope. -/
theorem face_eq_of_full_dimension {n : ℕ} {P F : Set (Space n)}
    (hc : Convex ℝ F) (he : IsExtreme ℝ P F) (hn : F.Nonempty)
    (hdim : Module.finrank ℝ (affineSpan ℝ F).direction = n) : F = P := by
  have hd : (affineSpan ℝ F).direction = ⊤ :=
    Submodule.eq_top_of_finrank_eq (hdim.trans (Module.finrank_fin_fun ℝ).symm)
  have hA : affineSpan ℝ F = ⊤ :=
    (AffineSubspace.direction_eq_top_iff_of_nonempty
      (hn.mono (subset_affineSpan ℝ F))).mp hd
  rw [← face_inter_affineSpan hc he, hA]
  simp

/-- Literal FVW face sequence: top membership and strictness are not assumed. -/
structure HalfspaceFullFlag {n : ℕ} (P : Set (Space n)) where
  faces : Fin (n + 1) → Set (Space n)
  nonempty : ∀ i, (faces i).Nonempty
  halfspace : ∀ i, IsHalfspaceFace P (faces i)
  dimension : ∀ i, Module.finrank ℝ (affineSpan ℝ (faces i)).direction = i.val
  chain : Monotone faces

theorem halfspaceFullFlag_ext {n : ℕ} {P : Set (Space n)}
    {F G : HalfspaceFullFlag P} (h : F.faces = G.faces) : F = G := by
  cases F
  cases G
  cases h
  rfl

theorem halfspaceFullFlag_strictMono {n : ℕ} {P : Set (Space n)}
    (F : HalfspaceFullFlag P) : StrictMono F.faces := by
  intro i j hij
  have hne : F.faces i ≠ F.faces j := by
    intro heq
    have hi := F.dimension i
    have hj := F.dimension j
    rw [heq] at hi
    have hij' : i.val < j.val := hij
    omega
  exact lt_of_le_of_ne (F.chain hij.le) hne

theorem halfspaceFullFlag_top {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : HalfspaceFullFlag P) : F.faces (Fin.last n) = P := by
  have hface := (finitePolytope_face_iff_halfspace hp hP).mpr (F.halfspace (Fin.last n))
  exact face_eq_of_full_dimension hface.1 hface.2 (F.nonempty (Fin.last n))
    (F.dimension (Fin.last n))

def supportingToHalfspaceFlag {n : ℕ} {P : Set (Space n)}
    (F : SupportingFullFlag P) : HalfspaceFullFlag P where
  faces := F.faces
  nonempty := F.nonempty
  halfspace := fun i => supportingFace_isHalfspaceFace (F.supporting i)
  dimension := F.dimension
  chain := F.chain.monotone

def halfspaceToSupportingFlag {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (F : HalfspaceFullFlag P) : SupportingFullFlag P where
  faces := F.faces
  nonempty := F.nonempty
  supporting := fun i => halfspaceFace_isSupportingFace hP (F.halfspace i)
  dimension := F.dimension
  chain := halfspaceFullFlag_strictMono F
  top := halfspaceFullFlag_top hp hP F

def supportingHalfspaceFlagEquiv {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P) :
    SupportingFullFlag P ≃ HalfspaceFullFlag P where
  toFun := supportingToHalfspaceFlag
  invFun := halfspaceToSupportingFlag hp hP
  left_inv := fun _ => supportingFullFlag_ext rfl
  right_inv := fun _ => halfspaceFullFlag_ext rfl

/-- Same geometric flags, exact correspondence with the literal closed-halfspace convention. -/
def fullFlagHalfspaceEquiv {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P) :
    FullFlag P ≃ HalfspaceFullFlag P :=
  (fullFlagSupportingEquiv hp hP).trans (supportingHalfspaceFlagEquiv hp hP)

theorem halfspaceFullFlag_finite {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P) :
    Finite (HalfspaceFullFlag P) :=
  let : Finite (FullFlag P) := fullFlag_finite hp
  Finite.of_equiv _ (fullFlagHalfspaceEquiv hp hP)

theorem halfspaceFullFlag_card_eq {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P) :
    Nat.card (HalfspaceFullFlag P) = Nat.card (FullFlag P) :=
  (Nat.card_congr (fullFlagHalfspaceEquiv hp hP)).symm

theorem fvwEpsilonUpper_iff_halfspaceFlag_upper {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P) :
    FVWEpsilonUpper P ↔ ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      funkVolume P (radius R) ≤ ENNReal.ofReal
        (((Nat.card (HalfspaceFullFlag P) : ℝ) / (n.factorial : ℝ) ^ 2 + ε) * R ^ n) := by
  rw [halfspaceFullFlag_card_eq hp hP]
  rfl

theorem fvwLeadingLimit_iff_halfspaceFlag_limit {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P) :
    FVWLeadingLimit P ↔ Tendsto
      (fun R : ℝ => (funkVolume P (radius R)).toReal / R ^ n) atTop
      (𝓝 ((Nat.card (HalfspaceFullFlag P) : ℝ) / (n.factorial : ℝ) ^ 2)) := by
  rw [halfspaceFullFlag_card_eq hp hP]
  rfl

end
end Funk
