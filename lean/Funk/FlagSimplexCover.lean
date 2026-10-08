import Funk.FaceChainCover
import Mathlib.Data.Fintype.EquivFin
import Mathlib.MeasureTheory.Measure.OpenPos

/-! A.e. and pointwise coverage by genuine complete flag simplices. Pointwise chains may
skip dimensions; all short-chain simplices are discarded as ambient-null.
This avoids codimension-one face extensions and relative cone-nullity transport. -/

open Set MeasureTheory

namespace Funk
noncomputable section

theorem face_rank_le_ambient {n : ℕ} {P : Set (Space n)} (F : PolytopeFace P) :
    Module.finrank ℝ (affineSpan ℝ F.val).direction ≤ n := by
  simpa only [Module.finrank_fin_fun] using
    Submodule.finrank_le (affineSpan ℝ F.val).direction

def chainRank {n : ℕ} {P : Set (Space n)} (s : Finset (PolytopeFace P))
    (F : s) : Fin (n + 1) :=
  ⟨Module.finrank ℝ (affineSpan ℝ F.val.val).direction,
    Nat.lt_succ_of_le (face_rank_le_ambient F.val)⟩

theorem chainRank_injective {n : ℕ} {P : Set (Space n)}
    {s : Finset (PolytopeFace P)} (hs : IsFaceChain s) : Function.Injective (chainRank s) := by
  intro F G h
  apply Subtype.ext
  by_contra hne
  have hd := congrArg Fin.val h
  rcases hs.2 F.val F.property G.val G.property hne with hFG | hGF
  · have hlt := face_dimension_lt_of_ssubset F.val G.val (hs.1 F.val F.property) hFG
    exact hlt.ne hd
  · have hlt := face_dimension_lt_of_ssubset G.val F.val (hs.1 G.val G.property) hGF
    exact hlt.ne hd.symm

theorem faceChain_card_le {n : ℕ} {P : Set (Space n)}
    {s : Finset (PolytopeFace P)} (hs : IsFaceChain s) : s.card ≤ n + 1 := by
  simpa only [Fintype.card_coe, Fintype.card_fin] using
    Fintype.card_le_of_injective (chainRank s) (chainRank_injective hs)

theorem faceChain_ssubset_of_rank_lt {n : ℕ} {P : Set (Space n)}
    {s : Finset (PolytopeFace P)} (hs : IsFaceChain s)
    {F G : PolytopeFace P} (hF : F ∈ s) (hG : G ∈ s)
    (hd : Module.finrank ℝ (affineSpan ℝ F.val).direction <
      Module.finrank ℝ (affineSpan ℝ G.val).direction) : F.val ⊂ G.val := by
  have hne : F ≠ G := by
    intro h
    subst G
    exact (lt_irrefl _) hd
  rcases hs.2 F hF G hG hne with hFG | hGF
  · exact hFG
  · exact False.elim (lt_asymm hd (face_dimension_lt_of_ssubset G F (hs.1 G hG) hGF))

def fullChainRankEquiv {n : ℕ} {P : Set (Space n)} (s : Finset (PolytopeFace P))
    (hs : IsFaceChain s) (hc : s.card = n + 1) : s ≃ Fin (n + 1) :=
  Equiv.ofBijective (chainRank s) ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨chainRank_injective hs, by simpa only [Fintype.card_coe, Fintype.card_fin] using hc⟩)

theorem fullChainRankEquiv_dimension {n : ℕ} {P : Set (Space n)}
    (s : Finset (PolytopeFace P)) (hs : IsFaceChain s) (hc : s.card = n + 1)
    (i : Fin (n + 1)) :
    Module.finrank ℝ (affineSpan ℝ ((fullChainRankEquiv s hs hc).symm i).val.val).direction = i.val :=
  congrArg Fin.val ((fullChainRankEquiv s hs hc).apply_symm_apply i)

/-- Sorting a maximal-length actual chain by rank gives the frozen geometric flag type. -/
def chainFullFlag {n : ℕ} {P : Set (Space n)} (s : Finset (PolytopeFace P))
    (hs : IsFaceChain s) (hc : s.card = n + 1) : FullFlagWithTop P where
  faces i := ((fullChainRankEquiv s hs hc).symm i).val.val
  nonempty i := hs.1 _ ((fullChainRankEquiv s hs hc).symm i).property
  convex i := ((fullChainRankEquiv s hs hc).symm i).val.property.1
  extreme i := ((fullChainRankEquiv s hs hc).symm i).val.property.2
  dimension := fullChainRankEquiv_dimension s hs hc
  chain := by
    intro i j hij
    apply faceChain_ssubset_of_rank_lt hs
      ((fullChainRankEquiv s hs hc).symm i).property
      ((fullChainRankEquiv s hs hc).symm j).property
    rw [fullChainRankEquiv_dimension, fullChainRankEquiv_dimension]
    exact hij
  top := face_eq_of_full_dimension
    ((fullChainRankEquiv s hs hc).symm (Fin.last n)).val.property.1
    ((fullChainRankEquiv s hs hc).symm (Fin.last n)).val.property.2
    (hs.1 _ ((fullChainRankEquiv s hs hc).symm (Fin.last n)).property)
    (fullChainRankEquiv_dimension s hs hc (Fin.last n))

theorem chainSimplex_eq_flagSimplex {n : ℕ} {P : Set (Space n)}
    (s : Finset (PolytopeFace P)) (hs : IsFaceChain s) (hc : s.card = n + 1) :
    chainSimplex s = flagSimplex (chainFullFlag s hs hc) := by
  unfold chainSimplex flagSimplex
  congr 1
  ext x
  constructor
  · rintro ⟨F, hF, rfl⟩
    let F' : s := ⟨F, hF⟩
    refine ⟨fullChainRankEquiv s hs hc F', ?_⟩
    change faceInteriorPoint ((fullChainRankEquiv s hs hc).symm
      (fullChainRankEquiv s hs hc F')).val = faceInteriorPoint F
    rw [Equiv.symm_apply_apply]
  · rintro ⟨i, rfl⟩
    exact ⟨((fullChainRankEquiv s hs hc).symm i).val,
      ((fullChainRankEquiv s hs hc).symm i).property, rfl⟩

/-- Actual complete flags cover almost every point of the actual polytope, with no cover input. -/
theorem ae_body_subset_flagSimplices {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P) :
    ∀ᵐ x ∂volume, x ∈ P → x ∈ ⋃ F : FullFlagWithTop P, flagSimplex F := by
  classical
  let : Finite {s : Finset (PolytopeFace P) // IsFaceChain s} := faceChain_finite hp
  have hall : ∀ᵐ x ∂volume, ∀ s : {s : Finset (PolytopeFace P) // IsFaceChain s},
      s.val.card ≤ n → x ∉ chainSimplex s.val := by
    apply ae_all_iff.mpr
    intro s
    by_cases hcard : s.val.card ≤ n
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp
        (volume_chainSimplex_zero_of_card_le s.val hcard)] with x hx
      exact fun _ => hx
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hcard h))
  filter_upwards [hall] with x hall
  intro hx
  obtain ⟨s, hxs⟩ := Set.mem_iUnion.mp (body_subset_chainSimplices hp hP hx)
  have hcard : s.val.card = n + 1 := by
    have hle := faceChain_card_le s.property
    have hnle : ¬ s.val.card ≤ n := fun h => hall s h hxs
    omega
  exact Set.mem_iUnion.mpr ⟨chainFullFlag s.val s.property hcard,
    (chainSimplex_eq_flagSimplex s.val s.property hcard) ▸ hxs⟩

/-- A closed cover of a regular-closed domain upgrades from a.e. to pointwise coverage. -/
theorem subset_closed_of_ae_cover {n : ℕ} {D C : Set (Space n)}
    (hD : D ⊆ closure (interior D)) (hC : IsClosed C)
    (hae : D ≤ᵐ[volume] C) : D ⊆ C := by
  have hnull : volume (interior D ∩ Cᶜ) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hae] with x hx
    exact fun h => h.2 (hx (interior_subset h.1))
  have hempty : interior D ∩ Cᶜ = ∅ :=
    (isOpen_interior.inter hC.isOpen_compl).eq_empty_of_measure_zero hnull
  have hi : interior D ⊆ C := by
    intro x hx
    by_contra hn
    have hm : x ∈ interior D ∩ Cᶜ := ⟨hx, hn⟩
    rw [hempty] at hm
    exact hm
  exact hD.trans (closure_minimal hi hC)

/-- Finite compact flag simplices also cover every boundary point of the original body. -/
theorem body_subset_flagSimplices {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P) :
    P ⊆ ⋃ F : FullFlagWithTop P, flagSimplex F := by
  let : Finite (FullFlagWithTop P) := fullFlagWithTop_finite hp hP
  have hclosure : closure (interior P) = P := by
    rw [hP.2.1.closure_interior_eq_closure_of_nonempty_interior ⟨0, hP.2.2.2⟩,
      hP.1.isClosed.closure_eq]
  exact subset_closed_of_ae_cover hclosure.symm.subset
    (isClosed_iUnion_of_finite (fun F => (flagSimplex_isCompact F).isClosed))
    (ae_body_subset_flagSimplices hp hP)

theorem body_eq_flagSimplices {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P) :
    P = ⋃ F : FullFlagWithTop P, flagSimplex F := by
  apply Set.Subset.antisymm (body_subset_flagSimplices hp hP)
  exact Set.iUnion_subset (fun F => flagSimplex_subset_polytope hP F)

/-- The genuine complete-flag primal integral upper bound; the polar kernel remains. -/
theorem funkVolume_le_flagSimplex_integrals {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P) {τ : ℝ} (hτ : 0 < τ) :
    let : Finite (FullFlagWithTop P) := fullFlagWithTop_finite hp hP
    let : Fintype (FullFlagWithTop P) := Fintype.ofFinite (FullFlagWithTop P)
    funkVolume P τ ≤ ENNReal.ofReal (τ ^ n) *
      ∑ F : FullFlagWithTop P, ∫⁻ X in flagSimplex F,
        volume (coordinatePolar (translate P (τ • X))) := by
  let : Finite (FullFlagWithTop P) := fullFlagWithTop_finite hp hP
  let : Fintype (FullFlagWithTop P) := Fintype.ofFinite (FullFlagWithTop P)
  rw [funkVolume_scale hP.1.measurableSet hτ]
  exact mul_le_mul_right
    (setLIntegral_le_sum_of_ae_cover P (fun F : FullFlagWithTop P => flagSimplex F)
      (ae_body_subset_flagSimplices hp hP) _) _

/-- The primal covering input is now supplied by a proved theorem. Only the actual
translated-polar matrix cover and its measurability remain explicit certificates. -/
theorem funkVolume_le_flag_rowSimplex_of_polar_cover {n : ℕ} {κ : Type*} [Fintype κ]
    {P : Set (Space n)} (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P)
    (τ : ℝ) (V : κ → Space n → Matrix (Fin n) (Fin n) ℝ)
    (hpolar : ∀ x ∈ (fun x => τ • x) '' P,
      coordinatePolar (translate P x) ⊆ ⋃ j, rowSimplex (V j x))
    (hV : ∀ j, Measurable (fun x a b => V j x a b)) :
    let : Finite (FullFlagWithTop P) := fullFlagWithTop_finite hp hP
    let : Fintype (FullFlagWithTop P) := Fintype.ofFinite (FullFlagWithTop P)
    funkVolume P τ ≤ ∑ F : FullFlagWithTop P, ∑ j,
      ∫⁻ x in (fun y => τ • y) '' flagSimplex F,
        ENNReal.ofReal (|(V j x).det| / (n.factorial : ℝ)) := by
  let : Finite (FullFlagWithTop P) := fullFlagWithTop_finite hp hP
  let : Fintype (FullFlagWithTop P) := Fintype.ofFinite (FullFlagWithTop P)
  exact funkVolume_le_flag_rowSimplex_cover P τ V
    (body_subset_flagSimplices hp hP) hpolar hV

end
end Funk
