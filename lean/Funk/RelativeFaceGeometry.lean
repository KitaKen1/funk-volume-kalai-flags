import Funk.RadialFaceCover
import Mathlib.Analysis.Normed.Affine.Isometry

/-! A compact convex face becomes a full-dimensional convex body in its own
vector direction space after translating an intrinsic-interior point to zero.
No symmetry is assumed. These are coordinate adapters, not a flag-cover proof. -/

open Set Topology

namespace Funk
noncomputable section

/-- The actual intrinsic vector space, embedded back into the frozen coordinates. -/
def relativeEmbedding {n : ℕ} (C : Set (Space n)) (p : affineSpan ℝ C) :
    (affineSpan ℝ C).direction →ᵃⁱ[ℝ] Space n := by
  let : Nonempty (affineSpan ℝ C) := ⟨p⟩
  exact (affineSpan ℝ C).subtypeₐᵢ.comp
    (AffineIsometryEquiv.vaddConst ℝ p).toAffineIsometry

/-- The original set expressed in the actual direction space, rather than ambient space. -/
def relativeBody {n : ℕ} (C : Set (Space n)) (p : affineSpan ℝ C) :
    Set (affineSpan ℝ C).direction := relativeEmbedding C p ⁻¹' C

theorem relativeEmbedding_apply {n : ℕ} (C : Set (Space n)) (p : affineSpan ℝ C)
    (v : (affineSpan ℝ C).direction) : relativeEmbedding C p v = (v : Space n) + p := rfl

theorem relativeEmbedding_zero {n : ℕ} (C : Set (Space n)) (p : affineSpan ℝ C) :
    relativeEmbedding C p 0 = p := by simp [relativeEmbedding_apply]

theorem relativeEmbedding_range {n : ℕ} (C : Set (Space n)) (p : affineSpan ℝ C) :
    Set.range (relativeEmbedding C p) = affineSpan ℝ C := by
  let : Nonempty (affineSpan ℝ C) := ⟨p⟩
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    exact ((AffineIsometryEquiv.vaddConst ℝ p) v).property
  · intro hx
    let x' : affineSpan ℝ C := ⟨x, hx⟩
    refine ⟨(AffineIsometryEquiv.vaddConst ℝ p).symm x', ?_⟩
    change ((AffineIsometryEquiv.vaddConst ℝ p)
      ((AffineIsometryEquiv.vaddConst ℝ p).symm x') : Space n) = x
    rw [AffineIsometryEquiv.apply_symm_apply]


theorem relativeBody_isCompact {n : ℕ} {C : Set (Space n)} (hk : IsCompact C)
    (p : affineSpan ℝ C) : IsCompact (relativeBody C p) := by
  apply (relativeEmbedding C p).isometry.isEmbedding.isInducing.isCompact_preimage'
  · exact hk
  · rw [relativeEmbedding_range]
    exact subset_affineSpan ℝ C

theorem relativeBody_convex {n : ℕ} {C : Set (Space n)} (hc : Convex ℝ C)
    (p : affineSpan ℝ C) : Convex ℝ (relativeBody C p) :=
  hc.affine_preimage (relativeEmbedding C p).toAffineMap

theorem relativeBody_image {n : ℕ} (C : Set (Space n)) (p : affineSpan ℝ C) :
    relativeEmbedding C p '' relativeBody C p = C := by
  apply Set.image_preimage_eq_of_subset
  rw [relativeEmbedding_range]
  exact subset_affineSpan ℝ C

theorem relativeBody_zero_interior {n : ℕ} {C : Set (Space n)}
    (p : affineSpan ℝ C) (hp : (p : Space n) ∈ intrinsicInterior ℝ C) :
    0 ∈ interior (relativeBody C p) := by
  let : Nonempty (affineSpan ℝ C) := ⟨p⟩
  obtain ⟨p', hp', hpp⟩ := hp
  have heq : p' = p := Subtype.ext hpp
  subst p'
  change 0 ∈ interior ((AffineIsometryEquiv.vaddConst ℝ p).toHomeomorph ⁻¹'
    ((↑) ⁻¹' C : Set (affineSpan ℝ C)))
  rw [← (AffineIsometryEquiv.vaddConst ℝ p).toHomeomorph.preimage_interior]
  simpa using hp'

theorem relativeEmbedding_frontier {n : ℕ} (C : Set (Space n)) (p : affineSpan ℝ C) :
    relativeEmbedding C p '' frontier (relativeBody C p) = intrinsicFrontier ℝ C := by
  let : Nonempty (affineSpan ℝ C) := ⟨p⟩
  change (Subtype.val ∘ (AffineIsometryEquiv.vaddConst ℝ p).toHomeomorph) ''
    frontier ((AffineIsometryEquiv.vaddConst ℝ p).toHomeomorph ⁻¹'
      ((↑) ⁻¹' C : Set (affineSpan ℝ C))) = _
  rw [Set.image_comp, ← (AffineIsometryEquiv.vaddConst ℝ p).toHomeomorph.preimage_frontier,
    (AffineIsometryEquiv.vaddConst ℝ p).toHomeomorph.image_preimage]
  rfl

/-- A relative radial segment in the original coordinates, with no symmetry premise. -/
theorem intrinsic_radial_boundary {n : ℕ} {C : Set (Space n)}
    (hk : IsCompact C) (hc : Convex ℝ C) {p : Space n}
    (hp : p ∈ intrinsicInterior ℝ C) {x : Space n} (hx : x ∈ C) (hxp : x ≠ p) :
    ∃ y ∈ intrinsicFrontier ℝ C, x ∈ segment ℝ p y := by
  let p' : affineSpan ℝ C := ⟨p, subset_affineSpan ℝ C (intrinsicInterior_subset hp)⟩
  obtain ⟨v, hv, hxv⟩ := (relativeBody_image C p').symm ▸ hx
  have hv0 : v ≠ 0 := by
    intro h
    apply hxp
    rw [← hxv, h, relativeEmbedding_zero]
  obtain ⟨w, hw, hvw⟩ := radial_boundary_of_compact_convex
    (relativeBody_isCompact hk p') (relativeBody_convex hc p')
    (relativeBody_zero_interior p' hp) hv hv0
  refine ⟨relativeEmbedding C p' w, ?_, ?_⟩
  · rw [← relativeEmbedding_frontier C p']
    exact ⟨w, hw, rfl⟩
  · have h := Set.mem_image_of_mem (relativeEmbedding C p') hvw
    change (relativeEmbedding C p') v ∈ (relativeEmbedding C p').toAffineMap '' segment ℝ 0 w at h
    rw [image_segment] at h
    change (relativeEmbedding C p') v ∈ segment ℝ ((relativeEmbedding C p') 0)
      ((relativeEmbedding C p') w) at h
    rw [relativeEmbedding_zero, hxv] at h
    exact h

end
end Funk
