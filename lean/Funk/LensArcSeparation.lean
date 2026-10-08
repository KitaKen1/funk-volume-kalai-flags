import Funk.LensRealPart
import Funk.WeightedSlope

/-! The actual right lens arc lies strictly on one side of its endpoint chord.
The opposite arc lies on the other side by oddness.  This does not yet provide
a Jordan-curve theorem or univalence on the disk. -/

open Set

namespace Funk
noncomputable section

/-- A real linear functional vanishing on the two actual endpoints. -/
def lensChordCoordinate (τ : ℝ) (z : ℂ) : ℝ :=
  z.re - (tiltedLens τ Complex.I).re * z.im

def lensChordField (τ θ : ℝ) : ℝ :=
  -lensRate τ * lensChordCoordinate τ (lensRadialTrace τ 1 θ) -
    lensFactor τ * (Complex.arctan (circleMap 0 1 θ)).im -
    (tiltedLens τ Complex.I).re * (lensRate τ / τ)

theorem lensChordCoordinate_neg (τ : ℝ) (z : ℂ) :
    lensChordCoordinate τ (-z) = -lensChordCoordinate τ z := by
  simp [lensChordCoordinate]
  ring

theorem lensChordCoordinate_continuous (τ : ℝ) : Continuous (lensChordCoordinate τ) := by
  unfold lensChordCoordinate
  fun_prop

theorem lensChordCoordinate_endpoints {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    lensChordCoordinate τ (lensRadialTrace τ 1 (-Real.pi / 2)) = 0 ∧
    lensChordCoordinate τ (lensRadialTrace τ 1 (Real.pi / 2)) = 0 := by
  have hr : lensChordCoordinate τ (lensRadialTrace τ 1 (Real.pi / 2)) = 0 := by
    simp [lensRadialTrace, circleMap_pi_div_two, lensChordCoordinate,
      lensBoundary_im_right hτ0 hτ1]
  exact ⟨by rw [lensBoundary_opposite_endpoints, lensChordCoordinate_neg, hr, neg_zero], hr⟩

theorem hasDerivAt_lensChord (τ : ℝ) {θ : ℝ} (hθ : 0 < Real.cos θ) :
    HasDerivAt (fun x => lensChordCoordinate τ (lensRadialTrace τ 1 x))
      (lensChordField τ θ) θ := by
  have h := (hasDerivAt_lensBoundary_re τ hθ).sub
    ((hasDerivAt_lensBoundary_im τ hθ).const_mul (tiltedLens τ Complex.I).re)
  convert h using 1
  · rfl
  · dsimp [lensChordField, lensChordCoordinate]
    rw [lensFactor_mul_pi]
    ring

theorem hasDerivAt_lensChordField (τ : ℝ) {θ : ℝ} (hθ : 0 < Real.cos θ) :
    HasDerivAt (lensChordField τ)
      (-lensRate τ * lensChordField τ θ - lensFactor τ / (2 * Real.cos θ)) θ := by
  have h := (((hasDerivAt_lensChord τ hθ).const_mul (-lensRate τ)).sub
    ((hasDerivAt_arctan_circle_im hθ).const_mul (lensFactor τ))).sub_const
    ((tiltedLens τ Complex.I).re * (lensRate τ / τ))
  convert h using 1
  · rfl
  · ring

theorem hasDerivAt_lensWeightedChordField (τ : ℝ) {θ : ℝ} (hθ : 0 < Real.cos θ) :
    HasDerivAt (fun x => Real.exp (lensRate τ * x) * lensChordField τ x)
      (Real.exp (lensRate τ * θ) * (-lensFactor τ / (2 * Real.cos θ))) θ := by
  convert (((hasDerivAt_id θ).const_mul (lensRate τ)).exp).mul
    (hasDerivAt_lensChordField τ hθ) using 1
  · rfl
  · dsimp
    ring

theorem lensWeightedChordField_strictAntiOn {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    StrictAntiOn (fun θ => Real.exp (lensRate τ * θ) * lensChordField τ θ)
      (Ioo (-Real.pi / 2) (Real.pi / 2)) := by
  have hd : ∀ θ ∈ Ioo (-Real.pi / 2) (Real.pi / 2),
      HasDerivAt (fun x => Real.exp (lensRate τ * x) * lensChordField τ x)
        (Real.exp (lensRate τ * θ) * (-lensFactor τ / (2 * Real.cos θ))) θ := by
    intro θ hθ
    exact hasDerivAt_lensWeightedChordField τ
      (Real.cos_pos_of_mem_Ioo (by simpa [neg_div] using hθ))
  apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
  · exact fun θ hθ => (hd θ hθ).continuousAt.continuousWithinAt
  · intro θ hθ
    rw [interior_Ioo] at hθ
    rw [(hd θ hθ).deriv]
    apply mul_neg_of_pos_of_neg (Real.exp_pos _)
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (lensFactor_pos hτ0 hτ1))
      (mul_pos (by norm_num) (Real.cos_pos_of_mem_Ioo (by simpa [neg_div] using hθ)))

/-- Strict separation from the endpoint chord on the open right arc. -/
theorem lensChordCoordinate_pos {τ θ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hθ : θ ∈ Ioo (-Real.pi / 2) (Real.pi / 2)) :
    0 < lensChordCoordinate τ (lensRadialTrace τ 1 θ) := by
  have he := lensChordCoordinate_endpoints hτ0 hτ1
  exact pos_of_weighted_deriv_strictAnti
    ((lensChordCoordinate_continuous τ).comp (lensBoundary_continuous τ)).continuousOn
    (fun θ hθ => hasDerivAt_lensChord τ
      (Real.cos_pos_of_mem_Ioo (by simpa [neg_div] using hθ)))
    he.1 he.2 (fun θ _ => Real.exp_pos (lensRate τ * θ))
    (lensWeightedChordField_strictAntiOn hτ0 hτ1) hθ

theorem lensChordCoordinate_nonneg {τ θ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hθ : θ ∈ Icc (-Real.pi / 2) (Real.pi / 2)) :
    0 ≤ lensChordCoordinate τ (lensRadialTrace τ 1 θ) := by
  rcases eq_or_lt_of_le hθ.1 with he | he
  · rw [← he, (lensChordCoordinate_endpoints hτ0 hτ1).1]
  · rcases eq_or_lt_of_le hθ.2 with hf | hf
    · rw [hf, (lensChordCoordinate_endpoints hτ0 hτ1).2]
    · exact (lensChordCoordinate_pos hτ0 hτ1 ⟨he, hf⟩).le

theorem lensRadialTrace_add_pi (τ θ : ℝ) :
    lensRadialTrace τ 1 (θ + Real.pi) = -lensRadialTrace τ 1 θ := by
  have hz : circleMap 0 1 (θ + Real.pi) = -circleMap 0 1 θ := by
    apply Complex.ext <;> simp [circleMap_zero_re, circleMap_zero_im]
  simp only [lensRadialTrace, hz, tiltedLens_neg]

/-- Points in the open right arc cannot meet any point in the opposite closed arc. -/
theorem lensBoundary_ne_opposite {τ θ φ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hθ : θ ∈ Ioo (-Real.pi / 2) (Real.pi / 2))
    (hφ : φ ∈ Icc (-Real.pi / 2) (Real.pi / 2)) :
    lensRadialTrace τ 1 θ ≠ lensRadialTrace τ 1 (φ + Real.pi) := by
  intro h
  have he := congrArg (lensChordCoordinate τ) h
  rw [lensRadialTrace_add_pi, lensChordCoordinate_neg] at he
  have hp := lensChordCoordinate_pos hτ0 hτ1 hθ
  have hn := lensChordCoordinate_nonneg hτ0 hτ1 hφ
  linarith

/-- The two closed arcs can meet only at the right arc's two endpoints. -/
theorem lensBoundary_meeting_is_endpoint {τ θ φ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hθ : θ ∈ Icc (-Real.pi / 2) (Real.pi / 2))
    (hφ : φ ∈ Icc (-Real.pi / 2) (Real.pi / 2))
    (heq : lensRadialTrace τ 1 θ = lensRadialTrace τ 1 (φ + Real.pi)) :
    θ = -Real.pi / 2 ∨ θ = Real.pi / 2 := by
  by_contra! hne
  exact lensBoundary_ne_opposite hτ0 hτ1
    ⟨lt_of_le_of_ne hθ.1 hne.1.symm, lt_of_le_of_ne hθ.2 hne.2⟩ hφ heq

end
end Funk
