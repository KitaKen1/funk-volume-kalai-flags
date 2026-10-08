import Funk.PolytopeStrips

/-! An explicit projective map between the original polar and the translated
polar. Positivity is verified for every x in tau P, including tau = 0.
No vertex enumeration or probability covering premise is used. -/

open Set

namespace Funk
noncomputable section

def polarShift {n : ℕ} (x y : Space n) : Space n :=
  (1 / (1 - dotProduct y x)) • y

theorem polarShift_zero {n : ℕ} (x : Space n) : polarShift x 0 = 0 := by
  simp [polarShift]

theorem polarShift_denominator_pos {n : ℕ} {P : Set (Space n)}
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) {X y : Space n}
    (hX : X ∈ P) (hy : y ∈ coordinatePolar P) :
    0 < 1 - dotProduct y (τ • X) := by
  have hb := hy X hX
  rw [dotProduct_smul, smul_eq_mul]
  have hm := mul_le_mul_of_nonneg_left hb hτ0
  linarith

theorem polarShift_mem_translatedPolar {n : ℕ} {P : Set (Space n)}
    {x y : Space n} (hy : y ∈ coordinatePolar P)
    (hd : 0 < 1 - dotProduct y x) :
    polarShift x y ∈ coordinatePolar (translate P x) := by
  rintro _ ⟨z, hz, rfl⟩
  simp only [polarShift, smul_dotProduct, dotProduct_sub, smul_eq_mul]
  calc
    _ = (dotProduct y z - dotProduct y x) / (1 - dotProduct y x) := by ring
    _ ≤ 1 := (div_le_one hd).mpr (sub_le_sub_right (hy z hz) (dotProduct y x))

theorem translatedPolar_inverse_denominator_pos {n : ℕ} {P : Set (Space n)}
    (hs : ∀ z ∈ P, -z ∈ P) {τ : ℝ} (hτ0 : 0 ≤ τ) {X w : Space n}
    (hX : X ∈ P) (hw : w ∈ coordinatePolar (translate P (τ • X))) :
    0 < 1 + dotProduct w (τ • X) := by
  have hb := hw (-X - τ • X) ⟨-X, hs X hX, rfl⟩
  simp only [dotProduct_sub, dotProduct_neg, dotProduct_smul, smul_eq_mul] at hb ⊢
  by_contra hn
  have hn' := le_of_not_gt hn
  have hd : 0 ≤ dotProduct w X := by linarith
  have hm := mul_nonneg hτ0 hd
  linarith

theorem translatedPolar_inverse_mem {n : ℕ} {P : Set (Space n)}
    {x w : Space n} (hw : w ∈ coordinatePolar (translate P x))
    (hd : 0 < 1 + dotProduct w x) :
    (1 / (1 + dotProduct w x)) • w ∈ coordinatePolar P := by
  intro z hz
  have hb := hw (z - x) ⟨z, hz, rfl⟩
  simp only [smul_dotProduct, smul_eq_mul, one_div_mul_eq_div]
  apply (div_le_one hd).mpr
  rw [dotProduct_sub] at hb
  linarith

theorem polarShift_inverse {n : ℕ} {x w : Space n}
    (hd : 1 + dotProduct w x ≠ 0) :
    polarShift x ((1 / (1 + dotProduct w x)) • w) = w := by
  unfold polarShift
  rw [smul_dotProduct, smul_eq_mul, smul_smul]
  have he : (1 / (1 - 1 / (1 + dotProduct w x) * dotProduct w x)) *
      (1 / (1 + dotProduct w x)) = 1 := by field_simp [hd]; ring
  rw [he, one_smul]

theorem translatedPolar_eq_polarShift_image {n : ℕ} {P : Set (Space n)}
    (hP : IsSymmetricConvexBody P) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    {X : Space n} (hX : X ∈ P) :
    coordinatePolar (translate P (τ • X)) = polarShift (τ • X) '' coordinatePolar P := by
  apply Set.Subset.antisymm
  · intro w hw
    have hd := translatedPolar_inverse_denominator_pos hP.2.2.1 hτ0 hX hw
    exact ⟨(1 / (1 + dotProduct w (τ • X))) • w,
      translatedPolar_inverse_mem hw hd, polarShift_inverse (ne_of_gt hd)⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact polarShift_mem_translatedPolar hy (polarShift_denominator_pos hτ0 hτ1 hX hy)

/-- A finite intersection of strict vertex inequalities is a neighborhood of zero. -/
theorem finitePolytope_zero_mem_interior_polar {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) : 0 ∈ interior (coordinatePolar P) := by
  classical
  obtain ⟨v, rfl⟩ := hp
  rw [coordinatePolar_convexHull]
  let U : Set (Space n) := ⋂ z : v, {y | dotProduct y z.val < 1}
  have ho : IsOpen U := isOpen_iInter_of_finite (fun z =>
    isOpen_lt (continuous_id.dotProduct continuous_const) continuous_const)
  have hs : U ⊆ coordinatePolar (v : Set (Space n)) := by
    intro y hy z hz
    exact (Set.mem_iInter.mp hy ⟨z, hz⟩).le
  apply interior_maximal hs ho
  apply Set.mem_iInter.mpr
  intro z
  change dotProduct (0 : Space n) z.val < 1
  simp

theorem coordinatePolar_isSymmetricConvexBody {n : ℕ} {P : Set (Space n)}
    (hp : IsFinitePolytope P) (hP : IsSymmetricConvexBody P) :
    IsSymmetricConvexBody (coordinatePolar P) :=
  ⟨isCompact_coordinatePolar hP.2.1 hP.2.2.2, convex_coordinatePolar P,
    fun _ hy => neg_mem_coordinatePolar hP.2.2.1 hy,
    finitePolytope_zero_mem_interior_polar hp⟩

end
end Funk
