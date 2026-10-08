import Funk.FunkFinite

/-! A two-parameter comparison for the actual Funk integral.
A larger body has smaller polar kernels, while a smaller radius can keep its
integration domain inside that of the original body. No limit interchange is used. -/

open Set MeasureTheory

namespace Funk
noncomputable section

theorem translate_mono {n : ℕ} {K P : Set (Space n)} (hKP : K ⊆ P) (x : Space n) :
    translate K x ⊆ translate P x := Set.image_mono hKP

/-- Body inclusion and domain inclusion point in opposite directions. -/
theorem funkVolume_le_of_body_and_domain {n : ℕ} {K P : Set (Space n)}
    {σ τ : ℝ} (hKP : K ⊆ P)
    (hdom : (fun x => σ • x) '' P ⊆ (fun x => τ • x) '' K) :
    funkVolume P σ ≤ funkVolume K τ := by
  unfold funkVolume
  calc
    _ ≤ ∫⁻ x in (fun x => σ • x) '' P,
        volume (coordinatePolar (translate K x)) := by
      apply lintegral_mono
      intro x
      exact measure_mono (coordinatePolar_antitone (translate_mono hKP x))
    _ ≤ _ := lintegral_mono_set hdom

/-- A multiplicative outer sandwich gives the required smaller-radius comparison. -/
theorem funkVolume_le_of_outer_sandwich {n : ℕ} {K P : Set (Space n)}
    {σ τ : ℝ} (hσ : 0 < σ) (hKP : K ⊆ P)
    (hPK : P ⊆ (fun x => (τ / σ) • x) '' K) :
    funkVolume P σ ≤ funkVolume K τ := by
  apply funkVolume_le_of_body_and_domain hKP
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, rfl⟩ := hPK hx
  refine ⟨y, hy, ?_⟩
  change τ • y = σ • ((τ / σ) • y)
  rw [smul_smul]
  congr 1
  field_simp

end
end Funk
