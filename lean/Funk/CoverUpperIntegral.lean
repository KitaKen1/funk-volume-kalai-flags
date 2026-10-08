import Funk.FlagSimplex
import Funk.FunkFinite
import Funk.SimplexCertificate
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! One-sided integral certificates from finite covers.
Overlap is allowed: neither a triangulation nor a.e. disjointness is assumed.
The actual primal and translated-polar cover hypotheses remain explicit inputs.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Funk
noncomputable section

/-- Finite covering suffices for an upper bound on the actual set integral. -/
theorem setLIntegral_le_sum_of_cover {n : ℕ} {ι : Type*} [Fintype ι]
    (D : Set (Space n)) (S : ι → Set (Space n))
    (hcover : D ⊆ ⋃ i, S i) (f : Space n → ℝ≥0∞) :
    ∫⁻ x in D, f x ≤ ∑ i, ∫⁻ x in S i, f x := by
  calc
    _ ≤ ∫⁻ x in ⋃ i, S i, f x := lintegral_mono_set hcover
    _ ≤ _ := by simpa only [tsum_fintype] using lintegral_iUnion_le S f

/-- Outer measure subadditivity also permits overlaps in a finite polar cover. -/
theorem volume_le_sum_of_cover {n : ℕ} {ι : Type*} [Fintype ι]
    (D : Set (Space n)) (S : ι → Set (Space n)) (hcover : D ⊆ ⋃ i, S i) :
    volume D ≤ ∑ i, volume (S i) := by
  calc
    _ ≤ volume (⋃ i, S i) := measure_mono hcover
    _ ≤ _ := by simpa only [tsum_fintype] using measure_iUnion_le S

/-- Two covering certificates imply a double-sum upper bound for the frozen Funk integral. -/
theorem funkVolume_le_cover_integrals {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Set (Space n)) (τ : ℝ) (D : ι → Set (Space n))
    (S : κ → Space n → Set (Space n))
    (hprimal : (fun x => τ • x) '' P ⊆ ⋃ i, D i)
    (hpolar : ∀ x ∈ (fun x => τ • x) '' P,
      coordinatePolar (translate P x) ⊆ ⋃ j, S j x)
    (hmeas : ∀ j, Measurable (fun x => volume (S j x))) :
    funkVolume P τ ≤ ∑ i, ∑ j, ∫⁻ x in D i, volume (S j x) := by
  classical
  unfold funkVolume
  calc
    _ ≤ ∫⁻ x in (fun x => τ • x) '' P, ∑ j, volume (S j x) := by
      apply setLIntegral_mono (Finset.measurable_sum _ (fun j _ => hmeas j))
      intro x hx
      exact volume_le_sum_of_cover _ (fun j => S j x) (hpolar x hx)
    _ ≤ ∑ i, ∫⁻ x in D i, ∑ j, volume (S j x) :=
      setLIntegral_le_sum_of_cover _ D hprimal _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact lintegral_finsetSum _ (fun j _ => hmeas j)

/-- Measurable matrix certificates make their actual simplex volumes measurable. -/
theorem measurable_rowSimplex_volume {n : ℕ}
    (V : Space n → Matrix (Fin n) (Fin n) ℝ)
    (hV : Measurable (fun x i j => V x i j)) :
    Measurable (fun x => volume (rowSimplex (V x))) := by
  simp only [volume_rowSimplex]
  have hdet : Measurable (fun A : Fin n → Fin n → ℝ => Matrix.det A) :=
    (show Continuous (fun A : Fin n → Fin n → ℝ => Matrix.det A) from
      continuous_id.matrix_det).measurable
  exact ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp (hdet.comp hV)).div_const _)

/-- Known row matrices supply exact simplex-volume certificates inside the upper bound. -/
theorem funkVolume_le_rowSimplex_cover {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Set (Space n)) (τ : ℝ) (D : ι → Set (Space n))
    (V : κ → Space n → Matrix (Fin n) (Fin n) ℝ)
    (hprimal : (fun x => τ • x) '' P ⊆ ⋃ i, D i)
    (hpolar : ∀ x ∈ (fun x => τ • x) '' P,
      coordinatePolar (translate P x) ⊆ ⋃ j, rowSimplex (V j x))
    (hmeas : ∀ j, Measurable (fun x =>
      ENNReal.ofReal (|(V j x).det| / (n.factorial : ℝ)))) :
    funkVolume P τ ≤ ∑ i, ∑ j, ∫⁻ x in D i,
      ENNReal.ofReal (|(V j x).det| / (n.factorial : ℝ)) := by
  have hm : ∀ j, Measurable (fun x => volume (rowSimplex (V j x))) := by
    intro j
    simpa only [volume_rowSimplex] using hmeas j
  simpa only [volume_rowSimplex] using
    funkVolume_le_cover_integrals P τ D (fun j x => rowSimplex (V j x)) hprimal hpolar hm

/-- The actual coherent flag simplices can be used without proving they are disjoint.
The general flag cover and every translated-polar cover are still required inputs. -/
theorem funkVolume_le_flag_rowSimplex_cover {n : ℕ} {κ : Type*} [Fintype κ]
    (P : Set (Space n)) [Fintype (FullFlagWithTop P)] (τ : ℝ)
    (V : κ → Space n → Matrix (Fin n) (Fin n) ℝ)
    (hflag : P ⊆ ⋃ F : FullFlagWithTop P, flagSimplex F)
    (hpolar : ∀ x ∈ (fun x => τ • x) '' P,
      coordinatePolar (translate P x) ⊆ ⋃ j, rowSimplex (V j x))
    (hV : ∀ j, Measurable (fun x a b => V j x a b)) :
    funkVolume P τ ≤ ∑ F : FullFlagWithTop P, ∑ j,
      ∫⁻ x in (fun y => τ • y) '' flagSimplex F,
        ENNReal.ofReal (|(V j x).det| / (n.factorial : ℝ)) := by
  have hprimal : (fun x => τ • x) '' P ⊆
      ⋃ F : FullFlagWithTop P, (fun y => τ • y) '' flagSimplex F := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨F, hF⟩ := Set.mem_iUnion.mp (hflag hx)
    exact Set.mem_iUnion.mpr ⟨F, ⟨x, hF, rfl⟩⟩
  apply funkVolume_le_rowSimplex_cover P τ _ V hprimal hpolar
  intro j
  simpa only [volume_rowSimplex] using measurable_rowSimplex_volume (V j) (hV j)

end
end Funk
