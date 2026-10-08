import Funk.RegularZeroNull
import Mathlib.MeasureTheory.Measure.Prod

/-! A measurable finite-dimensional set is null if all sections in one
coordinate are null. Isolated regular zeros and two transverse derivatives
then provide a null-set criterion with no real-analyticity assumption. -/

open Set Filter MeasureTheory
open scoped Topology

namespace Funk
noncomputable section

theorem volume_eq_zero_of_update_slices {n : ℕ} (s : Set (Space n))
    (hs : MeasurableSet s) (i : Fin n)
    (h : ∀ t : Space n, volume {u : ℝ | Function.update t i u ∈ s} = 0) :
    volume s = 0 := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    let e : (ℝ × Space n) ≃ᵐ Space (n + 1) :=
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm
    have hp : MeasurePreserving e :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm _
    rw [← hp.map_eq, Measure.map_apply e.measurable hs, Measure.volume_eq_prod,
      Measure.prod_apply_symm (hs.preimage e.measurable)]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [] with t
    have ht := h (i.insertNth 0 t)
    change volume {u : ℝ | i.insertNth u t ∈ s} = 0
    simpa only [Fin.update_insertNth] using ht

theorem volume_eq_zero_of_regular_coordinate {n : ℕ} (f : Space n → ℝ)
    (s : Set (Space n)) (hs : MeasurableSet s) (i : Fin n)
    (hz : ∀ t ∈ s, f t = 0)
    (hd : ∀ t ∈ s, ∃ d : ℝ,
      HasDerivAt (fun u => f (Function.update t i u)) d (t i) ∧ d ≠ 0) :
    volume s = 0 := by
  apply volume_eq_zero_of_update_slices s hs i
  intro t
  apply volume_regular_zeros_eq_zero (fun u => f (Function.update t i u))
  · intro u hu
    exact hz _ hu
  · intro u hu
    obtain ⟨d, hd, hne⟩ := hd _ hu
    refine ⟨d, ?_, hne⟩
    simpa only [Function.update_self, Function.update_idem] using hd

/-- Split f=0 into regular f-zeros and points in g=0. The latter are regular
g-zeros in a second coordinate. All measurability hypotheses are explicit. -/
theorem volume_zero_of_transverse_coordinate_derivatives {n : ℕ}
    (f g : Space n → ℝ) (hf : Measurable f) (hg : Measurable g)
    (U : Set (Space n)) (hU : MeasurableSet U) (i j : Fin n)
    (hfg : ∀ t ∈ U, HasDerivAt (fun u => f (Function.update t i u)) (g t) (t i))
    (hgg : ∀ t ∈ U, ∃ d : ℝ,
      HasDerivAt (fun u => g (Function.update t j u)) d (t j) ∧ d ≠ 0) :
    volume {t ∈ U | f t = 0} = 0 := by
  let A : Set (Space n) := {t ∈ U | f t = 0 ∧ g t ≠ 0}
  let B : Set (Space n) := {t ∈ U | g t = 0}
  have hA : MeasurableSet A := hU.inter
    ((measurableSet_eq_fun hf measurable_const).inter
      (measurableSet_eq_fun hg measurable_const).compl)
  have hB : MeasurableSet B := hU.inter (measurableSet_eq_fun hg measurable_const)
  have ha : volume A = 0 := volume_eq_zero_of_regular_coordinate f A hA i
    (fun _ ht => ht.2.1) (fun t ht => ⟨g t, hfg t ht.1, ht.2.2⟩)
  have hb : volume B = 0 := volume_eq_zero_of_regular_coordinate g B hB j
    (fun _ ht => ht.2) (fun t ht => hgg t ht.1)
  apply measure_mono_null (t := A ∪ B) ?_ (measure_union_null ha hb)
  intro t ht
  by_cases hg0 : g t = 0
  · exact Or.inr ⟨ht.1, hg0⟩
  · exact Or.inl ⟨ht.1, ht.2, hg0⟩

end
end Funk
