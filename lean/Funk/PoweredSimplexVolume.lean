import Funk.SimplexVolume
import Funk.StripNull

/-! The genuine positive powered-radius simplex has volume 1/n!.
Coordinate-zero and total-radius-one boundary sets are proved null. -/

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Funk
noncomputable section

/-- The open positive simplex for t_i = r_i^(2k). -/
def positivePoweredSimplex (n : ℕ) : Set (Space n) :=
  {t | (∀ i, 0 < t i) ∧ ∑ i, t i < 1}

theorem isOpen_positivePoweredSimplex (n : ℕ) : IsOpen (positivePoweredSimplex n) := by
  have he : positivePoweredSimplex n =
      (⋂ i, {t : Space n | 0 < t i}) ∩ {t | ∑ i, t i < 1} := by
    ext t
    simp [positivePoweredSimplex]
  rw [he]
  exact (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)).inter
    (isOpen_lt (by fun_prop) continuous_const)

theorem positivePoweredSimplex_subset_solid (n : ℕ) :
    positivePoweredSimplex n ⊆ solidSimplex n 1 :=
  fun _ ht => ⟨fun i => (ht.1 i).le, ht.2.le⟩

theorem volume_coordinate_zero {n : ℕ} (i : Fin n) :
    volume {t : Space n | t i = 0} = 0 := by
  classical
  let f : Space n →ₗ[ℝ] ℝ := LinearMap.proj i
  have hf : f ≠ 0 := by
    intro h
    have he := congrArg (fun g : Space n →ₗ[ℝ] ℝ => g (Pi.single i (1 : ℝ))) h
    simp [f] at he
  change volume (f.ker : Set (Space n)) = 0
  exact Measure.addHaar_submodule volume f.ker (fun h => hf (LinearMap.ker_eq_top.mp h))

theorem volume_total_coordinate_one (n : ℕ) :
    volume {t : Space n | ∑ i, t i = 1} = 0 := by
  simpa [dotProduct] using
    volume_dotProduct_level_zero (fun _ : Fin n => (1 : ℝ)) (by norm_num : (1 : ℝ) ≠ 0)

theorem ae_coordinates_nonzero (n : ℕ) :
    ∀ᵐ t ∂(volume : Measure (Space n)), ∀ i, t i ≠ 0 := by
  apply ae_all_iff.mpr
  intro i
  apply ae_iff.mpr
  simpa only [not_not] using volume_coordinate_zero i

theorem ae_total_coordinate_ne_one (n : ℕ) :
    ∀ᵐ t ∂(volume : Measure (Space n)), ∑ i, t i ≠ 1 := by
  apply ae_iff.mpr
  simpa only [not_not] using volume_total_coordinate_one n

theorem positivePoweredSimplex_ae_eq_solid (n : ℕ) :
    positivePoweredSimplex n =ᵐ[volume] solidSimplex n 1 := by
  filter_upwards [ae_coordinates_nonzero n, ae_total_coordinate_ne_one n] with t ht hs
  apply propext
  constructor
  · exact fun h => positivePoweredSimplex_subset_solid n h
  · intro h
    exact ⟨fun i => lt_of_le_of_ne (h.1 i) (ht i).symm, lt_of_le_of_ne h.2 hs⟩

theorem volume_positivePoweredSimplex (n : ℕ) :
    volume (positivePoweredSimplex n) = ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  rw [measure_congr (positivePoweredSimplex_ae_eq_solid n), volume_solidSimplex n (by norm_num)]
  simp

theorem volume_positivePoweredSimplex_ne_top (n : ℕ) :
    volume (positivePoweredSimplex n) ≠ ∞ := by
  rw [volume_positivePoweredSimplex]
  exact ENNReal.ofReal_ne_top

theorem positivePoweredSimplex_coordinate_lt_one {n : ℕ} {t : Space n}
    (ht : t ∈ positivePoweredSimplex n) (i : Fin n) : t i < 1 := by
  exact (Finset.single_le_sum (fun j _ => (ht.1 j).le) (Finset.mem_univ i)).trans_lt ht.2

end
end Funk
