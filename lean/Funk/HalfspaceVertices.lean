import Funk.PolytopeFaces
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Topology

/-! Finite halfspace intersections have finitely many extreme points.
An extreme point is uniquely determined by its active inequalities.
This avoids enumerating bases or computing facet normals. -/

open Set Filter
open scoped Topology

namespace Funk
noncomputable section

def halfspaceBody {n : ℕ} {ι : Type*} (rows : ι → Space n) (bounds : ι → ℝ) :
    Set (Space n) := {x | ∀ i, dotProduct (rows i) x ≤ bounds i}

theorem convex_halfspaceBody {n : ℕ} {ι : Type*}
    (rows : ι → Space n) (bounds : ι → ℝ) : Convex ℝ (halfspaceBody rows bounds) := by
  intro x hx y hy a b ha hb hab i
  change dotProduct (rows i) (a • x + b • y) ≤ bounds i
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
  calc
    _ ≤ a * bounds i + b * bounds i :=
      add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
        (mul_le_mul_of_nonneg_left (hy i) hb)
    _ = bounds i := by rw [← add_mul, hab, one_mul]

/-- Slight extrapolation away from another point preserves all inequalities
when every inequality active at x is also active at y. -/
theorem halfspace_extrapolate_eventually {n : ℕ} {ι : Type*} [Finite ι]
    (rows : ι → Space n) (bounds : ι → ℝ) {x y : Space n}
    (hx : x ∈ halfspaceBody rows bounds)
    (hactive : ∀ i, dotProduct (rows i) x = bounds i → dotProduct (rows i) y = bounds i) :
    ∀ᶠ t : ℝ in 𝓝 0, x + t • (x - y) ∈ halfspaceBody rows bounds := by
  change ∀ᶠ t : ℝ in 𝓝 0, ∀ i, dotProduct (rows i) (x + t • (x - y)) ≤ bounds i
  apply eventually_all.mpr
  intro i
  by_cases hi : dotProduct (rows i) x = bounds i
  · apply Filter.Eventually.of_forall
    intro t
    simp only [dotProduct_add, dotProduct_smul, dotProduct_sub, smul_eq_mul,
      hi, hactive i hi, sub_self, mul_zero, add_zero]
    exact le_rfl
  · have hc : Continuous (fun t : ℝ => dotProduct (rows i) (x + t • (x - y))) := by
      fun_prop
    have ht := hc.continuousAt.eventually_lt continuousAt_const
      (show dotProduct (rows i) (x + (0 : ℝ) • (x - y)) < bounds i by
        simpa using lt_of_le_of_ne (hx i) hi)
    exact ht.mono (fun _ h => h.le)

/-- An extreme point is fixed by its active inequalities among feasible points. -/
theorem halfspace_extreme_eq_of_active {n : ℕ} {ι : Type*} [Finite ι]
    (rows : ι → Space n) (bounds : ι → ℝ) {x y : Space n}
    (hx : x ∈ (halfspaceBody rows bounds).extremePoints ℝ)
    (hy : y ∈ halfspaceBody rows bounds)
    (hactive : ∀ i, dotProduct (rows i) x = bounds i → dotProduct (rows i) y = bounds i) :
    y = x := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (halfspace_extrapolate_eventually rows bounds hx.1 hactive)
  let t : ℝ := ε / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hw : x + t • (x - y) ∈ halfspaceBody rows bounds := by
    apply hball
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    linarith
  apply hx.2 hy hw
  refine ⟨t / (1 + t), 1 / (1 + t), by positivity, by positivity, ?_, ?_⟩
  · field_simp
    ring
  · ext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring

def activeConstraintCode {n : ℕ} {ι : Type*} [Fintype ι]
    (rows : ι → Space n) (bounds : ι → ℝ) (x : Space n) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => dotProduct (rows i) x = bounds i)

theorem activeConstraintCode_injective {n : ℕ} {ι : Type*} [Fintype ι]
    (rows : ι → Space n) (bounds : ι → ℝ) :
    Function.Injective (fun x : (halfspaceBody rows bounds).extremePoints ℝ =>
      activeConstraintCode rows bounds x.val) := by
  classical
  intro x y h
  apply Subtype.ext
  apply halfspace_extreme_eq_of_active rows bounds y.property x.property.1
  intro i hi
  have hm : i ∈ activeConstraintCode rows bounds y.val := by
    simp [activeConstraintCode, hi]
  change activeConstraintCode rows bounds x.val = activeConstraintCode rows bounds y.val at h
  rw [← h] at hm
  simpa [activeConstraintCode] using hm

theorem halfspace_extremePoints_finite {n : ℕ} {ι : Type*} [Finite ι]
    (rows : ι → Space n) (bounds : ι → ℝ) :
    ((halfspaceBody rows bounds).extremePoints ℝ).Finite := by
  let _ : Fintype ι := Fintype.ofFinite ι
  let : Finite ((halfspaceBody rows bounds).extremePoints ℝ) :=
    Finite.of_injective _ (activeConstraintCode_injective rows bounds)
  exact Set.toFinite _

/-- Compact finite halfspace intersections admit finite vertex presentations. -/
theorem halfspaceBody_isFinitePolytope {n : ℕ} {ι : Type*} [Finite ι]
    (rows : ι → Space n) (bounds : ι → ℝ) (hc : IsCompact (halfspaceBody rows bounds)) :
    IsFinitePolytope (halfspaceBody rows bounds) := by
  classical
  have hf := halfspace_extremePoints_finite rows bounds
  refine ⟨hf.toFinset, ?_⟩
  rw [hf.coe_toFinset]
  have hh := closure_convexHull_extremePoints hc (convex_halfspaceBody rows bounds)
  rw [(hf.isCompact_convexHull ℝ).isClosed.closure_eq] at hh
  exact hh.symm

end
end Funk
