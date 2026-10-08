import Funk.LensPowerTaylor

/-! A constructed local record of the actual analytic mass-source inputs.
Every field is proved for the actual lens, real rows and powers. This record
neither imports nor asserts the upstream mass inequality; the exact upstream
upstream structure adapter and dependency build remain separate obligations. -/

open Set Filter Asymptotics
open scoped Topology BigOperators

namespace Funk
noncomputable section

theorem lensPowerEnergy_eq_norm_sq {n m : ℕ} (τ : ℝ) (rows : Fin m → Space n)
    (k : ℕ) (z : LensComplexSpace n) :
    lensPowerEnergy τ rows k z = ‖lensPowerMap τ rows k z‖ ^ 2 :=
  (EuclideanSpace.norm_sq_eq (lensPowerMap τ rows k z)).symm

/-- The actual ten field obligations; no mass bound is contained in this record. -/
structure LensPowerMassInput (n m : ℕ) (τ : ℝ) (rows : Fin m → Space n) (k : ℕ) : Prop where
  dimension_pos : 1 ≤ n
  degree_pos : 1 ≤ k
  open_domain : IsOpen (lensComplexDomain τ rows)
  zero_mem : (0 : LensComplexSpace n) ∈ lensComplexDomain τ rows
  holomorphic : ∀ j, DifferentiableOn ℂ (lensPowerComponent τ rows k j) (lensComplexDomain τ rows)
  isolated_zero : ∀ z ∈ lensComplexDomain τ rows, (∀ j, lensPowerComponent τ rows k j z = 0) ↔ z = 0
  homogeneous : ∀ j, (lensLeadingPolynomial τ rows k j).IsHomogeneous k
  leading_nonzero : ∀ z : LensComplexSpace n, z ≠ 0 →
    ∃ j, MvPolynomial.eval (fun i => z i) (lensLeadingPolynomial τ rows k j) ≠ 0
  taylor_remainder :
    (fun z : LensComplexSpace n => (WithLp.toLp 2 (fun j => lensPowerComponent τ rows k j z -
      MvPolynomial.eval (fun i => z i) (lensLeadingPolynomial τ rows k j)) : LensComplexSpace m))
      =O[𝓝[≠] 0] (fun z => ‖z‖ ^ (k + 1))
  compact_sublevels : ∀ R : ℝ, 0 < R → R < 1 →
    IsCompact (closure (lensComplexDomain τ rows ∩ {z | lensPowerEnergy τ rows k z < R})) ∧
      closure (lensComplexDomain τ rows ∩ {z | lensPowerEnergy τ rows k z < R}) ⊆
        lensComplexDomain τ rows

/-- All source fields follow from the original actual geometric hypotheses. -/
theorem lensPowerMassInput_of_compact {n m : ℕ} (hn : 1 ≤ n) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n)
    (hK : IsCompact (stripBody rows)) {k : ℕ} (hk : 1 ≤ k) :
    LensPowerMassInput n m τ rows k where
  dimension_pos := hn
  degree_pos := hk
  open_domain := isOpen_lensComplexDomain τ rows
  zero_mem := zero_mem_lensComplexDomain hτ0 hτ1 rows
  holomorphic := lensPowerComponent_differentiableOn hτ0 hτ1 rows k
  isolated_zero := fun _ hz => lensPowerComponents_eq_zero_iff hτ0 hτ1 rows hK hk hz
  homogeneous := lensLeadingPolynomial_homogeneous τ rows k
  leading_nonzero := fun _ hz => lensLeadingPolynomial_nonzero hτ0 hτ1 rows hK hk hz
  taylor_remainder := lensPower_taylor_remainder hτ0 hτ1 rows k
  compact_sublevels := fun _ hR hR1 => lensPower_sublevel_compact_closure hτ0 hτ1 rows hK hk hR hR1

end
end Funk
