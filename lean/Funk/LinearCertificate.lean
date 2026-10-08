import Funk.Polar
import Mathlib.Tactic

/-! The soundness direction of a finite linear-inequality certificate.
A search program may find nonnegative weights; the kernel verifies the weights'
properties and exact identities. No completeness theorem for LP is required.
-/

namespace Funk

theorem linearCertificate_sound {n : ℕ} {ι : Type*} [Fintype ι]
    (rows : ι → Space n) (bounds weights : ι → ℝ) (target x : Space n) (bound : ℝ)
    (hweights : ∀ i, 0 ≤ weights i)
    (hrows : target = ∑ i, weights i • rows i)
    (hbound : ∑ i, weights i * bounds i ≤ bound)
    (hx : ∀ i, dotProduct (rows i) x ≤ bounds i) :
    dotProduct target x ≤ bound := by
  rw [hrows, sum_dotProduct]
  simp only [smul_dotProduct, smul_eq_mul]
  exact (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hx i) (hweights i))).trans hbound

/-- A certificate proves polar membership directly for the actual half-space intersection. -/
theorem linearCertificate_mem_polar {n : ℕ} {ι : Type*} [Fintype ι]
    (rows : ι → Space n) (bounds weights : ι → ℝ) (target : Space n)
    (hweights : ∀ i, 0 ≤ weights i)
    (hrows : target = ∑ i, weights i • rows i)
    (hbound : ∑ i, weights i * bounds i ≤ 1) :
    target ∈ coordinatePolar {x | ∀ i, dotProduct (rows i) x ≤ bounds i} := by
  intro x hx
  exact linearCertificate_sound rows bounds weights target x 1 hweights hrows hbound hx

end Funk
