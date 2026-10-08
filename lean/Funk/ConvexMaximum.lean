import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.LocallyConvex.Separation

/-! A convex-valued maximum principle.  Complex separation and exp turn a
real linear bound into the usual maximum modulus principle. -/

open Set

namespace Funk
noncomputable section

/-- If all boundary values lie in a closed convex set, so do all values on
the closure. This is independent of the particular lens construction. -/
theorem holomorphic_mem_closed_convex_of_frontier {f : ℂ → ℂ} {U K : Set ℂ}
    (hU : Bornology.IsBounded U) (hf : DiffContOnCl ℂ f U)
    (hK : Convex ℝ K) (hc : IsClosed K)
    (hb : ∀ z ∈ frontier U, f z ∈ K) {z : ℂ} (hz : z ∈ closure U) : f z ∈ K := by
  by_contra hn
  obtain ⟨l, c, hl, hlt⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) hK hc hn
  have hg : DiffContOnCl ℂ (fun w => Complex.exp (l (f w))) U :=
    Complex.differentiable_exp.comp_diffContOnCl (l.differentiable.comp_diffContOnCl hf)
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le hU hg
    (C := Real.exp c) (fun w hw => ?_) hz
  · rw [Complex.norm_exp, Real.exp_le_exp] at hmax
    exact (hlt.trans_le hmax).false
  · rw [Complex.norm_exp, Real.exp_le_exp]
    exact (hl _ (hb w hw)).le

end
end Funk
