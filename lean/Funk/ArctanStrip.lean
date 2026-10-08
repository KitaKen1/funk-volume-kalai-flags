import Funk.LensBoundary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv
import Mathlib.Analysis.Convex.Basic

/-! The complex arctangent sends the unit disk into a convex vertical strip;
tangent sends that strip back into the disk. -/

open Set

namespace Funk
noncomputable section

def arctanStrip : Set ℂ := {z | -Real.pi / 4 < z.re ∧ z.re < Real.pi / 4}

theorem arctanStrip_isOpen : IsOpen arctanStrip :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

theorem arctanStrip_convex : Convex ℝ arctanStrip :=
  (convex_Ioo (-Real.pi / 4) (Real.pi / 4)).linear_preimage Complex.reCLM.toLinearMap

theorem arctanCayley_re_pos_disk {z : ℂ} (hz : ‖z‖ < 1) :
    0 < (arctanCayley z).re := by
  have hd : 1 - z * Complex.I ≠ 0 := by
    intro h
    have hnorm := congrArg norm (sub_eq_zero.mp h)
    simp at hnorm
    linarith
  rw [arctanCayley_re]
  exact div_pos (by nlinarith [norm_nonneg z]) (Complex.normSq_pos.mpr hd)

theorem arctan_mem_strip {z : ℂ} (hz : ‖z‖ < 1) : Complex.arctan z ∈ arctanStrip := by
  have harg := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr
    (Or.inl (arctanCayley_re_pos_disk hz)))
  have he : (Complex.arctan z).re = (arctanCayley z).arg / 2 := by
    change (-Complex.I / 2 * Complex.log (arctanCayley z)).re = _
    simp [Complex.mul_re, Complex.log_im]
    ring
  change -Real.pi / 4 < (Complex.arctan z).re ∧ (Complex.arctan z).re < Real.pi / 4
  rw [he]
  constructor <;> linarith [harg.1, harg.2]

theorem norm_cos_sq_sub_norm_sin_sq (z : ℂ) :
    ‖Complex.cos z‖ ^ 2 - ‖Complex.sin z‖ ^ 2 = Real.cos (2 * z.re) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    Complex.cos_eq z, Complex.sin_eq z, Real.cos_two_mul']
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cosh_ofReal_re,
    Complex.sinh_ofReal_re]
  linear_combination (Real.cos z.re ^ 2 - Real.sin z.re ^ 2) *
    Real.cosh_sq_sub_sinh_sq z.im

theorem norm_sin_lt_norm_cos_of_mem_strip {z : ℂ} (hz : z ∈ arctanStrip) :
    ‖Complex.sin z‖ < ‖Complex.cos z‖ := by
  have hp : 0 < Real.cos (2 * z.re) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have he := norm_cos_sq_sub_norm_sin_sq z
  nlinarith [norm_nonneg (Complex.sin z), norm_nonneg (Complex.cos z)]

theorem cos_ne_zero_of_mem_strip {z : ℂ} (hz : z ∈ arctanStrip) : Complex.cos z ≠ 0 := by
  exact norm_pos_iff.mp ((norm_nonneg _).trans_lt (norm_sin_lt_norm_cos_of_mem_strip hz))

theorem norm_tan_lt_one_of_mem_strip {z : ℂ} (hz : z ∈ arctanStrip) : ‖Complex.tan z‖ < 1 := by
  rw [Complex.tan_eq_sin_div_cos, norm_div]
  exact (div_lt_one (norm_pos_iff.mpr (cos_ne_zero_of_mem_strip hz))).mpr
    (norm_sin_lt_norm_cos_of_mem_strip hz)

theorem hasDerivAt_tan_strip {z : ℂ} (hz : z ∈ arctanStrip) :
    HasDerivAt Complex.tan (1 + Complex.tan z ^ 2) z := by
  have hn := cos_ne_zero_of_mem_strip hz
  convert Complex.hasDerivAt_tan hn using 1
  rw [one_div, ← Complex.inv_one_add_tan_sq hn, inv_inv]

theorem tan_arctan_disk {z : ℂ} (hz : ‖z‖ < 1) : Complex.tan (Complex.arctan z) = z := by
  apply Complex.tan_arctan
  · intro he; simp [he] at hz
  · intro he; simp [he] at hz

end
end Funk
