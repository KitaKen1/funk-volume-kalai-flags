import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.RealDeriv

/-! Two elementary half-plane criteria. The first is the strict form of a
nonnegative real-part bound. The second reduces univalence on a convex domain
to the real mean-value theorem along line segments. -/

open Set Metric

namespace Funk
noncomputable section

theorem re_pos_of_nonneg_on_connected {f : ℂ → ℂ} {s : Set ℂ}
    (hs : IsOpen s) (hconn : IsPreconnected s) (hf : AnalyticOnNhd ℂ f s)
    (hn : ∀ z ∈ s, 0 ≤ (f z).re) {a : ℂ} (ha : a ∈ s) (hp : 0 < (f a).re) :
    ∀ z ∈ s, 0 < (f z).re := by
  rcases hf.is_constant_or_isOpen hconn with ⟨c, hc⟩ | ho
  · intro z hz
    rw [hc z hz, ← hc a ha]
    exact hp
  · intro z hz
    by_contra h
    have hz0 : (f z).re = 0 := le_antisymm (not_lt.mp h) (hn z hz)
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp (ho s subset_rfl hs) (f z) ⟨z, hz, rfl⟩
    have hm : f z - (ε / 2 : ℝ) ∈ ball (f z) ε := by
      rw [mem_ball, dist_eq_norm]
      simp only [sub_sub_cancel_left, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      linarith
    obtain ⟨w, hw, he⟩ := hb hm
    have hh := hn w hw
    rw [he, Complex.sub_re, Complex.ofReal_re, hz0] at hh
    linarith

theorem injOn_of_deriv_re_pos {f : ℂ → ℂ} {s : Set ℂ}
    (hs : IsOpen s) (hc : Convex ℝ s) (hf : DifferentiableOn ℂ f s)
    (hp : ∀ z ∈ s, 0 < (deriv f z).re) : InjOn f s := by
  intro z hz w hw he
  by_contra hne
  have hd : w - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  let p : ℂ → ℂ := fun t => z + t * (w - z)
  have hm {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : p t ∈ s := by
    have h := hc hz hw (sub_nonneg.mpr ht.2) ht.1 (by ring : 1 - t + t = 1)
    convert h using 1
    simp only [p, Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  let q : ℝ → ℝ := fun t => ((f (p t) - f z) / (w - z)).re
  have hq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt q (deriv f (p t)).re t := by
    have hf' := (hf.differentiableAt (hs.mem_nhds (hm ht))).hasDerivAt
    have hp' : HasDerivAt p (w - z) (t : ℂ) := by
      convert ((hasDerivAt_id (t : ℂ)).mul_const (w - z)).const_add z using 1 <;> simp [p]
    have hg := (((hf'.comp (t : ℂ) hp').sub_const (f z)).div_const (w - z)).comp_ofReal
    have hg' := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hg
    simpa only [q, Function.comp_def, Complex.reCLM_apply, mul_div_cancel_right₀ _ hd] using hg'
  have hcq : ContinuousOn q (Icc (0 : ℝ) 1) :=
    fun t ht => (hq ht).continuousAt.continuousWithinAt
  have hstrict := strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) 1) hcq
    (fun t ht => by rw [(hq (interior_subset ht)).deriv]; exact hp _ (hm (interior_subset ht)))
  have h := hstrict (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
    (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1) (by norm_num)
  simp [q, p, he] at h

end
end Funk
