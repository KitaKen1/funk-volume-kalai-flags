import Funk.LensPowerLeading
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Operator.Asymptotics

/-! The literal Taylor remainder needed by the isolated-zero mass input.
Factor g(w) = w dslope(g,0,w); analyticity of dslope gives a first-order
remainder for its k-th power. Finite coordinates are then transported back
into the same complex Euclidean space used by the upstream mass statement. -/

open Set Metric Filter Asymptotics
open scoped Topology BigOperators

namespace Funk
noncomputable section

/-- Factorization avoids computing every coefficient below degree k. -/
theorem tiltedLensInverse_power_remainder {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (k : ℕ) :
    (fun w : ℂ => (tiltedLensInverse τ w) ^ k - (lensInverseSlope τ * w) ^ k)
      =O[𝓝 0] (fun w => ‖w‖ ^ (k + 1)) := by
  have ha := tiltedLensInverse_analyticOnNhd hτ0 hτ1 0
    (lensGraphBody_zero_mem_interior hτ0 hτ1)
  obtain ⟨p, hp⟩ := ha
  have hs : AnalyticAt ℂ (dslope (tiltedLensInverse τ) 0) 0 :=
    ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  have hb : (fun w : ℂ => (dslope (tiltedLensInverse τ) 0 w) ^ k - (lensInverseSlope τ) ^ k)
      =O[𝓝 0] (fun w => w) := by
    simpa only [Pi.pow_apply, dslope_same, lensInverseSlope, sub_zero] using
      (hs.differentiableAt.pow k).isBigO_sub
  have hw := ((isBigO_refl (fun w : ℂ => w) (𝓝 0)).norm_right).pow k
  apply (hw.mul hb.norm_right).congr
  · intro w
    have he : w * dslope (tiltedLensInverse τ) 0 w = tiltedLensInverse τ w := by
      simpa only [sub_zero, smul_eq_mul, tiltedLensInverse_zero hτ0 hτ1] using
        sub_smul_dslope (tiltedLensInverse τ) (0 : ℂ) w
    calc
      w ^ k * ((dslope (tiltedLensInverse τ) 0 w) ^ k - (lensInverseSlope τ) ^ k) =
          (w * dslope (tiltedLensInverse τ) 0 w) ^ k - (lensInverseSlope τ * w) ^ k := by
        rw [mul_sub, mul_pow, mul_pow, mul_comm (lensInverseSlope τ ^ k)]
      _ = _ := by rw [he]
  · intro w
    exact (pow_succ ‖w‖ k).symm

/-- Each actual row remainder has the required degree in the original input norm. -/
theorem lensPowerComponent_taylor_remainder {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ) (j : Fin m) :
    (fun z : LensComplexSpace n => lensPowerComponent τ rows k j z -
      MvPolynomial.eval (fun i => z i) (lensLeadingPolynomial τ rows k j))
      =O[𝓝 0] (fun z => ‖z‖ ^ (k + 1)) := by
  have ht : Tendsto (lensComplexRow (rows j)) (𝓝 0) (𝓝 (0 : ℂ)) := by
    simpa only [map_zero] using (lensComplexRow (rows j)).continuous.tendsto 0
  have hb := (tiltedLensInverse_power_remainder hτ0 hτ1 k).comp_tendsto ht
  have hl := ((lensComplexRow (rows j)).isBigO_id (𝓝 0)).norm_left.norm_right.pow (k + 1)
  simpa only [Function.comp_def, lensPowerComponent, lensLeadingPolynomial_eval] using hb.trans hl

/-- Exact Euclidean vector and punctured-neighborhood convention of MassHypotheses. -/
theorem lensPower_taylor_remainder {n m : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : Fin m → Space n) (k : ℕ) :
    (fun z : LensComplexSpace n => (WithLp.toLp 2 (fun j => lensPowerComponent τ rows k j z -
      MvPolynomial.eval (fun i => z i) (lensLeadingPolynomial τ rows k j)) : LensComplexSpace m))
      =O[𝓝[≠] 0] (fun z => ‖z‖ ^ (k + 1)) := by
  have hp : (fun z : LensComplexSpace n => (fun j => lensPowerComponent τ rows k j z -
      MvPolynomial.eval (fun i => z i) (lensLeadingPolynomial τ rows k j)))
      =O[𝓝 0] (fun z => ‖z‖ ^ (k + 1)) :=
    isBigO_pi.mpr (lensPowerComponent_taylor_remainder hτ0 hτ1 rows k)
  exact (((EuclideanSpace.equiv (Fin m) ℂ).symm.toContinuousLinearMap.isBigO_comp _ (𝓝 0)).trans hp).mono nhdsWithin_le_nhds

end
end Funk
