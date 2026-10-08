import Funk.CollisionResidual
import Mathlib.Analysis.Calculus.Deriv.Pi

/-! Coordinate derivatives of the actual collision residual. A genuine extra
row has two nonzero basis coefficients; their mixed derivative is nonzero.
Passing from this curvature statement to a null set is a separate obligation. -/

open Set Matrix Filter
open scoped Topology

namespace Funk
noncomputable section

theorem hasDerivAt_dotProduct_update {n : ℕ} (coeff t : Space n) (i : Fin n) (u : ℝ) :
    HasDerivAt (fun v => dotProduct coeff (Function.update t i v)) (coeff i) u := by
  have hd := ((dotProductBilin ℝ ℝ coeff).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt
    u (hasDerivAt_update t i u)
  convert hd using 1
  · rfl
  · change coeff i = dotProduct coeff (Pi.single i 1)
    simp

def branchCollisionSlope {n : ℕ} (τ : ℝ) (b : Fin n → Bool) (σ : Bool)
    (coeff : Space n) (i : Fin n) (t : Space n) : ℝ :=
  coeff i * (lensBranchProfileSlope τ (b i) (t i) -
    lensBranchProfileSlope τ σ (dotProduct coeff t))

theorem hasDerivAt_branchCollisionResidual_update {n : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (b : Fin n → Bool) (σ : Bool)
    (coeff t : Space n) (i : Fin n) (hi : t i ∈ Ioo (-1) 1)
    (ht : dotProduct coeff t ∈ Ioo (-1) 1) :
    HasDerivAt (fun v => branchCollisionResidual τ b σ coeff (Function.update t i v))
      (branchCollisionSlope τ b σ coeff i t) (t i) := by
  have hd (j : Fin n) :
      HasDerivAt (fun v => coeff j * lensBranchProfile τ (b j) (Function.update t i v j))
        (if j = i then coeff i * lensBranchProfileSlope τ (b i) (t i) else 0) (t i) := by
    by_cases hj : j = i
    · subst j
      simpa using (hasDerivAt_lensBranchProfile hτ0 hτ1 (b i) hi).const_mul (coeff i)
    · simpa [Function.update_of_ne hj, hj] using
        hasDerivAt_const (t i) (coeff j * lensBranchProfile τ (b j) (t j))
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hd j)
  have hc := (hasDerivAt_lensBranchProfile hτ0 hτ1 σ ht).comp_of_eq (t i)
    (hasDerivAt_dotProduct_update coeff t i (t i)) (by simp)
  convert hs.sub hc using 1
  · rfl
  · simp [branchCollisionSlope]
    ring

theorem hasDerivAt_branchCollisionSlope_update {n : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (b : Fin n → Bool) (σ : Bool)
    (coeff t : Space n) (i j : Fin n) (hij : i ≠ j)
    (ht : dotProduct coeff t ∈ Ioo (-1) 1) :
    HasDerivAt (fun u => branchCollisionSlope τ b σ coeff i (Function.update t j u))
      (-coeff i * coeff j * lensBranchProfileCurvature τ σ (dotProduct coeff t)) (t j) := by
  have hc := (hasDerivAt_lensBranchProfileSlope hτ0 hτ1 σ ht).comp_of_eq (t j)
    (hasDerivAt_dotProduct_update coeff t j (t j)) (by simp)
  have hd := ((hasDerivAt_const (t j) (lensBranchProfileSlope τ (b i) (t i))).sub hc).const_mul
    (coeff i)
  convert hd using 1
  · funext u
    simp [branchCollisionSlope, Function.update_of_ne hij]
  · ring

/-- A mixed second derivative never vanishes in the strict-height domain. -/
theorem branchCollision_mixed_deriv_ne_zero {n : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (b : Fin n → Bool) (σ : Bool)
    (coeff t : Space n) (i j : Fin n) (hij : i ≠ j) (hi : coeff i ≠ 0) (hj : coeff j ≠ 0)
    (ht : dotProduct coeff t ∈ Ioo (-1) 1) :
    deriv (fun u => branchCollisionSlope τ b σ coeff i (Function.update t j u)) (t j) ≠ 0 := by
  rw [(hasDerivAt_branchCollisionSlope_update hτ0 hτ1 b σ coeff t i j hij ht).deriv]
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hi) hj)
    (lensBranchProfileCurvature_ne_zero hτ0 hτ1 σ ht)

/-- The derivative of the coordinate derivative of the residual itself. -/
theorem hasDerivAt_branchCollision_mixed {n : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (b : Fin n → Bool) (σ : Bool)
    (coeff t : Space n) (i j : Fin n) (hij : i ≠ j)
    (hi : t i ∈ Ioo (-1) 1) (ht : dotProduct coeff t ∈ Ioo (-1) 1) :
    HasDerivAt (fun u => deriv
      (fun v => branchCollisionResidual τ b σ coeff
        (Function.update (Function.update t j u) i v)) (t i))
      (-coeff i * coeff j * lensBranchProfileCurvature τ σ (dotProduct coeff t))
      (t j) := by
  have hc := (hasDerivAt_dotProduct_update coeff t j (t j)).continuousAt
  have hm : ∀ᶠ u in 𝓝 (t j), dotProduct coeff (Function.update t j u) ∈ Ioo (-1) 1 := by
    apply hc.preimage_mem_nhds
    simpa only [Function.update_eq_self] using isOpen_Ioo.mem_nhds ht
  have he : (fun u => deriv
      (fun v => branchCollisionResidual τ b σ coeff
        (Function.update (Function.update t j u) i v)) (t i)) =ᶠ[𝓝 (t j)]
      (fun u => branchCollisionSlope τ b σ coeff i (Function.update t j u)) := by
    filter_upwards [hm] with u hu
    have hid : Function.update t j u i ∈ Ioo (-1) 1 := by
      simpa only [Function.update_of_ne hij] using hi
    have hd := hasDerivAt_branchCollisionResidual_update hτ0 hτ1 b σ coeff
      (Function.update t j u) i hid hu
    simpa only [Function.update_of_ne hij] using hd.deriv
  exact (hasDerivAt_branchCollisionSlope_update hτ0 hτ1 b σ coeff t i j hij ht).congr_of_eventuallyEq he

def branchCollisionMixedDeriv {n : ℕ} (τ : ℝ) (b : Fin n → Bool) (σ : Bool)
    (coeff : Space n) (i j : Fin n) (t : Space n) : ℝ :=
  deriv (fun u => deriv
    (fun v => branchCollisionResidual τ b σ coeff
      (Function.update (Function.update t j u) i v)) (t i)) (t j)

theorem branchCollisionMixedDeriv_ne_zero {n : ℕ} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (b : Fin n → Bool) (σ : Bool)
    (coeff t : Space n) (i j : Fin n) (hij : i ≠ j)
    (hci : coeff i ≠ 0) (hcj : coeff j ≠ 0)
    (hi : t i ∈ Ioo (-1) 1) (ht : dotProduct coeff t ∈ Ioo (-1) 1) :
    branchCollisionMixedDeriv τ b σ coeff i j t ≠ 0 := by
  unfold branchCollisionMixedDeriv
  rw [(hasDerivAt_branchCollision_mixed hτ0 hτ1 b σ coeff t i j hij hi ht).deriv]
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hci) hcj)
    (lensBranchProfileCurvature_ne_zero hτ0 hτ1 σ ht)

/-- Every nonzero genuine extra row has a nonzero mixed derivative at every
strict-height point. This conclusion is local curvature, not nullity. -/
theorem extra_row_exists_nonzero_mixed_deriv {n : ℕ} {ι : Type*} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (rows : ι → Space n)
    (hirr : SignedIrredundant rows) (s : Fin n → ι)
    (hB : Matrix.det (fun k => rows (s k)) ≠ 0) {a : ι} (ha : a ∉ range s)
    (ha0 : rows a ≠ 0) (b : Fin n → Bool) (σ : Bool) (X : Space n)
    (hX : ∀ k, |dotProduct (rows (s k)) X| < 1)
    (haX : |dotProduct (rows a) X| < 1) :
    ∃ i j : Fin n, i ≠ j ∧ branchCollisionMixedDeriv τ b σ
      (rowBasisCoefficients (fun k => rows (s k)) (rows a)) i j
      (basisMap (fun k => rows (s k)) X) ≠ 0 := by
  obtain ⟨i, j, hij, hi, hj⟩ := extra_row_coefficients_two_nonzero rows hirr s hB ha ha0
  refine ⟨i, j, hij, branchCollisionMixedDeriv_ne_zero hτ0 hτ1 b σ _ _ i j hij hi hj ?_ ?_⟩
  · exact abs_lt.mp (hX i)
  · rw [rowBasisCoefficients_dot hB]
    exact abs_lt.mp haX

end
end Funk
