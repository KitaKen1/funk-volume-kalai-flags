import Funk.ScalarCertificate
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Matrix.Mul

/-! Coordinate polar and explicit feasible-simplex containment.
The conclusion is an actual inclusion of subsets of `Fin n → ℝ`.
Volume, linear independence, and non-overlap are separate obligations.
-/

namespace Funk

noncomputable section

abbrev Space (n : ℕ) := Fin n → ℝ

/-- The ordinary coordinate polar, with threshold one. -/
def coordinatePolar {n : ℕ} (K : Set (Space n)) : Set (Space n) :=
  {y | ∀ x ∈ K, dotProduct y x ≤ 1}

/-- Translation by `-x`, expressed as an image to keep membership concrete. -/
def translate {n : ℕ} (K : Set (Space n)) (x : Space n) : Set (Space n) :=
  (fun z => z - x) '' K

/-- A symmetric intersection of strips. Boundedness and full dimension are not assumed here. -/
def stripBody {n : ℕ} {ι : Type*} (rows : ι → Space n) : Set (Space n) :=
  {x | ∀ i, |dotProduct (rows i) x| ≤ 1}

theorem zero_mem_coordinatePolar {n : ℕ} (K : Set (Space n)) :
    0 ∈ coordinatePolar K := by
  intro x hx
  simp

theorem coordinatePolar_antitone {n : ℕ} {K L : Set (Space n)} (h : K ⊆ L) :
    coordinatePolar L ⊆ coordinatePolar K := by
  intro y hy x hx
  exact hy x (h hx)

theorem convex_coordinatePolar {n : ℕ} (K : Set (Space n)) :
    Convex ℝ (coordinatePolar K) := by
  intro u hu v hv a b ha hb hab x hx
  change dotProduct (a • u + b • v) x ≤ 1
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
  calc
    a * dotProduct u x + b * dotProduct v x ≤ a * 1 + b * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left (hu x hx) ha)
        (mul_le_mul_of_nonneg_left (hv x hx) hb)
    _ = 1 := by linarith

/-- The known answer is used as the witness. -/
def polarVertex {n : ℕ} (τ ε : ℝ) (row X : Space n) : Space n :=
  (ε / (1 - ε * τ * dotProduct row X)) • row

theorem polarVertex_mem {n : ℕ} {ι : Type*} {rows : ι → Space n}
    {τ ε : ℝ} {X : Space n} (hτ₀ : 0 ≤ τ) (hτ₁ : τ < 1)
    (hε : ε = 1 ∨ ε = -1) (hX : X ∈ stripBody rows) (i : ι) :
    polarVertex τ ε (rows i) X ∈ coordinatePolar (translate (stripBody rows) (τ • X)) := by
  rintro _ ⟨z, hz, rfl⟩
  change dotProduct (polarVertex τ ε (rows i) X) (z - τ • X) ≤ 1
  simp only [polarVertex, smul_dotProduct, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  calc
    ε / (1 - ε * τ * dotProduct (rows i) X) * dotProduct (rows i) z -
        τ * (ε / (1 - ε * τ * dotProduct (rows i) X) * dotProduct (rows i) X) =
        (ε * dotProduct (rows i) z - ε * τ * dotProduct (rows i) X) /
          (1 - ε * τ * dotProduct (rows i) X) := by ring
    _ ≤ 1 := vertex_pairing_le_one hτ₀ hτ₁ hε (hX i) (hz i)

/-- Any selected family of certified vertices, together with the origin, has its
convex hull in the translated polar. Taking `κ = Fin n` gives the intended simplex. -/
theorem feasibleHull_subset_polar {n : ℕ} {ι κ : Type*} {rows : ι → Space n}
    {τ : ℝ} {X : Space n} (hτ₀ : 0 ≤ τ) (hτ₁ : τ < 1)
    (hX : X ∈ stripBody rows) (selected : κ → ι) (signs : κ → ℝ)
    (hsigns : ∀ k, signs k = 1 ∨ signs k = -1) :
    convexHull ℝ (insert 0 (Set.range (fun k => polarVertex τ (signs k) (rows (selected k)) X)))
      ⊆ coordinatePolar (translate (stripBody rows) (τ • X)) := by
  apply convexHull_min _ (convex_coordinatePolar _)
  rintro y (rfl | ⟨k, rfl⟩)
  · exact zero_mem_coordinatePolar _
  · exact polarVertex_mem hτ₀ hτ₁ (hsigns k) hX (selected k)

end
end Funk
