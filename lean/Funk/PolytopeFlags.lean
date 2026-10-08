import Funk.PolytopeFaces
import Funk.IntervalFlags
import Mathlib.Analysis.Convex.Topology

/-! Finiteness of the frozen geometric FullFlag type in every dimension.
Vertex subset codes also give order tests and finite enumeration certificates.
No symmetry, interior assumption, simpliciality, or genericity is required. -/

open Set

namespace Funk

noncomputable section

theorem polytopeFace_isFinitePolytope {n : ℕ} {P : Set (Space n)}
    (hP : IsFinitePolytope P) (F : PolytopeFace P) : IsFinitePolytope F.val := by
  obtain ⟨vertices, rfl⟩ := hP
  exact ⟨faceVertexCode vertices F.val,
    face_eq_convexHull_code vertices F.val F.property.1 F.property.2⟩

theorem finitePolytope_isCompact {n : ℕ} {P : Set (Space n)}
    (hP : IsFinitePolytope P) : IsCompact P := by
  obtain ⟨vertices, rfl⟩ := hP
  exact vertices.finite_toSet.isCompact_convexHull ℝ

theorem polytopeFace_isCompact {n : ℕ} {P : Set (Space n)}
    (hP : IsFinitePolytope P) (F : PolytopeFace P) : IsCompact F.val :=
  finitePolytope_isCompact (polytopeFace_isFinitePolytope hP F)

/-- Inclusion of actual faces is exactly inclusion of their finite vertex codes. -/
theorem face_subset_iff_code_subset {n : ℕ} (vertices : Finset (Space n))
    (F G : PolytopeFace (convexHull ℝ (vertices : Set (Space n)))) :
    F.val ⊆ G.val ↔ faceVertexCode vertices F.val ⊆ faceVertexCode vertices G.val := by
  classical
  constructor
  · intro h x hx
    simp only [faceVertexCode, Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, h hx.2⟩
  · intro h
    rw [face_eq_convexHull_code vertices F.val F.property.1 F.property.2,
      face_eq_convexHull_code vertices G.val G.property.1 G.property.2]
    exact convexHull_mono h

/-- Encode each actual face of a flag in the finite type of actual faces. -/
def fullFlagFaceMap {n : ℕ} {P : Set (Space n)} (F : FullFlag P) :
    Fin n → PolytopeFace P :=
  fun i => ⟨F.faces i, F.convex i, F.extreme i⟩

theorem fullFlagFaceMap_injective {n : ℕ} (P : Set (Space n)) :
    Function.Injective (fullFlagFaceMap (P := P)) := by
  intro F G h
  apply fullFlag_ext
  funext i
  exact congrArg Subtype.val (congrFun h i)

/-- The finiteness conjunct of KalaiFullFlagsGoal, proved for every finite polytope. -/
theorem fullFlag_finite {n : ℕ} {P : Set (Space n)} (hP : IsFinitePolytope P) :
    Finite (FullFlag P) := by
  let : Finite (PolytopeFace P) := polytopeFace_finite hP
  exact Finite.of_injective fullFlagFaceMap (fullFlagFaceMap_injective P)

/-- Coarse size bound for the finite face code space, not Kalai's lower bound. -/
theorem polytopeFace_card_le {n : ℕ} (vertices : Finset (Space n)) :
    Nat.card (PolytopeFace (convexHull ℝ (vertices : Set (Space n)))) ≤
      2 ^ vertices.card := by
  classical
  let code : PolytopeFace (convexHull ℝ (vertices : Set (Space n))) →
      {s : Finset (Space n) // s ∈ vertices.powerset} :=
    fun F => ⟨faceVertexCode vertices F.val,
      Finset.mem_powerset.mpr (faceVertexCode_subset vertices F.val)⟩
  have hi : Function.Injective code := by
    intro F G h
    exact faceVertexCode_injective vertices (congrArg Subtype.val h)
  have h := Nat.card_le_card_of_injective code hi
  change Nat.card (PolytopeFace (convexHull ℝ (vertices : Set (Space n)))) ≤
    Nat.card vertices.powerset at h
  rwa [Nat.card_eq_finsetCard, Finset.card_powerset] at h

theorem fullFlag_card_le {n : ℕ} (vertices : Finset (Space n)) :
    Nat.card (FullFlag (convexHull ℝ (vertices : Set (Space n)))) ≤
      (2 ^ vertices.card) ^ n := by
  let P := convexHull ℝ (vertices : Set (Space n))
  let : Finite (PolytopeFace P) := polytopeFace_finite ⟨vertices, rfl⟩
  calc
    Nat.card (FullFlag P) ≤ Nat.card (Fin n → PolytopeFace P) :=
      Nat.card_le_card_of_injective fullFlagFaceMap (fullFlagFaceMap_injective P)
    _ = Nat.card (PolytopeFace P) ^ n := by rw [Nat.card_fun]; simp
    _ ≤ (2 ^ vertices.card) ^ n := Nat.pow_le_pow_left (polytopeFace_card_le vertices) n

/-- Verify a supplied enumeration, without having to discover flags in Lean. -/
theorem fullFlag_card_of_enumeration {n m : ℕ} {P : Set (Space n)}
    (flags : Fin m → FullFlag P) (hflags : Function.Bijective flags) :
    Nat.card (FullFlag P) = m := by
  rw [← Nat.card_congr (Equiv.ofBijective flags hflags)]
  simp

/-- A supplied injective family certifies a lower bound once actual finiteness is proved. -/
theorem fullFlag_card_lower_of_injective {n m : ℕ} {P : Set (Space n)}
    (hP : IsFinitePolytope P) (flags : Fin m → FullFlag P)
    (hflags : Function.Injective flags) : m ≤ Nat.card (FullFlag P) := by
  let : Finite (FullFlag P) := fullFlag_finite hP
  simpa using Nat.card_le_card_of_injective flags hflags

end
end Funk
