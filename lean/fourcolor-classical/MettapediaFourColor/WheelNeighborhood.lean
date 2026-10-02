import MettapediaFourColor.FacialStarCompletion
import MettapediaFourColor.ExceptionalCoreLocalInjectivity

/-!
# Exact cyclic neighbourhoods

The outgoing rotation of a vertex constructs its entire ordered wheel.
When ambient triangles are facial, the rim has exactly its consecutive
edges. The construction retains actual darts and works at arbitrary degree.
-/

namespace FourColor.WheelNeighborhood

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalOverlap ExceptionalCoreOrientation

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
  (rotation : Data G) (d : G.Dart) {n : ℕ}

def around (i : ℕ) : G.Dart := (rotation.vertexRotation ^ i) d

def neighbor (i : Fin n) : V := (around rotation d i.val).snd

omit [G.LocallyFinite] in
theorem around_fst (i : ℕ) : (around rotation d i).fst = d.fst :=
  FacialStarCompletion.pow_fst rotation d i

omit [G.LocallyFinite] in
theorem around_step (i : ℕ) :
    rotation.vertexRotation (around rotation d i) = around rotation d (i + 1) := by
  simp only [around, pow_succ', Equiv.Perm.mul_apply]

omit [G.LocallyFinite] in
theorem adjacent (i : Fin n) : G.Adj d.fst (neighbor rotation d i) := by
  simpa only [neighbor, around_fst] using (around rotation d i.val).adj

def next (positive : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ positive⟩

variable [Finite V]

theorem around_next (cyclic : rotation.IsVertexwiseCyclic)
    (degree : G.degree d.fst = n) (positive : 0 < n) (i : Fin n) :
    rotation.vertexRotation (around rotation d i.val) =
      around rotation d (next positive i).val := by
  rw [around_step]
  by_cases hi : i.val + 1 < n
  · simp only [next, Nat.mod_eq_of_lt hi]
  · have hi : i.val + 1 = n := by omega
    simp only [next, hi, Nat.mod_self]
    change (rotation.vertexRotation ^ n) d = d
    rw [← degree]
    exact FacialStarCompletion.pow_degree rotation cyclic d

theorem corner (cyclic : rotation.IsVertexwiseCyclic)
    (degree : G.degree d.fst = n) (positive : 0 < n) (i : Fin n) :
    Corner rotation d.fst (neighbor rotation d i) (neighbor rotation d (next positive i)) := by
  refine ⟨adjacent rotation d i, adjacent rotation d (next positive i), ?_⟩
  have darts (j : Fin n) :
      (⟨(d.fst, neighbor rotation d j), adjacent rotation d j⟩ : G.Dart) =
        around rotation d j.val := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext (around_fst rotation d j.val).symm rfl
  rw [darts, darts]
  exact around_next rotation d cyclic degree positive i

theorem neighbor_injective (cyclic : rotation.IsVertexwiseCyclic)
    (degree : G.degree d.fst = n) (positive : 0 < n) :
    Function.Injective (neighbor rotation d : Fin n → V) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  apply ExceptionalCoreLocalInjectivity.corner_chain_injective rotation cyclic
    d.fst positive (neighbor rotation d) (adjacent rotation d)
  · intro i hi
    have h := corner rotation d cyclic degree positive ⟨i, by omega⟩
    have eq : next positive ⟨i, by omega⟩ = (⟨i + 1, hi⟩ : Fin n) := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt hi
    simpa only [eq] using h
  · omega

theorem covers (cyclic : rotation.IsVertexwiseCyclic)
    (degree : G.degree d.fst = n) {w : V} (adj : G.Adj d.fst w) :
    ∃ i : Fin n, neighbor rotation d i = w := by
  obtain ⟨i, hi, eq⟩ := FacialStarCompletion.covers rotation cyclic d
    (⟨(d.fst, w), adj⟩ : G.Dart) rfl
  exact ⟨⟨i, degree ▸ hi⟩, congrArg (fun e : G.Dart => e.snd) eq⟩

theorem corner_iff (cyclic : rotation.IsVertexwiseCyclic)
    (degree : G.degree d.fst = n) (positive : 0 < n) (i j : Fin n) :
    Corner rotation d.fst (neighbor rotation d i) (neighbor rotation d j) ↔
      j = next positive i := by
  constructor
  · rintro ⟨_, _, h⟩
    obtain ⟨_, _, k⟩ := corner rotation d cyclic degree positive i
    apply neighbor_injective rotation d cyclic degree positive
    have eq := congrArg (fun e : G.Dart => e.snd) (h.symm.trans k)
    exact eq
  · rintro rfl
    exact corner rotation d cyclic degree positive i

/-- Facial triangles exclude every nonconsecutive chord of the rim. -/
theorem rim_adj_iff (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (degree : G.degree d.fst = n) (positive : 0 < n)
    (facial : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a →
      Corner rotation a b c ∨ Corner rotation a c b) (i j : Fin n) :
    G.Adj (neighbor rotation d i) (neighbor rotation d j) ↔
      j = next positive i ∨ i = next positive j := by
  constructor
  · intro h
    rcases facial _ _ _ (adjacent rotation d i) h (adjacent rotation d j).symm with h | h
    · exact Or.inl ((corner_iff rotation d cyclic degree positive i j).mp h)
    · exact Or.inr ((corner_iff rotation d cyclic degree positive j i).mp h)
  · rintro (rfl | rfl)
    · obtain ⟨h, _, _⟩ := Corner.rotate rotation tri (corner rotation d cyclic degree positive i)
      exact h
    · obtain ⟨h, _, _⟩ := Corner.rotate rotation tri (corner rotation d cyclic degree positive j)
      exact h.symm

def vertex (i : Option (Fin n)) : V := i.elim d.fst (neighbor rotation d)

theorem vertex_injective (cyclic : rotation.IsVertexwiseCyclic)
    (degree : G.degree d.fst = n) (positive : 0 < n) :
    Function.Injective (vertex rotation d : Option (Fin n) → V) := by
  intro i j eq
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j => exact ((adjacent rotation d j).ne eq).elim
  | some i =>
    cases j with
    | none => exact ((adjacent rotation d i).ne eq.symm).elim
    | some j => exact congrArg some (neighbor_injective rotation d cyclic degree positive eq)

end FourColor.WheelNeighborhood
