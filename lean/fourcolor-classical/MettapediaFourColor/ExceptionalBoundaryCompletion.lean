import MettapediaFourColor.FacialStarCompletion
import MettapediaFourColor.ExceptionalCoreInduced

/-!
# The eleven-port free completion in the actual ambient rotation

The full cyclic source stars are read as rotation powers of retained core
darts. Eight facial seam identities prove that neighbouring core stars
agree on their shared boundary ports. The resulting graph homomorphism
retains all nineteen source vertices and all core-star turns. Ring labels
may have equal ambient images; no injectivity is assumed for them.
-/

namespace FourColor.ExceptionalBoundaryCompletion

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalCore ExceptionalCoreOrientation ExceptionalCoreLocalInjectivity
open ExceptionalOverlap

set_option maxRecDepth 32768

def firstNeighbor : Fin 8 → Fin 8 := ![7, 4, 3, 6, 0, 2, 1, 5]

theorem first_edge : ∀ i, core.Adj i (firstNeighbor i) := by decide +kernel

theorem first_spoke : ∀ i,
    spoke i ⟨0, (star_specs i).1⟩ = firstNeighbor i := by decide +kernel

theorem degree_pos : ∀ i : Fin 8, 0 < coreDegree i := by decide +kernel

theorem degree_values : coreDegree = ![8, 5, 5, 7, 5, 5, 5, 5] := by decide +kernel

theorem star_lengths : (fun i => (star i).length) = ![5, 2, 2, 4, 3, 4, 4, 2] := by
  decide +kernel

theorem seam_last : ∀ i : Fin 8,
    spoke (firstNeighbor i)
      ⟨(star (firstNeighbor i)).length - 1, by
        have := (star_specs (firstNeighbor i)).1; omega⟩ = i := by
  decide +kernel

def shift : Fin 8 → ℕ := ![2, 2, 2, 2, 1, 0, 0, 1]

def fullRow (i : Fin 8) : List (Fin 19) :=
  (input.internalStar (i.natAdd 11)).rotate (shift i)

def fullSpoke (i : Fin 8) (p : Fin (coreDegree i)) : Fin 19 :=
  (fullRow i).getD p.val 0

def nextPos (i : Fin 8) (p : Fin (coreDegree i)) : Fin (coreDegree i) :=
  ⟨(p.val + 1) % coreDegree i, Nat.mod_lt _ (degree_pos i)⟩

theorem fullRow_length : ∀ i, (fullRow i).length = coreDegree i := by decide +kernel

theorem fullSpoke_core : ∀ (i : Fin 8) (p : Fin (star i).length),
    fullSpoke i ⟨p.val, lt_of_lt_of_le p.isLt (star_specs i).2.1⟩ =
      (spoke i p).natAdd 11 := by decide +kernel

def owner : Fin 11 → Fin 8 × ℕ :=
  ![(7, 3), (2, 2), (2, 3), (2, 4), (3, 5), (1, 2),
    (1, 3), (1, 4), (0, 5), (0, 6), (0, 7)]

/-- Source validation separates each chosen owner from the eight shared
readings. The geometric equalities are proved by the seam law below. -/
theorem ring_position_cases : ∀ (i : Fin 8) (p : Fin (coreDegree i)),
    (star i).length ≤ p.val → ∃ b : Fin 11, fullSpoke i p = b.castAdd 8 ∧
      (owner b = (i, p.val) ∨
       (i = 3 ∧ p.val = 6 ∧ b = 5) ∨
       (i = 6 ∧ p.val = 4 ∧ b = 5) ∨
       (i = 3 ∧ p.val = 4 ∧ b = 3) ∨
       (i = 4 ∧ p.val = 3 ∧ b = 7) ∨
       (i = 4 ∧ p.val = 4 ∧ b = 8) ∨
       (i = 5 ∧ p.val = 4 ∧ b = 1) ∨
       (i = 7 ∧ p.val = 4 ∧ b = 1) ∨
       (i = 7 ∧ p.val = 2 ∧ b = 10)) := by decide +kernel

/-- Every source edge is incident with a core vertex or lies between two
successive entries of a full core star. Ring edges are included. -/
theorem edge_reading : ∀ a b : Fin 19, input.graph.Adj a b →
    ∃ (i : Fin 8) (p : Fin (coreDegree i)),
      (a = i.natAdd 11 ∧ b = fullSpoke i p) ∨
      (b = i.natAdd 11 ∧ a = fullSpoke i p) ∨
      (a = fullSpoke i p ∧ b = fullSpoke i (nextPos i p)) ∨
      (b = fullSpoke i p ∧ a = fullSpoke i (nextPos i p)) := by decide +kernel

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {rotation : Data G}
  (r : JointReading rotation)

def base (i : Fin 8) : G.Dart :=
  ⟨(r.core.map i, r.core.map (firstNeighbor i)), r.core.map.map_adj (first_edge i)⟩

def around (i : Fin 8) (n : ℕ) : G.Dart := (rotation.vertexRotation ^ n) (base r i)

theorem around_fst (i : Fin 8) (n : ℕ) : (around r i n).fst = r.core.map i :=
  FacialStarCompletion.pow_fst rotation (base r i) n

theorem around_step (i : Fin 8) (n : ℕ) :
    rotation.vertexRotation (around r i n) = around r i (n + 1) := by
  simp only [around, pow_succ', Equiv.Perm.mul_apply]

theorem around_core (tri : Triangular rotation) (i : Fin 8) (p : Fin (star i).length) :
    (around r i p.val).snd = r.core.map (spoke i p) := by
  have hd : ∀ n (hn : n < (star i).length), around r i n =
      (⟨(r.core.map i, r.core.map (spoke i ⟨n, hn⟩)),
        r.core.map.map_adj ((star_specs i).2.2 _ |>.mpr ⟨⟨n, hn⟩, rfl⟩)⟩ : G.Dart) := by
    intro n
    induction n with
    | zero => intro hn; simp only [around, pow_zero, Equiv.Perm.one_apply, base, first_spoke]
    | succ n ih =>
      intro hn
      rw [← around_step, ih (by omega)]
      obtain ⟨_, _, eq⟩ := joint_preserves_turns r tri i _ _
        (star_steps i ⟨n, by omega⟩ ⟨n + 1, hn⟩ rfl)
      exact eq
  exact congrArg (fun d : G.Dart => d.snd) (hd p.val p.isLt)

def vertex (v : Fin 19) : V :=
  if h : v.val < 11 then (around r (owner ⟨v.val, h⟩).1 (owner ⟨v.val, h⟩).2).snd
  else r.core.map ⟨v.val - 11, by omega⟩

theorem vertex_core (i : Fin 8) : vertex r (i.natAdd 11) = r.core.map i := by
  simp [vertex, Fin.natAdd]

theorem vertex_ring (p : Fin 11) :
    vertex r (p.castAdd 8) = (around r (owner p).1 (owner p).2).snd := by
  simp [vertex, p.isLt]

variable [Finite V]

theorem around_period (cyclic : rotation.IsVertexwiseCyclic) (i : Fin 8) :
    around r i (coreDegree i) = around r i 0 := by
  have h := FacialStarCompletion.pow_degree rotation cyclic (base r i)
  change (rotation.vertexRotation ^ G.degree (r.core.map i)) (base r i) = base r i at h
  rw [r.core.degree] at h
  exact h

theorem around_previous (cyclic : rotation.IsVertexwiseCyclic) (i : Fin 8) :
    around r i (coreDegree i - 1) = rotation.vertexRotation.symm (base r i) := by
  have h := FacialStarCompletion.pow_pred rotation cyclic (base r i)
  change (rotation.vertexRotation ^ (G.degree (r.core.map i) - 1)) _ = _ at h
  rw [r.core.degree] at h
  exact h

/-- One seam law supplies all eight shared exterior-corner identities. -/
theorem outer_seam (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 8) :
    (around r i (coreDegree i - 1)).snd =
      (around r (firstNeighbor i) (star (firstNeighbor i)).length).snd := by
  let j := firstNeighbor i
  have hn := (star_specs j).1
  have hd : (base r i).symm = around r j ((star j).length - 1) := by
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · exact (around_fst r j _).symm
    · have h := around_core r tri j ⟨(star j).length - 1, by omega⟩
      rw [seam_last] at h
      exact h.symm
  rw [around_previous r cyclic, FacialStarCompletion.across_edge rotation tri, hd,
    around_step, Nat.sub_add_cancel hn]

theorem row_agrees (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic) :
    ∀ (i : Fin 8) (p : Fin (coreDegree i)),
      vertex r (fullSpoke i p) = (around r i p.val).snd := by
  have s0 := outer_seam r tri cyclic 0
  have s1 := outer_seam r tri cyclic 1
  have s2 := outer_seam r tri cyclic 2
  have s3 := outer_seam r tri cyclic 3
  have s4 := outer_seam r tri cyclic 4
  have s5 := outer_seam r tri cyclic 5
  have s6 := outer_seam r tri cyclic 6
  have s7 := outer_seam r tri cyclic 7
  simp only [degree_values, show ∀ i, (star i).length =
      (![5, 2, 2, 4, 3, 4, 4, 2] : Fin 8 → ℕ) i from fun i => congrFun star_lengths i,
    firstNeighbor, Matrix.cons_val_zero, Nat.reduceSub]
    at s0 s1 s2 s3 s4 s5 s6 s7
  intro i p
  by_cases hp : p.val < (star i).length
  · rw [show fullSpoke i p = (spoke i ⟨p.val, hp⟩).natAdd 11 from
      fullSpoke_core i ⟨p.val, hp⟩, vertex_core]
    exact (around_core r tri i ⟨p.val, hp⟩).symm
  obtain ⟨b, hb, cases⟩ := ring_position_cases i p (by omega)
  rw [hb, vertex_ring]
  rcases cases with own | ⟨rfl, hp, rfl⟩ | ⟨rfl, hp, rfl⟩ | ⟨rfl, hp, rfl⟩ |
    ⟨rfl, hp, rfl⟩ | ⟨rfl, hp, rfl⟩ | ⟨rfl, hp, rfl⟩ |
    ⟨rfl, hp, rfl⟩ | ⟨rfl, hp, rfl⟩
  · rw [own]
  · rw [hp]; exact (s3.trans s6).symm
  · rw [hp]; exact s6.symm
  · rw [hp]; exact s2
  · rw [hp]; exact s1
  · rw [hp]; exact s4.symm
  · rw [hp]; exact s5.symm
  · rw [hp]; exact (s7.trans s5).symm
  · rw [hp]; exact s0

theorem around_next (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 8) (p : Fin (coreDegree i)) :
    rotation.vertexRotation (around r i p.val) = around r i (nextPos i p).val := by
  rw [around_step]
  by_cases h : p.val + 1 < coreDegree i
  · simp only [nextPos, Nat.mod_eq_of_lt h]
  · have he : p.val + 1 = coreDegree i := by omega
    simp only [nextPos, he, Nat.mod_self]
    exact around_period r cyclic i

/-- The whole free completion maps to actual ambient vertices and edges. -/
def hom (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic) :
    input.graph →g G where
  toFun := vertex r
  map_rel' := by
    intro a b h
    obtain ⟨i, p, h⟩ := edge_reading a b h
    have center : G.Adj (vertex r (i.natAdd 11)) (vertex r (fullSpoke i p)) := by
      rw [vertex_core, row_agrees r tri cyclic]
      simpa only [around_fst] using (around r i p.val).adj
    have ring : G.Adj (vertex r (fullSpoke i p))
        (vertex r (fullSpoke i (nextPos i p))) := by
      rw [row_agrees r tri cyclic, row_agrees r tri cyclic]
      have h := consecutive_adjacent rotation tri (around r i p.val)
      rwa [around_next r cyclic] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact center
    · exact center.symm
    · exact ring
    · exact ring.symm

end FourColor.ExceptionalBoundaryCompletion
