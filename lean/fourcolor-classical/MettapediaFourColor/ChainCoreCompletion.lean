import MettapediaFourColor.ChainCoreReading
import MettapediaFourColor.FacialStarCompletion

/-!
# Growing the chain boundary from its retained core

Each actual star extends the prescribed core interval. The shared facial
seam law identifies its two readings of each shared exterior corner.
One joint eight-port map preserves all source edges, including ring edges.
-/

namespace FourColor.ChainCoreCompletion

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ChainCoreReading NearLinearChainData
open ExceptionalCoreOrientation ExceptionalOverlap

set_option maxRecDepth 32768

def firstNeighbor : Fin 5 → Fin 5 := ![1, 4, 0, 2, 3]

theorem first_edge : ∀ i, core.Adj i (firstNeighbor i) := by decide +kernel

theorem first_spoke : ∀ i,
    spoke i ⟨0, (star_specs i).1⟩ = firstNeighbor i := by decide +kernel

theorem degree_pos : ∀ i : Fin 5, 0 < degree i := by decide +kernel

theorem seam_last : ∀ i : Fin 5,
    spoke (firstNeighbor i)
      ⟨(star (firstNeighbor i)).length - 1, by
        have := (star_specs (firstNeighbor i)).1; omega⟩ = i := by decide +kernel

def shift : Fin 5 → ℕ := ![1, 1, 1, 1, 2]

def fullRow (i : Fin 5) : List (Fin 13) :=
  ((stars0004 (i.natAdd 8)).reverse).rotate (shift i)

def fullSpoke (i : Fin 5) (p : Fin (degree i)) : Fin 13 := (fullRow i).getD p.val 0

def nextPos (i : Fin 5) (p : Fin (degree i)) : Fin (degree i) :=
  ⟨(p.val + 1) % degree i, Nat.mod_lt _ (degree_pos i)⟩

theorem fullRow_length : ∀ i, (fullRow i).length = degree i := by decide +kernel

theorem fullSpoke_core : ∀ (i : Fin 5) (p : Fin (star i).length),
    fullSpoke i ⟨p.val, lt_trans p.isLt (star_specs i).2.1⟩ =
      (spoke i p).natAdd 8 := by decide +kernel

def owner : Fin 8 → Fin 5 × ℕ :=
  ![(4, 3), (4, 2), (1, 4), (0, 3), (0, 2), (2, 3), (3, 4), (3, 3)]

theorem ring_position_cases : ∀ (i : Fin 5) (p : Fin (degree i)),
    (star i).length ≤ p.val → ∃ b : Fin 8, fullSpoke i p = b.castAdd 5 ∧
      (owner b = (i, p.val) ∨
       (i = 0 ∧ p.val = 4 ∧ b = 2) ∨
       (i = 1 ∧ p.val = 5 ∧ b = 1) ∨
       (i = 2 ∧ p.val = 4 ∧ b = 4) ∨
       (i = 3 ∧ p.val = 5 ∧ b = 5) ∨
       (i = 4 ∧ p.val = 4 ∧ b = 7)) := by decide +kernel

/-- Every source edge is at a core vertex or joins successive spokes. -/
theorem edge_reading : ∀ a b : Fin 13, input0004.graph.Adj a b →
    ∃ (i : Fin 5) (p : Fin (degree i)),
      (a = i.natAdd 8 ∧ b = fullSpoke i p) ∨
      (b = i.natAdd 8 ∧ a = fullSpoke i p) ∨
      (a = fullSpoke i p ∧ b = fullSpoke i (nextPos i p)) ∨
      (b = fullSpoke i p ∧ a = fullSpoke i (nextPos i p)) := by decide +kernel

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {rotation : Data G}
  (r : Reading rotation)

def base (i : Fin 5) : G.Dart :=
  ⟨(r.map i, r.map (firstNeighbor i)), r.map.map_adj (first_edge i)⟩

def around (i : Fin 5) (n : ℕ) : G.Dart := (rotation.vertexRotation ^ n) (base r i)

theorem around_fst (i : Fin 5) (n : ℕ) : (around r i n).fst = r.map i :=
  FacialStarCompletion.pow_fst rotation (base r i) n

theorem around_step (i : Fin 5) (n : ℕ) :
    rotation.vertexRotation (around r i n) = around r i (n + 1) := by
  simp only [around, pow_succ', Equiv.Perm.mul_apply]

theorem around_core (tri : Triangular rotation) (i : Fin 5) (p : Fin (star i).length) :
    (around r i p.val).snd = r.map (spoke i p) := by
  have hd : ∀ n (hn : n < (star i).length), around r i n =
      (⟨(r.map i, r.map (spoke i ⟨n, hn⟩)),
        r.map.map_adj ((star_specs i).2.2 _ |>.mpr ⟨⟨n, hn⟩, rfl⟩)⟩ : G.Dart) := by
    intro n
    induction n with
    | zero => intro hn; simp only [around, pow_zero, Equiv.Perm.one_apply, base, first_spoke]
    | succ n ih =>
      intro hn
      rw [← around_step, ih (by omega)]
      obtain ⟨_, _, eq⟩ := turns r tri i ⟨n, by omega⟩ ⟨n + 1, hn⟩ rfl
      exact eq
  exact congrArg (fun d : G.Dart => d.snd) (hd p.val p.isLt)

def vertex (v : Fin 13) : V :=
  if h : v.val < 8 then (around r (owner ⟨v.val, h⟩).1 (owner ⟨v.val, h⟩).2).snd
  else r.map ⟨v.val - 8, by omega⟩

theorem vertex_core (i : Fin 5) : vertex r (i.natAdd 8) = r.map i := by
  simp [vertex, Fin.natAdd]

theorem vertex_ring (p : Fin 8) :
    vertex r (p.castAdd 5) = (around r (owner p).1 (owner p).2).snd := by
  simp [vertex, p.isLt]

/-- The common centre retains every core observation within one edge. -/
theorem core_near (i : Fin 5) :
    r.map i ∈ LocalCoverageAssembly.closedBall G (r.map 1) 1 := by
  by_cases hi : i = 1
  · subst i
    exact LocalCoverageAssembly.centre_mem G _ _
  · let p : G.Walk (r.map 1) (r.map i) :=
      .cons (r.map.map_adj (ChainCoreReading.center_adj i hi)) .nil
    simpa [LocalCoverageAssembly.closedBall, p] using p.edist_le

/-- The complete joint boundary, including possible identifications, lies
within radius two of the same retained centre. -/
theorem vertex_near (v : Fin 13) :
    vertex r v ∈ LocalCoverageAssembly.closedBall G (r.map 1) 2 := by
  by_cases hv : v.val < 8
  · let q : Fin 8 := ⟨v.val, hv⟩
    have ve : v = q.castAdd 5 := by apply Fin.ext; rfl
    rw [ve, vertex_ring]
    apply LocalCoverageAssembly.ball_recenter G (b := 1) (core_near r (owner q).1)
    let p : G.Walk (r.map (owner q).1) (around r (owner q).1 (owner q).2).snd :=
      .cons (by simpa only [around_fst] using (around r (owner q).1 (owner q).2).adj) .nil
    simpa [LocalCoverageAssembly.closedBall, p] using p.edist_le
  · let i : Fin 5 := ⟨v.val - 8, by omega⟩
    have ve : v = i.natAdd 8 := by apply Fin.ext; dsimp [i]; omega
    rw [ve, vertex_core]
    exact LocalCoverageAssembly.ball_mono G (by decide : 1 ≤ 2) (core_near r i)

variable [Finite V]

theorem around_period (cyclic : rotation.IsVertexwiseCyclic) (i : Fin 5) :
    around r i (degree i) = around r i 0 := by
  have h := FacialStarCompletion.pow_degree rotation cyclic (base r i)
  change (rotation.vertexRotation ^ G.degree (r.map i)) (base r i) = base r i at h
  rw [r.degree_eq] at h
  exact h

theorem around_previous (cyclic : rotation.IsVertexwiseCyclic) (i : Fin 5) :
    around r i (degree i - 1) = rotation.vertexRotation.symm (base r i) := by
  have h := FacialStarCompletion.pow_pred rotation cyclic (base r i)
  change (rotation.vertexRotation ^ (G.degree (r.map i) - 1)) _ = _ at h
  rw [r.degree_eq] at h
  exact h

/-- One seam law supplies all five shared exterior-corner identities. -/
theorem outer_seam (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 5) :
    (around r i (degree i - 1)).snd =
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
    ∀ (i : Fin 5) (p : Fin (degree i)),
      vertex r (fullSpoke i p) = (around r i p.val).snd := by
  have s0 := outer_seam r tri cyclic 0
  have s1 := outer_seam r tri cyclic 1
  have s2 := outer_seam r tri cyclic 2
  have s3 := outer_seam r tri cyclic 3
  have s4 := outer_seam r tri cyclic 4
  change (around r 0 4).snd = (around r 1 4).snd at s0
  change (around r 1 5).snd = (around r 4 2).snd at s1
  change (around r 2 4).snd = (around r 0 2).snd at s2
  change (around r 3 5).snd = (around r 2 3).snd at s3
  change (around r 4 4).snd = (around r 3 3).snd at s4
  intro i p
  by_cases hp : p.val < (star i).length
  · rw [show fullSpoke i p = (spoke i ⟨p.val, hp⟩).natAdd 8 from
      fullSpoke_core i ⟨p.val, hp⟩, vertex_core]
    exact (around_core r tri i ⟨p.val, hp⟩).symm
  obtain ⟨b, hb, cases⟩ := ring_position_cases i p (by omega)
  rw [hb, vertex_ring]
  rcases cases with own | ⟨rfl, hp, rfl⟩ | ⟨rfl, hp, rfl⟩ | ⟨rfl, hp, rfl⟩ |
    ⟨rfl, hp, rfl⟩ | ⟨rfl, hp, rfl⟩
  · rw [own]
  · rw [hp]; exact s0.symm
  · rw [hp]; exact s1.symm
  · rw [hp]; exact s2.symm
  · rw [hp]; exact s3.symm
  · rw [hp]; exact s4.symm

theorem around_next (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 5) (p : Fin (degree i)) :
    rotation.vertexRotation (around r i p.val) = around r i (nextPos i p).val := by
  rw [around_step]
  by_cases h : p.val + 1 < degree i
  · simp only [nextPos, Nat.mod_eq_of_lt h]
  · have he : p.val + 1 = degree i := by omega
    simp only [nextPos, he, Nat.mod_self]
    exact around_period r cyclic i

/-- The whole free completion maps to actual ambient vertices and edges. -/
def hom (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic) :
    input0004.graph →g G where
  toFun := vertex r
  map_rel' := by
    intro a b h
    obtain ⟨i, p, h⟩ := edge_reading a b h
    have center : G.Adj (vertex r (i.natAdd 8)) (vertex r (fullSpoke i p)) := by
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

end FourColor.ChainCoreCompletion
