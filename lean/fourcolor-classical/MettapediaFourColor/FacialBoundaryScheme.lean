import MettapediaFourColor.FacialStarCompletion
import MettapediaFourColor.ExceptionalCoreLocalInjectivity

/-!
# Completing a facial patch from its core intervals

A core records consecutive known neighbours, with compatible closing seams.
A scheme extends those intervals to full source stars and assigns an owner
to each exterior port. The triangular rotation law identifies every second
reading across a seam. One joint boundary map then reconstructs all edges
and complete core rotations.

The number of core vertices, the core graph, degrees and boundary layout are
parameters. Inducedness ensures the reconstructed boundary stays outside the
core; identifications among boundary ports remain permitted.
-/

namespace FourColor.FacialBoundaryScheme

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalCoreOrientation ExceptionalOverlap

/-- An oriented core has a nonempty interval of known neighbours at each
vertex. Its first edge closes against the last edge of the opposite interval. -/
structure Core (n : ℕ) where
  graph : SimpleGraph (Fin n)
  star : Fin n → List (Fin n)
  positive : ∀ i, 0 < (star i).length
  adjacent : ∀ i j, graph.Adj i j ↔ ∃ p : Fin (star i).length, (star i).get p = j
  seam : ∀ i, let j := (star i).get ⟨0, positive i⟩
    (star j).get ⟨(star j).length - 1, by have := positive j; omega⟩ = i

variable {n : ℕ} (c : Core n)

def spoke (i : Fin n) (p : Fin (c.star i).length) : Fin n := (c.star i).get p
def firstNeighbor (i : Fin n) : Fin n := spoke c i ⟨0, c.positive i⟩

theorem first_edge (i : Fin n) : c.graph.Adj i (firstNeighbor c i) :=
  (c.adjacent i _).mpr ⟨⟨0, c.positive i⟩, rfl⟩

theorem first_spoke (i : Fin n) : spoke c i ⟨0, c.positive i⟩ = firstNeighbor c i := rfl

theorem seam_last (i : Fin n) :
    spoke c (firstNeighbor c i)
      ⟨(c.star (firstNeighbor c i)).length - 1, by
        have := c.positive (firstNeighbor c i); omega⟩ = i := c.seam i

structure Scheme (ports : ℕ) where
  graph : SimpleGraph (Fin (ports + n))
  degree : Fin n → ℕ
  proper : ∀ i, (c.star i).length < degree i
  row : Fin n → ℕ → Fin (ports + n)
  owner : Fin ports → Fin n × ℕ
  owner_bounds : ∀ b, (c.star (owner b).1).length ≤ (owner b).2 ∧
    (owner b).2 < degree (owner b).1
  core_prefix : ∀ (i : Fin n) (p : Fin (c.star i).length),
    row i p.val = (spoke c i p).natAdd ports
  ring_cases : ∀ (i : Fin n) (p : Fin (degree i)), (c.star i).length ≤ p.val →
    ∃ b : Fin ports, row i p.val = b.castAdd n ∧
      (owner b = (i, p.val) ∨
        (p.val + 1 = degree i ∧
          owner b = (firstNeighbor c i, (c.star (firstNeighbor c i)).length)))
  edge_reading : ∀ a b, graph.Adj a b → ∃ (i : Fin n) (p : Fin (degree i)),
    (a = i.natAdd ports ∧ b = row i p.val) ∨
    (b = i.natAdd ports ∧ a = row i p.val) ∨
    (a = row i p.val ∧ b = row i ((p.val + 1) % degree i)) ∨
    (b = row i p.val ∧ a = row i ((p.val + 1) % degree i))

variable {ports : ℕ} (s : Scheme c ports)

theorem degree_pos (i : Fin n) : 0 < s.degree i :=
  lt_trans (c.positive i) (s.proper i)

def nextPos (i : Fin n) (p : Fin (s.degree i)) : Fin (s.degree i) :=
  ⟨(p.val + 1) % s.degree i, Nat.mod_lt _ (degree_pos c s i)⟩

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {rotation : Data G}

structure Reading (s : Scheme c ports) (rotation : Data G) where
  map : c.graph →g G
  turns : ∀ (i : Fin n) (p q : Fin (c.star i).length), q.val = p.val + 1 →
    Corner rotation (map i) (map (spoke c i p)) (map (spoke c i q))
  degree_eq : ∀ i, G.degree (map i) = s.degree i

variable {s} (r : Reading c s rotation)

def base (i : Fin n) : G.Dart :=
  ⟨(r.map i, r.map (firstNeighbor c i)), r.map.map_adj (first_edge c i)⟩

def around (i : Fin n) (n : ℕ) : G.Dart := (rotation.vertexRotation ^ n) (base c r i)

theorem around_fst (i : Fin n) (n : ℕ) : (around c r i n).fst = r.map i :=
  FacialStarCompletion.pow_fst rotation (base c r i) n

theorem around_step (i : Fin n) (n : ℕ) :
    rotation.vertexRotation (around c r i n) = around c r i (n + 1) := by
  simp only [around, pow_succ', Equiv.Perm.mul_apply]

theorem around_core (_tri : Triangular rotation) (i : Fin n) (p : Fin (c.star i).length) :
    (around c r i p.val).snd = r.map (spoke c i p) := by
  have hd : ∀ n (hn : n < (c.star i).length), around c r i n =
      (⟨(r.map i, r.map (spoke c i ⟨n, hn⟩)),
        r.map.map_adj ((c.adjacent i) _ |>.mpr ⟨⟨n, hn⟩, rfl⟩)⟩ : G.Dart) := by
    intro n
    induction n with
    | zero => intro hn; simp only [around, pow_zero, Equiv.Perm.one_apply, base, first_spoke]
    | succ n ih =>
      intro hn
      rw [← around_step, ih (by omega)]
      obtain ⟨_, _, eq⟩ := r.turns i
        ⟨n, by omega⟩ ⟨n + 1, hn⟩ rfl
      exact eq
  exact congrArg (fun d : G.Dart => d.snd) (hd p.val p.isLt)

def vertex (v : Fin (ports + n)) : V :=
  if h : v.val < ports then (around c r (s.owner ⟨v.val, h⟩).1 (s.owner ⟨v.val, h⟩).2).snd
  else r.map ⟨v.val - ports, by omega⟩

theorem vertex_core (i : Fin n) : vertex c r (i.natAdd ports) = r.map i := by
  simp [vertex, Fin.natAdd]

theorem vertex_ring (b : Fin ports) :
    vertex c r (b.castAdd n) = (around c r (s.owner b).1 (s.owner b).2).snd := by
  simp [vertex, b.isLt]

variable [Finite V]

theorem around_period (cyclic : rotation.IsVertexwiseCyclic) (i : Fin n) :
    around c r i (s.degree i) = around c r i 0 := by
  have h := FacialStarCompletion.pow_degree rotation cyclic (base c r i)
  change (rotation.vertexRotation ^ G.degree (r.map i)) (base c r i) = base c r i at h
  rw [r.degree_eq] at h
  exact h

theorem around_previous (cyclic : rotation.IsVertexwiseCyclic) (i : Fin n) :
    around c r i (s.degree i - 1) = rotation.vertexRotation.symm (base c r i) := by
  have h := FacialStarCompletion.pow_pred rotation cyclic (base c r i)
  change (rotation.vertexRotation ^ (G.degree (r.map i) - 1)) _ = _ at h
  rw [r.degree_eq] at h
  exact h

theorem outer_seam (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin n) :
    (around c r i (s.degree i - 1)).snd =
      (around c r (firstNeighbor c i) (c.star (firstNeighbor c i)).length).snd := by
  let j := firstNeighbor c i
  have hn := c.positive j
  have hd : (base c r i).symm = around c r j ((c.star j).length - 1) := by
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · exact (around_fst c r j _).symm
    · have h := around_core c r tri j ⟨(c.star j).length - 1, by omega⟩
      rw [seam_last] at h
      exact h.symm
  rw [around_previous c r cyclic, FacialStarCompletion.across_edge rotation tri, hd,
    around_step, Nat.sub_add_cancel hn]

/-- Owner and seam equalities produce a single joint boundary map. -/
theorem row_agrees (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin n) (p : Fin (s.degree i)) :
    vertex c r (s.row i p.val) = (around c r i p.val).snd := by
  by_cases hp : p.val < (c.star i).length
  · rw [s.core_prefix i ⟨p.val, hp⟩, vertex_core]
    exact (around_core c r tri i ⟨p.val, hp⟩).symm
  obtain ⟨b, hb, own | ⟨last, seam⟩⟩ := s.ring_cases i p (by omega)
  · rw [hb, vertex_ring, own]
  · rw [hb, vertex_ring, seam]
    have hp : p.val = s.degree i - 1 := by omega
    rw [hp]
    exact (outer_seam c r tri cyclic i).symm

theorem around_next (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin n) (p : Fin (s.degree i)) :
    rotation.vertexRotation (around c r i p.val) = around c r i (nextPos c s i p).val := by
  rw [around_step]
  by_cases h : p.val + 1 < s.degree i
  · simp only [nextPos, Nat.mod_eq_of_lt h]
  · have he : p.val + 1 = s.degree i := by omega
    simp only [nextPos, he, Nat.mod_self]
    exact around_period c r cyclic i

def hom (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic) : s.graph →g G where
  toFun := vertex c r
  map_rel' := by
    intro a b h
    obtain ⟨i, p, h⟩ := s.edge_reading a b h
    have center : G.Adj (vertex c r (i.natAdd ports)) (vertex c r (s.row i p.val)) := by
      rw [vertex_core, row_agrees c r tri cyclic]
      simpa only [around_fst] using (around c r i p.val).adj
    have ring : G.Adj (vertex c r (s.row i p.val))
        (vertex c r (s.row i ((p.val + 1) % s.degree i))) := by
      change G.Adj (vertex c r (s.row i p.val)) (vertex c r (s.row i (nextPos c s i p).val))
      rw [row_agrees c r tri cyclic, row_agrees c r tri cyclic]
      have h := consecutive_adjacent rotation tri (around c r i p.val)
      rwa [around_next c r cyclic] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact center
    · exact center.symm
    · exact ring
    · exact ring.symm

theorem full_turn (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin n) (p : Fin (s.degree i)) :
    Corner rotation (vertex c r (i.natAdd ports)) (vertex c r (s.row i p.val))
      (vertex c r (s.row i (nextPos c s i p).val)) := by
  have adj (q : Fin (s.degree i)) :
      G.Adj (vertex c r (i.natAdd ports)) (vertex c r (s.row i q.val)) := by
    rw [vertex_core, row_agrees c r tri cyclic]
    simpa only [around_fst] using (around c r i q.val).adj
  have eq (q : Fin (s.degree i)) :
      (⟨(vertex c r (i.natAdd ports), vertex c r (s.row i q.val)), adj q⟩ : G.Dart) =
        around c r i q.val := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext ((vertex_core c r i).trans (around_fst c r i q.val).symm)
      (row_agrees c r tri cyclic i q)
  refine ⟨adj p, adj (nextPos c s i p), ?_⟩
  exact (congrArg rotation.vertexRotation (eq p)).trans
    ((around_next c r cyclic i p).trans (eq (nextPos c s i p)).symm)

theorem around_injective (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin n) : Function.Injective (fun p : Fin (s.degree i) => (around c r i p.val).snd) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  apply ExceptionalCoreLocalInjectivity.corner_chain_injective rotation cyclic
    (r.map i) (degree_pos c s i)
  · intro p
    simpa only [around_fst] using (around c r i p.val).adj
  · intro n hn
    have h := full_turn c r tri cyclic i ⟨n, by omega⟩
    rw [vertex_core, row_agrees c r tri cyclic, row_agrees c r tri cyclic] at h
    simpa only [nextPos, Nat.mod_eq_of_lt hn] using h
  · rw [r.degree_eq]

/-- An owned exterior position cannot identify with an induced core vertex.
Identifications among exterior ports remain permitted. -/
theorem ring_outside_core (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (reflect : ∀ i j, G.Adj (r.map i) (r.map j) → c.graph.Adj i j)
    (p : Fin ports) (j : Fin n) : vertex c r (p.castAdd n) ≠ r.map j := by
  intro eq
  rw [vertex_ring] at eq
  let i := (s.owner p).1
  let n := (s.owner p).2
  obtain ⟨lo, hi⟩ := s.owner_bounds p
  have adj : G.Adj (r.map i) (r.map j) := by
    have h := (around c r i n).adj
    rw [around_fst, eq] at h
    exact h
  obtain ⟨q, hq⟩ := (c.adjacent i) j |>.mp (reflect i j adj)
  change spoke c i q = j at hq
  have he : (around c r i n).snd = (around c r i q.val).snd := by
    rw [around_core c r tri i q, hq]
    exact eq
  have indices : (⟨n, hi⟩ : Fin (s.degree i)) =
      ⟨q.val, lt_trans q.isLt (s.proper i)⟩ :=
    around_injective c r tri cyclic i he
  have hval := congrArg Fin.val indices
  have hqbound := q.isLt
  change n = q.val at hval
  change (c.star i).length ≤ n at lo
  omega

end FourColor.FacialBoundaryScheme
