import MettapediaFourColor.ThreeTriangleFan
import MettapediaFourColor.FacialStarCompletion

/-!
# Completing the joint boundary of a facial fan

A scheme specifies full source stars extending the common three-triangle
core. Each boundary port has one owner. A second reading of that port is
allowed precisely at the shared exterior corner of an edge. The triangular
rotation law identifies those readings, so all source edges reconstruct in
one ambient graph. Degrees and the number of ports are parameters.
-/

namespace FourColor.FanBoundaryScheme

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ThreeTriangleFan ExceptionalCoreOrientation ExceptionalOverlap

def firstNeighbor : Fin 5 → Fin 5 := ![1, 4, 0, 2, 3]

theorem first_edge : ∀ i, core.Adj i (firstNeighbor i) := by decide +kernel

theorem first_spoke : ∀ i,
    spoke i ⟨0, (star_specs i).1⟩ = firstNeighbor i := by decide +kernel

theorem seam_last : ∀ i : Fin 5,
    spoke (firstNeighbor i)
      ⟨(star (firstNeighbor i)).length - 1, by
        have := (star_specs (firstNeighbor i)).1; omega⟩ = i := by decide +kernel

structure Scheme (ports : ℕ) where
  graph : SimpleGraph (Fin (ports + 5))
  degree : Fin 5 → ℕ
  proper : ∀ i, (star i).length < degree i
  row : Fin 5 → ℕ → Fin (ports + 5)
  owner : Fin ports → Fin 5 × ℕ
  owner_bounds : ∀ b, (star (owner b).1).length ≤ (owner b).2 ∧
    (owner b).2 < degree (owner b).1
  core_prefix : ∀ (i : Fin 5) (p : Fin (star i).length),
    row i p.val = (spoke i p).natAdd ports
  ring_cases : ∀ (i : Fin 5) (p : Fin (degree i)), (star i).length ≤ p.val →
    ∃ b : Fin ports, row i p.val = b.castAdd 5 ∧
      (owner b = (i, p.val) ∨
        (p.val + 1 = degree i ∧
          owner b = (firstNeighbor i, (star (firstNeighbor i)).length)))
  edge_reading : ∀ a b, graph.Adj a b → ∃ (i : Fin 5) (p : Fin (degree i)),
    (a = i.natAdd ports ∧ b = row i p.val) ∨
    (b = i.natAdd ports ∧ a = row i p.val) ∨
    (a = row i p.val ∧ b = row i ((p.val + 1) % degree i)) ∨
    (b = row i p.val ∧ a = row i ((p.val + 1) % degree i))

variable {ports : ℕ} (s : Scheme ports)

theorem degree_pos (i : Fin 5) : 0 < s.degree i :=
  lt_trans (star_specs i).1 (s.proper i)

def nextPos (i : Fin 5) (p : Fin (s.degree i)) : Fin (s.degree i) :=
  ⟨(p.val + 1) % s.degree i, Nat.mod_lt _ (degree_pos s i)⟩

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {rotation : Data G}

structure Reading (s : Scheme ports) (rotation : Data G)
    extends ThreeTriangleFan.Reading rotation where
  degree_eq : ∀ i, G.degree (map i) = s.degree i

variable {s} (r : Reading s rotation)

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
        r.map.map_adj ((star_specs i).2 _ |>.mpr ⟨⟨n, hn⟩, rfl⟩)⟩ : G.Dart) := by
    intro n
    induction n with
    | zero => intro hn; simp only [around, pow_zero, Equiv.Perm.one_apply, base, first_spoke]
    | succ n ih =>
      intro hn
      rw [← around_step, ih (by omega)]
      obtain ⟨_, _, eq⟩ := ThreeTriangleFan.turns r.toReading tri i
        ⟨n, by omega⟩ ⟨n + 1, hn⟩ rfl
      exact eq
  exact congrArg (fun d : G.Dart => d.snd) (hd p.val p.isLt)

def vertex (v : Fin (ports + 5)) : V :=
  if h : v.val < ports then (around r (s.owner ⟨v.val, h⟩).1 (s.owner ⟨v.val, h⟩).2).snd
  else r.map ⟨v.val - ports, by omega⟩

theorem vertex_core (i : Fin 5) : vertex r (i.natAdd ports) = r.map i := by
  simp [vertex, Fin.natAdd]

theorem vertex_ring (b : Fin ports) :
    vertex r (b.castAdd 5) = (around r (s.owner b).1 (s.owner b).2).snd := by
  simp [vertex, b.isLt]

theorem core_near (i : Fin 5) :
    r.map i ∈ LocalCoverageAssembly.closedBall G (r.map 1) 1 := by
  by_cases hi : i = 1
  · subst i
    exact LocalCoverageAssembly.centre_mem G _ _
  · let p : G.Walk (r.map 1) (r.map i) :=
      .cons (r.map.map_adj (center_adj i hi)) .nil
    simpa [LocalCoverageAssembly.closedBall, p] using p.edist_le

theorem vertex_near (v : Fin (ports + 5)) :
    vertex r v ∈ LocalCoverageAssembly.closedBall G (r.map 1) 2 := by
  by_cases hv : v.val < ports
  · let q : Fin ports := ⟨v.val, hv⟩
    have ve : v = q.castAdd 5 := by apply Fin.ext; rfl
    rw [ve, vertex_ring]
    apply LocalCoverageAssembly.ball_recenter G (b := 1) (core_near r (s.owner q).1)
    let p : G.Walk (r.map (s.owner q).1) (around r (s.owner q).1 (s.owner q).2).snd :=
      .cons (by simpa only [around_fst] using (around r (s.owner q).1 (s.owner q).2).adj) .nil
    simpa [LocalCoverageAssembly.closedBall, p] using p.edist_le
  · let i : Fin 5 := ⟨v.val - ports, by omega⟩
    have ve : v = i.natAdd ports := by apply Fin.ext; dsimp [i]; omega
    rw [ve, vertex_core]
    exact LocalCoverageAssembly.ball_mono G (by decide : 1 ≤ 2) (core_near r i)

variable [Finite V]

theorem around_period (cyclic : rotation.IsVertexwiseCyclic) (i : Fin 5) :
    around r i (s.degree i) = around r i 0 := by
  have h := FacialStarCompletion.pow_degree rotation cyclic (base r i)
  change (rotation.vertexRotation ^ G.degree (r.map i)) (base r i) = base r i at h
  rw [r.degree_eq] at h
  exact h

theorem around_previous (cyclic : rotation.IsVertexwiseCyclic) (i : Fin 5) :
    around r i (s.degree i - 1) = rotation.vertexRotation.symm (base r i) := by
  have h := FacialStarCompletion.pow_pred rotation cyclic (base r i)
  change (rotation.vertexRotation ^ (G.degree (r.map i) - 1)) _ = _ at h
  rw [r.degree_eq] at h
  exact h

theorem outer_seam (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 5) :
    (around r i (s.degree i - 1)).snd =
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

/-- Owner and seam equalities produce a single joint boundary map. -/
theorem row_agrees (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 5) (p : Fin (s.degree i)) :
    vertex r (s.row i p.val) = (around r i p.val).snd := by
  by_cases hp : p.val < (star i).length
  · rw [s.core_prefix i ⟨p.val, hp⟩, vertex_core]
    exact (around_core r tri i ⟨p.val, hp⟩).symm
  obtain ⟨b, hb, own | ⟨last, seam⟩⟩ := s.ring_cases i p (by omega)
  · rw [hb, vertex_ring, own]
  · rw [hb, vertex_ring, seam]
    have hp : p.val = s.degree i - 1 := by omega
    rw [hp]
    exact (outer_seam r tri cyclic i).symm

theorem around_next (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 5) (p : Fin (s.degree i)) :
    rotation.vertexRotation (around r i p.val) = around r i (nextPos s i p).val := by
  rw [around_step]
  by_cases h : p.val + 1 < s.degree i
  · simp only [nextPos, Nat.mod_eq_of_lt h]
  · have he : p.val + 1 = s.degree i := by omega
    simp only [nextPos, he, Nat.mod_self]
    exact around_period r cyclic i

def hom (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic) : s.graph →g G where
  toFun := vertex r
  map_rel' := by
    intro a b h
    obtain ⟨i, p, h⟩ := s.edge_reading a b h
    have center : G.Adj (vertex r (i.natAdd ports)) (vertex r (s.row i p.val)) := by
      rw [vertex_core, row_agrees r tri cyclic]
      simpa only [around_fst] using (around r i p.val).adj
    have ring : G.Adj (vertex r (s.row i p.val))
        (vertex r (s.row i ((p.val + 1) % s.degree i))) := by
      change G.Adj (vertex r (s.row i p.val)) (vertex r (s.row i (nextPos s i p).val))
      rw [row_agrees r tri cyclic, row_agrees r tri cyclic]
      have h := consecutive_adjacent rotation tri (around r i p.val)
      rwa [around_next r cyclic] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact center
    · exact center.symm
    · exact ring
    · exact ring.symm

theorem full_turn (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 5) (p : Fin (s.degree i)) :
    Corner rotation (vertex r (i.natAdd ports)) (vertex r (s.row i p.val))
      (vertex r (s.row i (nextPos s i p).val)) := by
  have adj (q : Fin (s.degree i)) :
      G.Adj (vertex r (i.natAdd ports)) (vertex r (s.row i q.val)) := by
    rw [vertex_core, row_agrees r tri cyclic]
    simpa only [around_fst] using (around r i q.val).adj
  have eq (q : Fin (s.degree i)) :
      (⟨(vertex r (i.natAdd ports), vertex r (s.row i q.val)), adj q⟩ : G.Dart) =
        around r i q.val := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext ((vertex_core r i).trans (around_fst r i q.val).symm)
      (row_agrees r tri cyclic i q)
  refine ⟨adj p, adj (nextPos s i p), ?_⟩
  exact (congrArg rotation.vertexRotation (eq p)).trans
    ((around_next r cyclic i p).trans (eq (nextPos s i p)).symm)

theorem around_injective (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 5) : Function.Injective (fun p : Fin (s.degree i) => (around r i p.val).snd) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  apply ExceptionalCoreLocalInjectivity.corner_chain_injective rotation cyclic
    (r.map i) (degree_pos s i)
  · intro p
    simpa only [around_fst] using (around r i p.val).adj
  · intro n hn
    have h := full_turn r tri cyclic i ⟨n, by omega⟩
    rw [vertex_core, row_agrees r tri cyclic, row_agrees r tri cyclic] at h
    simpa only [nextPos, Nat.mod_eq_of_lt hn] using h
  · rw [r.degree_eq]

/-- An owned exterior position cannot identify with an induced core vertex.
Identifications among exterior ports remain permitted. -/
theorem ring_outside_core (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (reflect : ∀ i j, G.Adj (r.map i) (r.map j) → core.Adj i j)
    (p : Fin ports) (j : Fin 5) : vertex r (p.castAdd 5) ≠ r.map j := by
  intro eq
  rw [vertex_ring] at eq
  let i := (s.owner p).1
  let n := (s.owner p).2
  obtain ⟨lo, hi⟩ := s.owner_bounds p
  have adj : G.Adj (r.map i) (r.map j) := by
    have h := (around r i n).adj
    rw [around_fst, eq] at h
    exact h
  obtain ⟨q, hq⟩ := (star_specs i).2 j |>.mp (reflect i j adj)
  have he : (around r i n).snd = (around r i q.val).snd := by
    rw [around_core r tri i q, hq]
    exact eq
  have indices : (⟨n, hi⟩ : Fin (s.degree i)) =
      ⟨q.val, lt_trans q.isLt (s.proper i)⟩ :=
    around_injective r tri cyclic i he
  have hval := congrArg Fin.val indices
  have hqbound := q.isLt
  change n = q.val at hval
  change (star i).length ≤ n at lo
  omega

end FourColor.FanBoundaryScheme
