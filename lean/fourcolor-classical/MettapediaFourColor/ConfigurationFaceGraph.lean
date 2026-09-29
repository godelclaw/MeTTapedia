import MettapediaFourColor.ConfigurationTable
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Exact graph colourings of a configuration hypermap

A face presentation names every face by a graph vertex, supplies a dart in
each face, and identifies exactly the graph edges. These data give an
equivalence of actual colouring witnesses. Their interpretation also retains
arbitrary ordered boundary observations.
-/

namespace FourColor.ConfigurationFaceGraph

/-- The reference colours and the four graph colours are the same finite set. -/
def colorEquiv : Fin 4 ≃ Color where
  toFun := ![Color.c0, Color.c1, Color.c2, Color.c3]
  invFun
    | .c0 => 0
    | .c1 => 1
    | .c2 => 2
    | .c3 => 3
  left_inv := by decide +kernel
  right_inv c := by cases c <;> rfl

variable {D V : Type*} (M : Hypermap D) (G : SimpleGraph V)

/-- The exact adjacency induced by the two faces incident to each edge. -/
def graph (vertex : D → V) (plain : ∀ d, M.edge (M.edge d) = d)
    (separated : ∀ d, vertex d ≠ vertex (M.edge d)) : SimpleGraph V where
  Adj v w := ∃ d, vertex d = v ∧ vertex (M.edge d) = w
  symm := ⟨by
    rintro v w ⟨d, rfl, rfl⟩
    exact ⟨M.edge d, rfl, congrArg vertex (plain d)⟩⟩
  loopless := ⟨by
    rintro v ⟨d, hv, hw⟩
    exact separated d (hv.trans hw.symm)⟩

instance {vertex : D → V} {plain : ∀ d, M.edge (M.edge d) = d}
    {separated : ∀ d, vertex d ≠ vertex (M.edge d)} [Fintype D] [DecidableEq V] :
    DecidableRel (graph M vertex plain separated).Adj := fun v w =>
  inferInstanceAs (Decidable (∃ d, vertex d = v ∧ vertex (M.edge d) = w))

structure Presentation where
  vertex : D → V
  representative : V → D
  vertex_rep : ∀ v, vertex (representative v) = v
  vertex_face : ∀ d, vertex (M.face d) = vertex d
  same_face : ∀ d, M.CFace d (representative (vertex d))
  adjacent : ∀ v w, G.Adj v w ↔ ∃ d, vertex d = v ∧ vertex (M.edge d) = w

namespace Presentation

variable {M G} (P : Presentation M G)

def pull (k : G.Coloring Color) : {k : D → Color // M.Coloring k} :=
  ⟨fun d => k (P.vertex d),
    ⟨fun d => (k.valid ((P.adjacent _ _).mpr ⟨d, rfl, rfl⟩)).symm,
      fun d => congrArg k (P.vertex_face d)⟩⟩

def push (k : {k : D → Color // M.Coloring k}) : G.Coloring Color :=
  .mk (fun v => k.val (P.representative v)) (by
    intro v w hvw
    obtain ⟨d, rfl, rfl⟩ := (P.adjacent v w).mp hvw
    rw [← k.property.cface (P.same_face d),
      ← k.property.cface (P.same_face (M.edge d))]
    exact (k.property.edge d).symm)

/-- Nothing about the colouring witness is lost by naming the face classes. -/
def coloringEquiv : G.Coloring Color ≃ {k : D → Color // M.Coloring k} where
  toFun := P.pull
  invFun := P.push
  left_inv k := by
    ext v
    exact congrArg k (P.vertex_rep v)
  right_inv k := by
    apply Subtype.ext
    funext d
    exact (k.property.cface (P.same_face d)).symm

/-- The graph and hypermap have exactly the same ordered boundary traces. -/
theorem ringTrace_iff (r : List D) (et : List Color) :
    M.RingTrace r et ↔ ∃ k : G.Coloring Color,
      et = trace (r.map fun d => k (P.vertex d)) := by
  constructor
  · rintro ⟨k, hk, htrace⟩
    refine ⟨P.push ⟨k, hk⟩, ?_⟩
    convert htrace using 1
    congr 1
    apply List.map_congr_left
    intro d _
    exact (hk.cface (P.same_face d)).symm
  · rintro ⟨k, htrace⟩
    exact ⟨(P.pull k).val, (P.pull k).property, htrace⟩

/-- The same equivalence preserves any predicate on the boundary colours. -/
theorem boundary_iff {Port : Type*} (ports : Port → D)
    (accepts : (Port → Color) → Prop) :
    (∃ k, M.Coloring k ∧ accepts (k ∘ ports)) ↔
      ∃ k : G.Coloring Color, accepts (fun p => k (P.vertex (ports p))) := by
  constructor
  · rintro ⟨k, hk, h⟩
    refine ⟨P.push ⟨k, hk⟩, ?_⟩
    convert h using 1
    funext p
    exact (hk.cface (P.same_face (ports p))).symm
  · rintro ⟨k, h⟩
    exact ⟨(P.pull k).val, (P.pull k).property, h⟩

end Presentation

variable {M}

/-- The finite cyclic certificate proves that no face class was split. -/
theorem same_face_of_reaches {n : ℕ} {vertex : D → V} {representative : V → D}
    (reaches : ∀ d, ∃ k : Fin n, (M.face ^ k.val) d = representative (vertex d)) :
    ∀ d, M.CFace d (representative (vertex d)) := by
  intro d
  obtain ⟨k, hk⟩ := reaches d
  exact ⟨(k.val : ℤ), by simpa using hk⟩

/-- Read a finite candidate face cycle in the map's actual cyclic order. -/
def faceCycle (M : Hypermap D) (d : D) (n : ℕ) : List D :=
  (List.range n).map fun k => (M.face ^ k) d

/-- Read the neighbours of a graph vertex in the embedded cyclic order. -/
def star (M : Hypermap D) (vertex : D → V) (representative : V → D)
    (degree : V → ℕ) (v : V) : List V :=
  (faceCycle M (representative v) (degree v)).map fun d => vertex (M.edge d)

/-- A cyclic, duplicate-free certificate enumerates the complete face orbit. -/
theorem faceCycle_eq_orbit [Finite D] (d : D) (n : ℕ)
    (cyclic : IsCyclicChain (fun u v => v = M.face u) (faceCycle M d n))
    (nodup : (faceCycle M d n).Nodup) (nonempty : faceCycle M d n ≠ [])
    (head : (faceCycle M d n).headD d = d) :
    faceCycle M d n = orbitList M.face d :=
  eq_orbitList_of_isCyclicChain cyclic nodup nonempty head

/-- Update cyclic neighbour lists by an oriented boundary-triangle insertion.
The third vertex sees `a`, the new vertex, then `b`; the old `a-b` edge is
replaced by the two boundary edges incident to the new vertex. -/
def triangleStar [DecidableEq V] (stars : V → List V) (a b c : V) :
    Option V → List (Option V)
  | none => [some b, some c, some a]
  | some v =>
    if v = a then (stars v).map fun w => if w = b then none else some w
    else if v = b then (stars v).map fun w => if w = a then none else some w
    else if v = c then (stars v).flatMap fun w =>
      if w = a then [some w, none] else [some w]
    else (stars v).map some

/-- Insert the new boundary vertex immediately after `a` in the oriented ring. -/
def triangleBoundary [DecidableEq V] (boundary : List V) (a : V) : List (Option V) :=
  boundary.flatMap fun v => if v = a then [some v, none] else [some v]

end FourColor.ConfigurationFaceGraph
