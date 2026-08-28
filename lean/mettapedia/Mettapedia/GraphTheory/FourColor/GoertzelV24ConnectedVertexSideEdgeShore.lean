import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedEdgeShoreMajority

/-!
# Edge shores from connected vertex sides

A literal separator first produces connected vertex sides, whereas the
finite-state descent is indexed by a partition of the ambient edge set.  This
file gives the canonical monotone conversion used by corridor prefixes: put
every edge meeting the chosen vertex side into its edge shore.  The
complementary edge shore then consists exactly of the edges internal to the
opposite vertex side.

No planarity or colouring hypothesis is used.  The proof constructs the
required shore walks explicitly from a walk in the relevant induced graph.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ConnectedVertexSideEdgeShore

open SimpleGraph
open GoertzelV24ConnectedEdgeShoreMajority

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Every edge with at least one endpoint on `side`.  Assigning boundary
edges to `side` in this way is monotone in the vertex predicate. -/
def incidentEdgeShore (G : SimpleGraph V) [Fintype G.edgeSet]
    (side : V → Prop) : Finset G.edgeSet := by
  classical
  exact Finset.univ.filter fun edge => ∃ vertex, vertex ∈ (edge : Sym2 V) ∧ side vertex

@[simp]
theorem mem_incidentEdgeShore_iff
    (side : V → Prop) (edge : G.edgeSet) :
    edge ∈ incidentEdgeShore G side ↔
      ∃ vertex, vertex ∈ (edge : Sym2 V) ∧ side vertex := by
  simp [incidentEdgeShore]

/-- Enlarging the vertex side enlarges its incident-edge shore. -/
theorem incidentEdgeShore_mono {first second : V → Prop}
    (hsubset : ∀ vertex, first vertex → second vertex) :
    incidentEdgeShore G first ⊆ incidentEdgeShore G second := by
  intro edge hedge
  rcases (mem_incidentEdgeShore_iff first edge).1 hedge with
    ⟨vertex, hvertexEdge, hvertex⟩
  exact (mem_incidentEdgeShore_iff second edge).2
    ⟨vertex, hvertexEdge, hsubset vertex hvertex⟩

/-- If two vertices lie on one graph edge, then they coincide or are
adjacent. -/
private theorem eq_or_adj_of_mem_edge
    (edge : G.edgeSet) {left right : V}
    (hleft : left ∈ (edge : Sym2 V))
    (hright : right ∈ (edge : Sym2 V)) :
    left = right ∨ G.Adj left right := by
  by_cases heq : left = right
  · exact Or.inl heq
  · right
    have hedgeValue : (edge : Sym2 V) = s(left, right) :=
      sym2_eq_mk_of_mem_of_mem_of_ne hleft hright heq
    exact (SimpleGraph.mem_edgeSet G).1 (by
      simpa [hedgeValue] using edge.property)

/-- Every edge of a walk supported on `side` belongs to the incident-edge
shore of `side`. -/
private theorem walk_edge_mem_incidentEdgeShore
    (side : V → Prop) {left right : V} (walk : G.Walk left right)
    (hsupport : ∀ vertex, vertex ∈ walk.support → side vertex)
    (edge : G.edgeSet) (hedge : (edge : Sym2 V) ∈ walk.edges) :
    edge ∈ incidentEdgeShore G side := by
  rcases Sym2.mk_surjective (edge : Sym2 V) with ⟨⟨first, second⟩, hvalue⟩
  have hvalue' : s(first, second) = (edge : Sym2 V) := by
    simpa using hvalue
  have hedge' : s(first, second) ∈ walk.edges := by
    rw [hvalue']
    exact hedge
  have hfirstSupport := walk.fst_mem_support_of_mem_edges hedge'
  apply (mem_incidentEdgeShore_iff side edge).2
  refine ⟨first, ?_, hsupport first hfirstSupport⟩
  rw [← hvalue']
  simp

/-- A connected induced vertex side yields a connected incident-edge shore.
Vertices just outside the side that support a boundary edge are joined to the
connected core by that edge. -/
theorem edgeShoreConnected_incidentEdgeShore
    (side : V → Prop)
    (hconnected : (G.induce side).Connected) :
    EdgeShoreConnected G (incidentEdgeShore G side) := by
  intro left right hleftIncident hrightIncident
  rcases hleftIncident with ⟨leftEdge, hleftShore, hleftEdge⟩
  rcases hrightIncident with ⟨rightEdge, hrightShore, hrightEdge⟩
  rcases (mem_incidentEdgeShore_iff side leftEdge).1 hleftShore with
    ⟨leftCore, hleftCoreEdge, hleftCore⟩
  rcases (mem_incidentEdgeShore_iff side rightEdge).1 hrightShore with
    ⟨rightCore, hrightCoreEdge, hrightCore⟩
  rcases hconnected ⟨leftCore, hleftCore⟩ ⟨rightCore, hrightCore⟩ with
    ⟨coreWalk⟩
  let inclusion : G.induce side →g G :=
    { toFun := Subtype.val
      map_rel' := fun {_ _} hadj => hadj }
  let ambientCoreWalk : G.Walk leftCore rightCore := coreWalk.map inclusion
  have hambientCoreSupport : ∀ vertex,
      vertex ∈ ambientCoreWalk.support → side vertex := by
    intro vertex hvertex
    simp only [ambientCoreWalk, SimpleGraph.Walk.support_map] at hvertex
    rcases List.mem_map.mp hvertex with ⟨sourceVertex, _hsource, hvalue⟩
    simpa [inclusion] using hvalue ▸ sourceVertex.2
  have hleftEqOrAdj :=
    eq_or_adj_of_mem_edge leftEdge hleftEdge hleftCoreEdge
  have hrightEqOrAdj :=
    eq_or_adj_of_mem_edge rightEdge hrightCoreEdge hrightEdge
  rcases hleftEqOrAdj with hleftEq | hleftAdj
  · subst leftCore
    rcases hrightEqOrAdj with hrightEq | hrightAdj
    · subst right
      refine ⟨ambientCoreWalk, ?_⟩
      intro edge hedge
      exact walk_edge_mem_incidentEdgeShore
        side ambientCoreWalk hambientCoreSupport edge hedge
    · let rightWalk : G.Walk rightCore right :=
        SimpleGraph.Walk.cons hrightAdj SimpleGraph.Walk.nil
      let joined := ambientCoreWalk.append rightWalk
      refine ⟨joined, ?_⟩
      intro edge hedge
      simp only [joined, SimpleGraph.Walk.edges_append, List.mem_append] at hedge
      rcases hedge with hcore | hright
      · exact walk_edge_mem_incidentEdgeShore
          side ambientCoreWalk hambientCoreSupport edge hcore
      · apply (mem_incidentEdgeShore_iff side edge).2
        refine ⟨rightCore, ?_, hrightCore⟩
        have hedgeValue : (edge : Sym2 V) = s(rightCore, right) := by
          simpa [rightWalk] using hright
        rw [hedgeValue]
        simp
  · rcases hrightEqOrAdj with hrightEq | hrightAdj
    · subst right
      let leftWalk : G.Walk left leftCore :=
        SimpleGraph.Walk.cons hleftAdj SimpleGraph.Walk.nil
      let joined := leftWalk.append ambientCoreWalk
      refine ⟨joined, ?_⟩
      intro edge hedge
      simp only [joined, SimpleGraph.Walk.edges_append, List.mem_append] at hedge
      rcases hedge with hleft | hcore
      · apply (mem_incidentEdgeShore_iff side edge).2
        refine ⟨leftCore, ?_, hleftCore⟩
        have hedgeValue : (edge : Sym2 V) = s(left, leftCore) := by
          simpa [leftWalk] using hleft
        rw [hedgeValue]
        simp
      · exact walk_edge_mem_incidentEdgeShore
          side ambientCoreWalk hambientCoreSupport edge hcore
    · let leftWalk : G.Walk left leftCore :=
        SimpleGraph.Walk.cons hleftAdj SimpleGraph.Walk.nil
      let rightWalk : G.Walk rightCore right :=
        SimpleGraph.Walk.cons hrightAdj SimpleGraph.Walk.nil
      let joined := leftWalk.append (ambientCoreWalk.append rightWalk)
      refine ⟨joined, ?_⟩
      intro edge hedge
      simp only [joined, SimpleGraph.Walk.edges_append, List.mem_append] at hedge
      rcases hedge with hleft | hcore | hright
      · apply (mem_incidentEdgeShore_iff side edge).2
        refine ⟨leftCore, ?_, hleftCore⟩
        have hedgeValue : (edge : Sym2 V) = s(left, leftCore) := by
          simpa [leftWalk] using hleft
        rw [hedgeValue]
        simp
      · exact walk_edge_mem_incidentEdgeShore
          side ambientCoreWalk hambientCoreSupport edge hcore
      · apply (mem_incidentEdgeShore_iff side edge).2
        refine ⟨rightCore, ?_, hrightCore⟩
        have hedgeValue : (edge : Sym2 V) = s(rightCore, right) := by
          simpa [rightWalk] using hright
        rw [hedgeValue]
        simp

/-- An edge is outside the incident shore precisely when neither endpoint is
on the chosen side. -/
theorem mem_complement_incidentEdgeShore_iff
    (side : V → Prop) (edge : G.edgeSet) :
    edge ∈ Finset.univ \ incidentEdgeShore G side ↔
      ∀ vertex, vertex ∈ (edge : Sym2 V) → ¬ side vertex := by
  rw [Finset.mem_sdiff]
  simp only [Finset.mem_univ, true_and, mem_incidentEdgeShore_iff]
  push Not
  rfl

/-- If the complementary induced vertex side is connected, then the
complement of the incident-edge shore is connected.  Every edge in this
complement has both endpoints on the complementary side. -/
theorem edgeShoreConnected_complement_incidentEdgeShore
    (side : V → Prop)
    (hconnected : (G.induce (fun vertex => ¬ side vertex)).Connected) :
    EdgeShoreConnected G (Finset.univ \ incidentEdgeShore G side) := by
  intro left right hleftIncident hrightIncident
  rcases hleftIncident with ⟨leftEdge, hleftShore, hleftEdge⟩
  rcases hrightIncident with ⟨rightEdge, hrightShore, hrightEdge⟩
  have hleft : ¬ side left :=
    (mem_complement_incidentEdgeShore_iff side leftEdge).1
      hleftShore left hleftEdge
  have hright : ¬ side right :=
    (mem_complement_incidentEdgeShore_iff side rightEdge).1
      hrightShore right hrightEdge
  rcases hconnected ⟨left, hleft⟩ ⟨right, hright⟩ with ⟨insideWalk⟩
  let inclusion : G.induce (fun vertex => ¬ side vertex) →g G :=
    { toFun := Subtype.val
      map_rel' := fun {_ _} hadj => hadj }
  let walk : G.Walk left right := insideWalk.map inclusion
  refine ⟨walk, ?_⟩
  intro edge hedge
  apply (mem_complement_incidentEdgeShore_iff side edge).2
  intro vertex hvertexEdge hvertexSide
  have hvertexSupport : vertex ∈ walk.support :=
    walk.mem_support_of_mem_edges hedge hvertexEdge
  simp only [walk, SimpleGraph.Walk.support_map] at hvertexSupport
  rcases List.mem_map.mp hvertexSupport with
    ⟨sourceVertex, _hsource, hvalue⟩
  have hvalue' : sourceVertex.1 = vertex := by
    simpa [inclusion] using hvalue
  rw [← hvalue'] at hvertexSide
  exact sourceVertex.2 hvertexSide

/-- A connected vertex bipartition canonically supplies the two connected
edge shores consumed by the majority-shore splice. -/
theorem connected_edgeShores_of_connected_vertexSides
    (side : V → Prop)
    (hside : (G.induce side).Connected)
    (hcomplement : (G.induce (fun vertex => ¬ side vertex)).Connected) :
    EdgeShoreConnected G (incidentEdgeShore G side) ∧
      EdgeShoreConnected G (Finset.univ \ incidentEdgeShore G side) :=
  ⟨edgeShoreConnected_incidentEdgeShore side hside,
    edgeShoreConnected_complement_incidentEdgeShore side hcomplement⟩

end

end GoertzelV24ConnectedVertexSideEdgeShore

end Mettapedia.GraphTheory.FourColor
