import Mettapedia.GraphTheory.FourColor.CyclicEdgeCut
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Component boundaries as exact Goertzel cyclic cuts

This is the graph-facing half of the primal-separator interface.  A finite
edge deletion has a canonical vertex side for each connected component of the
deleted graph; its boundary is computed from endpoints, not guessed from a
picture.  The annulus/Jordan layer still has to identify the relevant deleted
support and prove the two cycle witnesses, but once those facts are available
the exact `CyclicEdgeCutRealization` is mechanical.

The construction is deliberately independent of the classical unavoidable-set
route.  It is useful for the closed-web chord layer because it separates the
generic component argument from the remaining wall/sector geometry.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FiniteDeletionCyclicCut

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-! The value-level deletion support corresponding to a finite set of graph
edges.  `deleteEdges` consumes unordered vertex pairs, whereas the proof
interfaces consume graph-edge subtypes. -/

def edgeFinsetValueSet (removed : Finset G.edgeSet) : Set (Sym2 V) :=
  Subtype.val '' (removed : Set G.edgeSet)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem mem_edgeFinsetValueSet_iff
    (removed : Finset G.edgeSet) (edge : Sym2 V) :
    edge ∈ edgeFinsetValueSet removed ↔
      ∃ graphEdge ∈ removed, graphEdge.1 = edge := by
  simp [edgeFinsetValueSet]

/-! The exact boundary of one deletion component. -/

def componentCrossingEdges
    (removed : Finset G.edgeSet)
    (component :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent) :
    Finset G.edgeSet := by
  classical
  exact Finset.univ.filter fun edge =>
    EdgeCrossesVertexSide G (fun vertex => vertex ∈ component.supp) edge

omit [DecidableEq V] in
@[simp]
theorem mem_componentCrossingEdges_iff
    (removed : Finset G.edgeSet)
    (component :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent)
    (edge : G.edgeSet) :
    edge ∈ componentCrossingEdges removed component ↔
      EdgeCrossesVertexSide G
        (fun vertex => vertex ∈ component.supp) edge := by
  simp [componentCrossingEdges]

/-!
An edge crossing a deletion component cannot survive the deletion.  This is
the only graph-theoretic separator fact needed by the exact-boundary
constructor below.
-/

omit [Fintype V] [DecidableRel G.Adj] in
theorem edge_mem_removed_of_crosses_component
    (removed : Finset G.edgeSet)
    (component :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent)
    (edge : G.edgeSet)
    (hcross : EdgeCrossesVertexSide G
      (fun vertex => vertex ∈ component.supp) edge) :
    edge ∈ removed := by
  rcases hcross with ⟨left, right, hleftEdge, hrightEdge,
    hleftComponent, hrightComponent⟩
  have hne : left ≠ right := by
    intro heq
    exact hrightComponent (heq ▸ hleftComponent)
  have hedgeValue : edge.1 = s(left, right) :=
    sym2_eq_mk_of_mem_of_mem_of_ne hleftEdge hrightEdge hne
  by_contra hnotMem
  have hnotValue : edge.1 ∉ edgeFinsetValueSet removed := by
    intro hvalue
    rcases (mem_edgeFinsetValueSet_iff removed edge.1).1 hvalue with
      ⟨other, hother, hotherValue⟩
    apply hnotMem
    simpa [Subtype.ext hotherValue] using hother
  have hadj : G.Adj left right :=
    (SimpleGraph.mem_edgeSet G).1 (by simpa [hedgeValue] using edge.2)
  have hdeleteAdj :
      (G.deleteEdges (edgeFinsetValueSet removed)).Adj left right := by
    rw [SimpleGraph.deleteEdges_adj]
    exact ⟨hadj, by simpa [← hedgeValue] using hnotValue⟩
  exact hrightComponent
    ((component.mem_supp_congr_adj hdeleteAdj).mp hleftComponent)

theorem componentCrossingEdges_subset_removed
    (removed : Finset G.edgeSet)
    (component :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent) :
    componentCrossingEdges removed component ⊆ removed := by
  intro edge hedge
  exact edge_mem_removed_of_crosses_component removed component edge
    ((mem_componentCrossingEdges_iff removed component edge).1 hedge)

theorem card_componentCrossingEdges_le_removed
    (removed : Finset G.edgeSet)
    (component :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent) :
    (componentCrossingEdges removed component).card ≤ removed.card :=
  Finset.card_le_card (componentCrossingEdges_subset_removed removed component)

/-!
The component side is constant along every walk that avoids the deleted
support.  This is the walk form of the endpoint boundary calculation and is
the exact graph lemma needed when a planar/Jordan argument supplies an
avoiding route around a wall vertex.
-/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem component_side_iff_of_walk_avoiding_removed
    (removed : Finset G.edgeSet)
    (component :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent)
    {u v : V} (walk : G.Walk u v)
    (havoid : ∀ edge : G.edgeSet, (edge : Sym2 V) ∈ walk.edges →
      edge.1 ∉ edgeFinsetValueSet removed) :
    (u ∈ component.supp ↔ v ∈ component.supp) := by
  induction walk with
  | nil =>
      exact Iff.rfl
  | @cons u v w hadj tail ih =>
      let edge : G.edgeSet := ⟨s(u, v), hadj⟩
      have hedge_mem : (edge : Sym2 V) ∈
          (SimpleGraph.Walk.cons hadj tail).edges := by
        simp [SimpleGraph.Walk.edges_cons, edge]
      have hedge_avoid : edge.1 ∉ edgeFinsetValueSet removed :=
        havoid edge hedge_mem
      have hdeleteAdj :
          (G.deleteEdges (edgeFinsetValueSet removed)).Adj u v := by
        rw [SimpleGraph.deleteEdges_adj]
        exact ⟨hadj, hedge_avoid⟩
      have hstep : u ∈ component.supp ↔ v ∈ component.supp :=
        component.mem_supp_congr_adj hdeleteAdj
      have htailAvoid : ∀ edge' : G.edgeSet,
          (edge' : Sym2 V) ∈ tail.edges →
            edge'.1 ∉ edgeFinsetValueSet removed := by
        intro edge' hedge'
        exact havoid edge' (by
          simp [SimpleGraph.Walk.edges_cons, hedge'])
      exact hstep.trans (ih htailAvoid)

/-!
The exact realization constructor.  Notice that the edge support in the
result is the *computed* component boundary.  Reusing a preselected deleted
support requires the separate equality
`componentCrossingEdges removed component = removed`; that equality is the
remaining saturation statement in a Jordan/chord application.
-/

def componentCyclicEdgeCutRealization
    (removed : Finset G.edgeSet)
    (component :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent)
    (hinsideCycle : HasCycleOnSide G
      (fun vertex => vertex ∈ component.supp))
    (houtsideCycle : HasCycleOnSide G
      (fun vertex => ¬ vertex ∈ component.supp)) :
    CyclicEdgeCutRealization G (componentCrossingEdges removed component) :=
  { side := fun vertex => vertex ∈ component.supp
    hcut_eq := fun edge => (mem_componentCrossingEdges_iff removed component edge)
    hinside_cycle := hinsideCycle
    houtside_cycle := houtsideCycle }

end

end GoertzelV24FiniteDeletionCyclicCut

end Mettapedia.GraphTheory.FourColor
