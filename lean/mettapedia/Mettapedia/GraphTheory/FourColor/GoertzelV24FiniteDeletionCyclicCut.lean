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

omit [DecidableEq V] in
/-- If two deletion components are distinct, connectedness of the original
graph forces the computed boundary of either one to contain an edge.  This is
pure finite graph theory: it neither supplies a planar side nor identifies the
computed boundary with a proposed dual wall. -/
theorem componentCrossingEdges_nonempty_of_distinct
    (hconnected : G.Connected) (removed : Finset G.edgeSet)
    (inside outside :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent)
    (hdistinct : inside ≠ outside) :
    (componentCrossingEdges removed inside).Nonempty := by
  rcases inside.nonempty_supp with ⟨insideVertex, hinside⟩
  rcases outside.nonempty_supp with ⟨outsideVertex, houtside⟩
  have houtsideNotInside : outsideVertex ∉ inside.supp := by
    intro hcommon
    apply hdistinct
    exact SimpleGraph.ConnectedComponent.eq_of_common_vertex hcommon houtside
  rcases hconnected insideVertex outsideVertex with ⟨walk⟩
  rcases exists_edgeCrossesVertexSide_of_walk_endpoint_sides
      (fun vertex => vertex ∈ inside.supp) walk hinside houtsideNotInside with
    ⟨edge, _hwalkEdge, hcross⟩
  exact ⟨edge,
    (mem_componentCrossingEdges_iff removed inside edge).2 hcross⟩

omit [DecidableEq V] in
/-- A finite edge deletion that disconnects a connected graph has a component
with a nonempty computed boundary.  Later annular geometry must still prove
which component is the intended side and provide its two cycle witnesses. -/
theorem exists_componentCrossingEdges_nonempty_of_not_connected
    (hconnected : G.Connected) (removed : Finset G.edgeSet)
    (hdelete : ¬ (G.deleteEdges (edgeFinsetValueSet removed)).Connected) :
    ∃ component :
        (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent,
      (componentCrossingEdges removed component).Nonempty := by
  let deleted := G.deleteEdges (edgeFinsetValueSet removed)
  letI : Nonempty V := hconnected.nonempty
  have hnotPreconnected : ¬ deleted.Preconnected := by
    intro hpreconnected
    exact hdelete ⟨hpreconnected⟩
  rw [SimpleGraph.Preconnected] at hnotPreconnected
  push Not at hnotPreconnected
  rcases hnotPreconnected with ⟨insideVertex, outsideVertex, hnotReachable⟩
  let inside := deleted.connectedComponentMk insideVertex
  let outside := deleted.connectedComponentMk outsideVertex
  refine ⟨inside, ?_⟩
  apply componentCrossingEdges_nonempty_of_distinct hconnected removed inside outside
  intro heq
  exact hnotReachable (SimpleGraph.ConnectedComponent.exact heq)

/-!
The saturation equality is often the only set-theoretic line left after a
Jordan/annulus argument has identified the two sides of the deleted wall.  We
keep it as a named generic lemma so callers prove the geometric fact in its
natural direction (`every removed edge crosses`) instead of reproving the
computed-boundary subset argument.
-/

theorem componentCrossingEdges_eq_removed_of_forall_removed_crosses
    (removed : Finset G.edgeSet)
    (component :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent)
    (hcross : ∀ edge : G.edgeSet, edge ∈ removed →
      EdgeCrossesVertexSide G (fun vertex => vertex ∈ component.supp) edge) :
    componentCrossingEdges removed component = removed := by
  apply Finset.Subset.antisymm
  · exact componentCrossingEdges_subset_removed removed component
  · intro edge hedge
    exact (mem_componentCrossingEdges_iff removed component edge).2
      (hcross edge hedge)

/-- If every deletion component sees the same nonempty removed boundary,
then the complement of any chosen component is connected.  This is the
finite graph form of the two-side conclusion needed after a simple dual
separator: a removed edge has only two endpoints, so it cannot cross three
different saturated components. -/
theorem induce_complement_connected_of_component_boundary_saturation
    (removed : Finset G.edgeSet)
    (component :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent)
    (hremoved : removed.Nonempty)
    (hsaturation : ∀ other :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent,
      componentCrossingEdges removed other = removed) :
    (G.induce (fun vertex => vertex ∉ component.supp)).Connected := by
  rcases hremoved with ⟨edge, hedge⟩
  have hcrossComponent : EdgeCrossesVertexSide G
      (fun vertex => vertex ∈ component.supp) edge := by
    apply (mem_componentCrossingEdges_iff removed component edge).1
    rw [hsaturation component]
    exact hedge
  rcases hcrossComponent with ⟨inside, outside, hinsideEdge, houtsideEdge,
    hinside, houtside⟩
  have hinsideNeOutside : inside ≠ outside := by
    intro heq
    exact houtside (heq ▸ hinside)
  have hedgePair : (edge : Sym2 V) = s(inside, outside) :=
    sym2_eq_mk_of_mem_of_mem_of_ne hinsideEdge houtsideEdge hinsideNeOutside
  let otherComponent :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent :=
    (G.deleteEdges (edgeFinsetValueSet removed)).connectedComponentMk outside
  have houtsideOther : outside ∈ otherComponent.supp := by
    dsimp [otherComponent]
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hotherNeComponent : otherComponent ≠ component := by
    intro heq
    exact houtside (heq ▸ houtsideOther)
  have outside_mem_of_ne
      (candidate :
        (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent)
      (hcandidate : candidate ≠ component) :
      outside ∈ candidate.supp := by
    have hcrossCandidate : EdgeCrossesVertexSide G
        (fun vertex => vertex ∈ candidate.supp) edge := by
      apply (mem_componentCrossingEdges_iff removed candidate edge).1
      rw [hsaturation candidate]
      exact hedge
    rcases hcrossCandidate with ⟨endpoint, opposite, hendpointEdge,
      _hoppositeEdge, hendpointCandidate, _hopposite⟩
    rw [hedgePair] at hendpointEdge
    rcases (Sym2.mem_iff.mp hendpointEdge) with hinsideEq | houtsideEq
    · exfalso
      apply hcandidate
      have hinsideCandidate : inside ∈ candidate.supp := by
        simpa [hinsideEq] using hendpointCandidate
      exact SimpleGraph.ConnectedComponent.eq_of_common_vertex
        hinsideCandidate hinside
    · simpa [houtsideEq] using hendpointCandidate
  have hcomplement_eq_other :
      (fun vertex => vertex ∉ component.supp) = otherComponent.supp := by
    funext vertex
    apply propext
    constructor
    · intro hnotComponent
      let candidate :
          (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent :=
        (G.deleteEdges (edgeFinsetValueSet removed)).connectedComponentMk vertex
      have hvertexCandidate : vertex ∈ candidate.supp := by
        dsimp [candidate]
        exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
      have hcandidateNe : candidate ≠ component := by
        intro heq
        exact hnotComponent (heq ▸ hvertexCandidate)
      have houtsideCandidate : outside ∈ candidate.supp :=
        outside_mem_of_ne candidate hcandidateNe
      have hcandidateEq : candidate = otherComponent :=
        SimpleGraph.ConnectedComponent.eq_of_common_vertex
          houtsideCandidate houtsideOther
      exact hcandidateEq ▸ hvertexCandidate
    · intro hvertexOther hvertexComponent
      apply hotherNeComponent
      exact SimpleGraph.ConnectedComponent.eq_of_common_vertex
        hvertexOther hvertexComponent
  rw [hcomplement_eq_other]
  exact otherComponent.connected_toSimpleGraph.mono (by
    intro left right hadj
    exact (G.deleteEdges_le (edgeFinsetValueSet removed)) hadj)

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

/-- The component construction can be reindexed to a proposed finite support
when the planar layer has proved boundary saturation.  This is the useful
bridge for a Jordan/chord argument: the component side supplies all wall
seams automatically, while the one remaining geometric equality identifies
its computed boundary with the intended chord support. -/
def componentCyclicEdgeCutRealization_of_edgeCut_eq
    (removed : Finset G.edgeSet)
    (component :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent)
    {edgeCut : Finset G.edgeSet}
    (hboundary : componentCrossingEdges removed component = edgeCut)
    (hinsideCycle : HasCycleOnSide G
      (fun vertex => vertex ∈ component.supp))
    (houtsideCycle : HasCycleOnSide G
      (fun vertex => ¬ vertex ∈ component.supp)) :
    CyclicEdgeCutRealization G edgeCut := by
  rw [← hboundary]
  exact componentCyclicEdgeCutRealization removed component
    hinsideCycle houtsideCycle

def componentCyclicEdgeCutRealization_of_forall_removed_crosses
    (removed : Finset G.edgeSet)
    (component :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent)
    (hcross : ∀ edge : G.edgeSet, edge ∈ removed →
      EdgeCrossesVertexSide G (fun vertex => vertex ∈ component.supp) edge)
    (hinsideCycle : HasCycleOnSide G
      (fun vertex => vertex ∈ component.supp))
    (houtsideCycle : HasCycleOnSide G
      (fun vertex => ¬ vertex ∈ component.supp)) :
    CyclicEdgeCutRealization G removed :=
  componentCyclicEdgeCutRealization_of_edgeCut_eq
    removed component
    (componentCrossingEdges_eq_removed_of_forall_removed_crosses
      removed component hcross)
    hinsideCycle houtsideCycle

/-- Away from the computed component boundary, an ambient edge preserves the
component side.  This is the local form used to discharge all non-wall edges
once boundary saturation has been established. -/
theorem component_side_iff_of_edge_not_mem_componentCrossingEdges
    (removed : Finset G.edgeSet)
    (component :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent)
    {edge : G.edgeSet}
    (hedge : edge ∉ componentCrossingEdges removed component)
    {u v : V} (hu : u ∈ (edge : Sym2 V)) (hv : v ∈ (edge : Sym2 V)) :
    (u ∈ component.supp ↔ v ∈ component.supp) := by
  have hnotCross : ¬ EdgeCrossesVertexSide G
      (fun vertex => vertex ∈ component.supp) edge := by
    intro hcross
    exact hedge ((mem_componentCrossingEdges_iff removed component edge).2 hcross)
  exact (not_edgeCrossesVertexSide_iff_forall_side_iff
    G (fun vertex => vertex ∈ component.supp) edge).1 hnotCross u v hu hv

/-- A closed walk avoiding the deleted support stays wholly in one deletion
component once its root is known to lie there.  This packages the side-cycle
obligation in the form supplied by the annular hole walks. -/
theorem hasCycleOnSide_of_walk_avoiding_removed
    (removed : Finset G.edgeSet)
    (component :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent)
    {root : V} (walk : G.Walk root root) (hcycle : walk.IsCycle)
    (havoid : ∀ edge : G.edgeSet, (edge : Sym2 V) ∈ walk.edges →
      edge.1 ∉ edgeFinsetValueSet removed)
    (hroot : root ∈ component.supp) :
    HasCycleOnSide G (fun vertex => vertex ∈ component.supp) := by
  refine ⟨root, hroot, walk, hcycle, ?_⟩
  intro vertex hvertex
  let pfx := walk.takeUntil vertex hvertex
  have hprefixAvoid : ∀ edge : G.edgeSet,
      (edge : Sym2 V) ∈ pfx.edges →
        edge.1 ∉ edgeFinsetValueSet removed := by
    intro edge hedge
    exact havoid edge
      (walk.edges_takeUntil_subset_edges hvertex hedge)
  have hside := component_side_iff_of_walk_avoiding_removed
    removed component pfx hprefixAvoid
  exact hside.mp hroot

/-- The complementary side-cycle variant of
`hasCycleOnSide_of_walk_avoiding_removed`. -/
theorem hasCycleOnComplementSide_of_walk_avoiding_removed
    (removed : Finset G.edgeSet)
    (component :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent)
    {root : V} (walk : G.Walk root root) (hcycle : walk.IsCycle)
    (havoid : ∀ edge : G.edgeSet, (edge : Sym2 V) ∈ walk.edges →
      edge.1 ∉ edgeFinsetValueSet removed)
    (hroot : ¬ root ∈ component.supp) :
    HasCycleOnSide G (fun vertex => ¬ vertex ∈ component.supp) := by
  refine ⟨root, hroot, walk, hcycle, ?_⟩
  intro vertex hvertex hcomponent
  let pfx := walk.takeUntil vertex hvertex
  have hprefixAvoid : ∀ edge : G.edgeSet,
      (edge : Sym2 V) ∈ pfx.edges →
        edge.1 ∉ edgeFinsetValueSet removed := by
    intro edge hedge
    exact havoid edge
      (walk.edges_takeUntil_subset_edges hvertex hedge)
  have hside := component_side_iff_of_walk_avoiding_removed
    removed component pfx hprefixAvoid
  exact hroot (hside.mpr hcomponent)

/-- A compact annular-witness constructor: once two closed walks avoid the
deleted support and start on opposite deletion sides, the only remaining
geometric datum needed for an exact cyclic cut is boundary saturation. -/
def componentCyclicEdgeCutRealization_of_edgeCut_eq_of_avoiding_cycle_witnesses
    (removed : Finset G.edgeSet)
    (component :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent)
    {edgeCut : Finset G.edgeSet}
    (hboundary : componentCrossingEdges removed component = edgeCut)
    {insideRoot outsideRoot : V}
    (insideWalk : G.Walk insideRoot insideRoot)
    (outsideWalk : G.Walk outsideRoot outsideRoot)
    (hinsideCycle : insideWalk.IsCycle)
    (houtsideCycle : outsideWalk.IsCycle)
    (hinsideAvoid : ∀ edge : G.edgeSet,
      (edge : Sym2 V) ∈ insideWalk.edges →
        edge.1 ∉ edgeFinsetValueSet removed)
    (houtsideAvoid : ∀ edge : G.edgeSet,
      (edge : Sym2 V) ∈ outsideWalk.edges →
        edge.1 ∉ edgeFinsetValueSet removed)
    (hinsideRoot : insideRoot ∈ component.supp)
    (houtsideRoot : ¬ outsideRoot ∈ component.supp) :
    CyclicEdgeCutRealization G edgeCut :=
  componentCyclicEdgeCutRealization_of_edgeCut_eq
    removed component hboundary
    (hasCycleOnSide_of_walk_avoiding_removed
      removed component insideWalk hinsideCycle hinsideAvoid hinsideRoot)
    (hasCycleOnComplementSide_of_walk_avoiding_removed
      removed component outsideWalk houtsideCycle houtsideAvoid houtsideRoot)

end

end GoertzelV24FiniteDeletionCyclicCut

end Mettapedia.GraphTheory.FourColor
