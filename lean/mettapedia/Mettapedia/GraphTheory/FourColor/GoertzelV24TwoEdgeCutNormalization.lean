import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicTwoEdgeCyclicCut
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TwoEdgeCutNormalization

open GoertzelV24CubicTwoEdgeCyclicCut
open GoertzelV24RotationEdgeBridge
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TwoEdgeCutCapGeometry
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- If one of two deleted edges crosses a deleted-graph component, then
bridge-freeness forces the other edge to cross it as well. Otherwise an
avoiding path around the first edge would have no way to leave the component. -/
theorem other_edge_crosses_delete_component_of_edgeBridgeFree
    (graphData : Data G)
    (hfree : EdgeBridgeFree graphData.toRotationSystem)
    (deletedFirst deletedSecond crossed other : G.edgeSet)
    (hpair : ({crossed, other} : Finset G.edgeSet) =
      {deletedFirst, deletedSecond})
    (component :
      (G.deleteEdges
        ({deletedFirst.1, deletedSecond.1} : Set (Sym2 V))).ConnectedComponent)
    (hcrossed : EdgeCrossesVertexSide G
      (fun vertex => vertex ∈ component.supp) crossed) :
    EdgeCrossesVertexSide G
      (fun vertex => vertex ∈ component.supp) other := by
  classical
  by_contra hother
  rcases hcrossed with
    ⟨inside, outside, hinsideCrossed, houtsideCrossed,
      hinsideComponent, houtsideComponent⟩
  have hvertices : inside ≠ outside := by
    intro heq
    exact houtsideComponent (heq ▸ hinsideComponent)
  have hcrossedValue : crossed.1 = s(inside, outside) :=
    sym2_eq_mk_of_mem_of_mem_of_ne
      hinsideCrossed houtsideCrossed hvertices
  have hadj : G.Adj inside outside :=
    (SimpleGraph.mem_edgeSet G).1 (by
      simpa [hcrossedValue] using crossed.2)
  let dart : G.Dart := ⟨(inside, outside), hadj⟩
  have hdartEdge : graphData.toRotationSystem.edgeOf dart = crossed := by
    apply Subtype.ext
    exact hcrossedValue.symm
  have hreach := hfree dart
  rw [hdartEdge,
    edgeDeletedPrimalGraph_toRotationSystem_eq graphData crossed] at hreach
  change (G.deleteEdges ({crossed.1} : Set (Sym2 V))).Reachable
    inside outside at hreach
  rcases hreach with ⟨avoidingWalk⟩
  let ambientWalk : G.Walk inside outside :=
    avoidingWalk.mapLe (G.deleteEdges_le ({crossed.1} : Set (Sym2 V)))
  have hambientEdges : ambientWalk.edges = avoidingWalk.edges :=
    avoidingWalk.edges_mapLe_eq_edges
      (G.deleteEdges_le ({crossed.1} : Set (Sym2 V)))
  rcases exists_edgeCrossesVertexSide_of_walk_endpoint_sides
      (fun vertex => vertex ∈ component.supp) ambientWalk
      hinsideComponent houtsideComponent with
    ⟨crossing, hcrossingWalk, hcrossing⟩
  have hcrossingPair :=
    edge_mem_pair_of_crosses_delete_component
      deletedFirst deletedSecond component crossing hcrossing
  rw [← hpair] at hcrossingPair
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcrossingPair
  rcases hcrossingPair with hcrossingCrossed | hcrossingOther
  · have havoidsCrossed : crossed.1 ∉ ambientWalk.edges := by
      intro hmem
      have hdeleted := avoidingWalk.edges_subset_edgeSet
        (by simpa [hambientEdges] using hmem)
      simp at hdeleted
    exact havoidsCrossed (by
      simpa [hcrossingCrossed] using hcrossingWalk)
  · exact hother (hcrossingOther ▸ hcrossing)

/-- Every proper component left after deleting two edges of a connected
bridge-free graph is crossed by both deleted edges. -/
theorem both_edges_cross_delete_component_of_edgeBridgeFree
    (graphData : Data G) (hconnected : G.Connected)
    (hfree : EdgeBridgeFree graphData.toRotationSystem)
    (first second : G.edgeSet)
    (component :
      (G.deleteEdges ({first.1, second.1} : Set (Sym2 V))).ConnectedComponent)
    (outside : V) (houtside : outside ∉ component.supp) :
    EdgeCrossesVertexSide G
        (fun vertex => vertex ∈ component.supp) first ∧
      EdgeCrossesVertexSide G
        (fun vertex => vertex ∈ component.supp) second := by
  classical
  rcases component.nonempty_supp with ⟨inside, hinside⟩
  rcases hconnected inside outside with ⟨walk⟩
  rcases exists_edgeCrossesVertexSide_of_walk_endpoint_sides
      (fun vertex => vertex ∈ component.supp) walk hinside houtside with
    ⟨crossing, _hcrossingWalk, hcrossing⟩
  have hcrossingPair :=
    edge_mem_pair_of_crosses_delete_component
      first second component crossing hcrossing
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcrossingPair
  rcases hcrossingPair with hfirst | hsecond
  · subst crossing
    exact ⟨hcrossing,
      other_edge_crosses_delete_component_of_edgeBridgeFree
        graphData hfree first second first second rfl component hcrossing⟩
  · subst crossing
    have hfirst :=
      other_edge_crosses_delete_component_of_edgeBridgeFree
        graphData hfree first second second first
          (Finset.pair_comm second first) component hcrossing
    exact ⟨hfirst, hcrossing⟩

/-- Once both deleted edges cross one component, bridge-freeness forces every
other deleted-graph vertex into a single complementary component. Hence the
complement of the chosen component is connected in the ambient graph. -/
theorem connected_induce_compl_delete_component_of_edgeBridgeFree
    (graphData : Data G) (hconnected : G.Connected)
    (hfree : EdgeBridgeFree graphData.toRotationSystem)
    (first second : G.edgeSet)
    (component :
      (G.deleteEdges ({first.1, second.1} : Set (Sym2 V))).ConnectedComponent)
    (hfirst : EdgeCrossesVertexSide G
      (fun vertex => vertex ∈ component.supp) first)
    (hsecond : EdgeCrossesVertexSide G
      (fun vertex => vertex ∈ component.supp) second) :
    (G.induce {vertex | vertex ∉ component.supp}).Connected := by
  classical
  rcases hfirst with
    ⟨firstInside, firstOutside, hfirstInsideEdge, hfirstOutsideEdge,
      hfirstInside, hfirstOutside⟩
  rcases hsecond with
    ⟨secondInside, secondOutside, hsecondInsideEdge, hsecondOutsideEdge,
      hsecondInside, hsecondOutside⟩
  have hfirstVertices : firstInside ≠ firstOutside := by
    intro heq
    exact hfirstOutside (heq ▸ hfirstInside)
  have hsecondVertices : secondInside ≠ secondOutside := by
    intro heq
    exact hsecondOutside (heq ▸ hsecondInside)
  have hfirstValue : first.1 = s(firstInside, firstOutside) :=
    sym2_eq_mk_of_mem_of_mem_of_ne
      hfirstInsideEdge hfirstOutsideEdge hfirstVertices
  have hsecondValue : second.1 = s(secondInside, secondOutside) :=
    sym2_eq_mk_of_mem_of_mem_of_ne
      hsecondInsideEdge hsecondOutsideEdge hsecondVertices
  let complementComponent :=
    (G.deleteEdges
      ({first.1, second.1} : Set (Sym2 V))).connectedComponentMk firstOutside
  have hfirstOutsideComplement :
      firstOutside ∈ complementComponent.supp :=
    ConnectedComponent.connectedComponentMk_mem
  have hfirstInsideNotComplement :
      firstInside ∉ complementComponent.supp := by
    intro hmem
    have heq : component = complementComponent :=
      ConnectedComponent.eq_of_common_vertex hfirstInside hmem
    apply hfirstOutside
    rw [heq]
    exact hfirstOutsideComplement
  have hfirstCrossesComplement : EdgeCrossesVertexSide G
      (fun vertex => vertex ∈ complementComponent.supp) first :=
    ⟨firstOutside, firstInside, hfirstOutsideEdge, hfirstInsideEdge,
      hfirstOutsideComplement, hfirstInsideNotComplement⟩
  have hsecondCrossesComplement : EdgeCrossesVertexSide G
      (fun vertex => vertex ∈ complementComponent.supp) second :=
    other_edge_crosses_delete_component_of_edgeBridgeFree
      graphData hfree first second first second rfl complementComponent
        hfirstCrossesComplement
  have hsecondInsideNotComplement :
      secondInside ∉ complementComponent.supp := by
    intro hmem
    have heq : component = complementComponent :=
      ConnectedComponent.eq_of_common_vertex hsecondInside hmem
    apply hfirstOutside
    rw [heq]
    exact hfirstOutsideComplement
  have hsecondOutsideComplement :
      secondOutside ∈ complementComponent.supp := by
    by_contra hnot
    exact
      (not_side_iff_of_edgeCrossesVertexSide_of_sym2_eq
        hsecondValue hsecondCrossesComplement)
        (iff_of_false hsecondInsideNotComplement hnot)
  have houtsideSubset :
      {vertex | vertex ∉ component.supp} ⊆ complementComponent.supp := by
    intro vertex hvertexOutside
    let vertexComponent :=
      (G.deleteEdges
        ({first.1, second.1} : Set (Sym2 V))).connectedComponentMk vertex
    have hvertexComponent : vertex ∈ vertexComponent.supp :=
      ConnectedComponent.connectedComponentMk_mem
    have hfirstInsideNotVertex : firstInside ∉ vertexComponent.supp := by
      intro hmem
      have heq : component = vertexComponent :=
        ConnectedComponent.eq_of_common_vertex hfirstInside hmem
      apply hvertexOutside
      rw [heq]
      exact hvertexComponent
    have hsecondInsideNotVertex : secondInside ∉ vertexComponent.supp := by
      intro hmem
      have heq : component = vertexComponent :=
        ConnectedComponent.eq_of_common_vertex hsecondInside hmem
      apply hvertexOutside
      rw [heq]
      exact hvertexComponent
    rcases component.nonempty_supp with ⟨insideVertex, hinsideVertex⟩
    have hinsideNotVertex : insideVertex ∉ vertexComponent.supp := by
      intro hmem
      have heq : component = vertexComponent :=
        ConnectedComponent.eq_of_common_vertex hinsideVertex hmem
      apply hvertexOutside
      rw [heq]
      exact hvertexComponent
    rcases hconnected vertex insideVertex with ⟨walk⟩
    rcases exists_edgeCrossesVertexSide_of_walk_endpoint_sides
        (fun candidate => candidate ∈ vertexComponent.supp) walk
        hvertexComponent hinsideNotVertex with
      ⟨crossing, _hcrossingWalk, hcrossing⟩
    have hcrossingPair :=
      edge_mem_pair_of_crosses_delete_component
        first second vertexComponent crossing hcrossing
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcrossingPair
    rcases hcrossingPair with hcrossingFirst | hcrossingSecond
    · subst crossing
      have hfirstOutsideVertex : firstOutside ∈ vertexComponent.supp := by
        by_contra hnot
        exact
          (not_side_iff_of_edgeCrossesVertexSide_of_sym2_eq
            hfirstValue hcrossing)
            (iff_of_false hfirstInsideNotVertex hnot)
      have heq : vertexComponent = complementComponent :=
        ConnectedComponent.eq_of_common_vertex
          hfirstOutsideVertex hfirstOutsideComplement
      rw [← heq]
      exact hvertexComponent
    · subst crossing
      have hsecondOutsideVertex : secondOutside ∈ vertexComponent.supp := by
        by_contra hnot
        exact
          (not_side_iff_of_edgeCrossesVertexSide_of_sym2_eq
            hsecondValue hcrossing)
            (iff_of_false hsecondInsideNotVertex hnot)
      have heq : vertexComponent = complementComponent :=
        ConnectedComponent.eq_of_common_vertex
          hsecondOutsideVertex hsecondOutsideComplement
      rw [← heq]
      exact hvertexComponent
  have hcomplementSubset :
      complementComponent.supp ⊆ {vertex | vertex ∉ component.supp} := by
    intro vertex hvertexComplement hvertexComponent
    have heq : component = complementComponent :=
      ConnectedComponent.eq_of_common_vertex
        hvertexComponent hvertexComplement
    apply hfirstOutside
    rw [heq]
    exact hfirstOutsideComplement
  have hsupport :
      {vertex | vertex ∉ component.supp} = complementComponent.supp :=
    Set.Subset.antisymm houtsideSubset hcomplementSubset
  rw [hsupport]
  exact connected_induce_component_of_delete_pair
    first second complementComponent

/-- In a cubic bridge-free graph, the two edges of an exact two-edge side
boundary have distinct endpoints on that side. If they met at one vertex, the
unique third incident edge would be the sole edge leaving the side after that
vertex is removed, hence a bridge. -/
theorem side_endpoints_ne_of_cubic_of_edgeBridgeFree
    (graphData : Data G)
    (hCubic : graphData.toRotationSystem.IsCubic)
    (hfree : EdgeBridgeFree graphData.toRotationSystem)
    (first second : G.edgeSet) (hedges : first ≠ second)
    (side : V → Prop)
    (hcrossingPair : ∀ edge : G.edgeSet,
      EdgeCrossesVertexSide G side edge →
        edge ∈ ({first, second} : Finset G.edgeSet))
    (hfirstCross : EdgeCrossesVertexSide G side first)
    (hsecondCross : EdgeCrossesVertexSide G side second)
    {firstVertex secondVertex : V}
    (hfirstVertexEdge : firstVertex ∈ (first : Sym2 V))
    (hfirstVertexSide : side firstVertex)
    (hsecondVertexEdge : secondVertex ∈ (second : Sym2 V))
    (hsecondVertexSide : side secondVertex) :
    firstVertex ≠ secondVertex := by
  classical
  intro hvertices
  subst secondVertex
  let shared := firstVertex
  let firstOutside := Sym2.Mem.other' hfirstVertexEdge
  let secondOutside := Sym2.Mem.other' hsecondVertexEdge
  have hfirstValue : first.1 = s(shared, firstOutside) := by
    exact (Sym2.other_spec' hfirstVertexEdge).symm
  have hsecondValue : second.1 = s(shared, secondOutside) := by
    exact (Sym2.other_spec' hsecondVertexEdge).symm
  have hfirstOutsideEdge : firstOutside ∈ (first : Sym2 V) :=
    Sym2.other_mem' hfirstVertexEdge
  have hsecondOutsideEdge : secondOutside ∈ (second : Sym2 V) :=
    Sym2.other_mem' hsecondVertexEdge
  have hfirstOutsideSide : ¬ side firstOutside := by
    intro hmem
    exact
      (not_side_iff_of_edgeCrossesVertexSide_of_sym2_eq
        hfirstValue hfirstCross)
        ⟨fun _ => hmem, fun _ => hfirstVertexSide⟩
  have hsecondOutsideSide : ¬ side secondOutside := by
    intro hmem
    exact
      (not_side_iff_of_edgeCrossesVertexSide_of_sym2_eq
        hsecondValue hsecondCross)
        ⟨fun _ => hmem, fun _ => hfirstVertexSide⟩
  let RS := graphData.toRotationSystem
  have hfirstIncident : first ∈ RS.incidentEdges shared :=
    (RS.mem_endpoints_iff_mem_incidentEdges).1
      ((mem_simpleGraphRotationSystem_endpoints_iff
        graphData first shared).2 hfirstVertexEdge)
  have hsecondIncident : second ∈ RS.incidentEdges shared :=
    (RS.mem_endpoints_iff_mem_incidentEdges).1
      ((mem_simpleGraphRotationSystem_endpoints_iff
        graphData second shared).2 hsecondVertexEdge)
  have hthirdExists : ∃ third : G.edgeSet,
      third ∈ RS.incidentEdges shared ∧
        third ≠ first ∧ third ≠ second := by
    by_contra hnot
    push Not at hnot
    have hsubset : RS.incidentEdges shared ⊆
        ({first, second} : Finset G.edgeSet) := by
      intro edge hedge
      by_cases hedgeFirst : edge = first
      · simp [hedgeFirst]
      · have hedgeSecond := hnot edge hedge hedgeFirst
        simp [hedgeSecond]
    have hcard := Finset.card_le_card hsubset
    rw [RS.incidentEdges_card_eq_three_of_isCubic hCubic shared] at hcard
    have hpairCard : ({first, second} : Finset G.edgeSet).card ≤ 2 :=
      Finset.card_le_two
    omega
  rcases hthirdExists with
    ⟨third, hthirdIncident, hthirdFirst, hthirdSecond⟩
  have htripleSubset : ({first, second, third} : Finset G.edgeSet) ⊆
      RS.incidentEdges shared := by
    intro edge hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl | rfl
    · exact hfirstIncident
    · exact hsecondIncident
    · exact hthirdIncident
  have htripleCard : ({first, second, third} : Finset G.edgeSet).card = 3 := by
    simp [hedges, hthirdFirst.symm, hthirdSecond.symm]
  have htripleEq : ({first, second, third} : Finset G.edgeSet) =
      RS.incidentEdges shared := by
    apply Finset.eq_of_subset_of_card_le htripleSubset
    rw [htripleCard,
      RS.incidentEdges_card_eq_three_of_isCubic hCubic shared]
  have hthirdSharedRS : shared ∈ RS.endpoints third :=
    (RS.mem_endpoints_iff_mem_incidentEdges).2 hthirdIncident
  have hthirdShared : shared ∈ (third : Sym2 V) :=
    (mem_simpleGraphRotationSystem_endpoints_iff
      graphData third shared).1 hthirdSharedRS
  let thirdInside := Sym2.Mem.other' hthirdShared
  have hthirdValue : third.1 = s(shared, thirdInside) := by
    exact (Sym2.other_spec' hthirdShared).symm
  have hthirdInsideEdge : thirdInside ∈ (third : Sym2 V) :=
    Sym2.other_mem' hthirdShared
  have hthirdInsideSide : side thirdInside := by
    by_contra houtside
    have hcross : EdgeCrossesVertexSide G side third :=
      ⟨shared, thirdInside, hthirdShared, hthirdInsideEdge,
        hfirstVertexSide, houtside⟩
    have hpair := hcrossingPair third hcross
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpair
    exact hpair.elim hthirdFirst hthirdSecond
  have hthirdVertices : shared ≠ thirdInside := by
    intro heq
    have : third.1 = s(shared, shared) := by simpa [heq] using hthirdValue
    exact G.loopless.irrefl shared
      ((SimpleGraph.mem_edgeSet G).1 (this ▸ third.2))
  have hfirstInsideUnique : ∀ {vertex : V},
      vertex ∈ (first : Sym2 V) → side vertex →
        vertex = shared := by
    intro vertex hedge hside
    rw [hfirstValue, Sym2.mem_iff] at hedge
    rcases hedge with rfl | houtside
    · rfl
    · exact False.elim (hfirstOutsideSide (houtside ▸ hside))
  have hsecondInsideUnique : ∀ {vertex : V},
      vertex ∈ (second : Sym2 V) → side vertex →
        vertex = shared := by
    intro vertex hedge hside
    rw [hsecondValue, Sym2.mem_iff] at hedge
    rcases hedge with rfl | houtside
    · rfl
    · exact False.elim (hsecondOutsideSide (houtside ▸ hside))
  have hcrossReduced_eq_third : ∀ edge : G.edgeSet,
      EdgeCrossesVertexSide G
        (fun vertex => side vertex ∧ vertex ≠ shared) edge →
      edge = third := by
    intro edge hcross
    rcases hcross with
      ⟨inside, outside, hinsideEdge, houtsideEdge,
        hinsideSide, houtsideSide⟩
    by_cases houtsideComponent : side outside
    · have houtsideShared : outside = shared := by
        by_contra hne
        exact houtsideSide ⟨houtsideComponent, hne⟩
      subst outside
      have hedgeEndpointsRS : shared ∈ RS.endpoints edge :=
        (mem_simpleGraphRotationSystem_endpoints_iff
          graphData edge shared).2 houtsideEdge
      have hedgeIncident : edge ∈ RS.incidentEdges shared :=
        (RS.mem_endpoints_iff_mem_incidentEdges).1 hedgeEndpointsRS
      have hedgeTriple : edge ∈
          ({first, second, third} : Finset G.edgeSet) := by
        rw [htripleEq]
        exact hedgeIncident
      simp only [Finset.mem_insert, Finset.mem_singleton] at hedgeTriple
      rcases hedgeTriple with hedgeFirst | hedgeSecond | hedgeThird
      · subst edge
        exact False.elim
          (hinsideSide.2
            (hfirstInsideUnique hinsideEdge hinsideSide.1))
      · subst edge
        exact False.elim
          (hinsideSide.2
            (hsecondInsideUnique hinsideEdge hinsideSide.1))
      · exact hedgeThird
    · have hcrossComponent : EdgeCrossesVertexSide G side edge :=
        ⟨inside, outside, hinsideEdge, houtsideEdge,
          hinsideSide.1, houtsideComponent⟩
      have hedgePair := hcrossingPair edge hcrossComponent
      simp only [Finset.mem_insert, Finset.mem_singleton] at hedgePair
      rcases hedgePair with hedgeFirst | hedgeSecond
      · subst edge
        exact False.elim
          (hinsideSide.2
            (hfirstInsideUnique hinsideEdge hinsideSide.1))
      · subst edge
        exact False.elim
          (hinsideSide.2
            (hsecondInsideUnique hinsideEdge hinsideSide.1))
  have hthirdAdj : G.Adj shared thirdInside :=
    (SimpleGraph.mem_edgeSet G).1 (by
      simpa [hthirdValue] using third.2)
  let thirdDart : G.Dart := ⟨(shared, thirdInside), hthirdAdj⟩
  have hthirdDartEdge : RS.edgeOf thirdDart = third := by
    apply Subtype.ext
    exact hthirdValue.symm
  have hreach := hfree thirdDart
  rw [hthirdDartEdge,
    edgeDeletedPrimalGraph_toRotationSystem_eq graphData third] at hreach
  change (G.deleteEdges ({third.1} : Set (Sym2 V))).Reachable
    shared thirdInside at hreach
  rcases hreach.symm with ⟨avoidingWalk⟩
  let ambientWalk : G.Walk thirdInside shared :=
    avoidingWalk.mapLe (G.deleteEdges_le ({third.1} : Set (Sym2 V)))
  have hambientEdges : ambientWalk.edges = avoidingWalk.edges :=
    avoidingWalk.edges_mapLe_eq_edges
      (G.deleteEdges_le ({third.1} : Set (Sym2 V)))
  rcases exists_edgeCrossesVertexSide_of_walk_endpoint_sides
      (fun vertex => side vertex ∧ vertex ≠ shared)
      ambientWalk ⟨hthirdInsideSide, hthirdVertices.symm⟩
      (fun h => h.2 rfl) with
    ⟨crossing, hcrossingWalk, hcrossing⟩
  have hcrossingThird := hcrossReduced_eq_third crossing hcrossing
  have havoidsThird : third.1 ∉ ambientWalk.edges := by
    intro hmem
    have hdeleted := avoidingWalk.edges_subset_edgeSet
      (by simpa [hambientEdges] using hmem)
    simp at hdeleted
  exact havoidsThird (by
    simpa [hcrossingThird] using hcrossingWalk)

/-- The retained vertex of a graph-backed boundary dart is an endpoint of
the underlying simple-graph edge. -/
theorem boundaryDart_vertex_mem_graphEdge
    (graphData : Data G) (keep : V → Prop)
    (dart : GoertzelV24RotationCutDartDecomposition.BoundaryDart
      graphData.toRotationSystem keep)
    (edge : G.edgeSet)
    (hedge : graphData.toRotationSystem.edgeOf dart.1.1 = edge) :
    graphData.toRotationSystem.vertOf dart.1.1 ∈ (edge : Sym2 V) := by
  apply (mem_simpleGraphRotationSystem_endpoints_iff graphData edge _).1
  rw [graphData.toRotationSystem.mem_endpoints_iff]
  exact ⟨dart.1.1,
    (graphData.toRotationSystem.mem_dartsOn).2 hedge, rfl⟩

/-- A proper component of a two-edge deletion in a connected cubic
bridge-free graph canonically supplies exact cap data. Both induced sides are
connected, and cubic bridge-freeness discharges the two non-collision fields. -/
theorem exists_twoEdgeCutPairData_of_delete_component
    (graphData : Data G) (hconnected : G.Connected)
    (hCubic : graphData.toRotationSystem.IsCubic)
    (hfree : EdgeBridgeFree graphData.toRotationSystem)
    (first second : G.edgeSet) (hedges : first ≠ second)
    (component :
      (G.deleteEdges ({first.1, second.1} : Set (Sym2 V))).ConnectedComponent)
    (outside : V) (houtside : outside ∉ component.supp) :
    ∃ cut : graphData.toRotationSystem.TwoEdgeCutPairData,
      (G.induce {vertex | vertex ∈ cut.side}).Connected ∧
        (G.induce {vertex | vertex ∈ cut.sideᶜ}).Connected := by
  classical
  let side : Finset V := component.supp.toFinset
  obtain ⟨hfirstCross, hsecondCross⟩ :=
    both_edges_cross_delete_component_of_edgeBridgeFree
      graphData hconnected hfree first second component outside houtside
  have hsideCrossingPair : ∀ edge : G.edgeSet,
      EdgeCrossesVertexSide G (fun vertex => vertex ∈ component.supp) edge →
        edge ∈ ({first, second} : Finset G.edgeSet) := by
    intro edge hcross
    exact edge_mem_pair_of_crosses_delete_component
      first second component edge hcross
  have hfirstComplement : EdgeCrossesVertexSide G
      (fun vertex => vertex ∉ component.supp) first :=
    (edgeCrossesVertexSide_compl G
      (fun vertex => vertex ∈ component.supp) first).2 hfirstCross
  have hsecondComplement : EdgeCrossesVertexSide G
      (fun vertex => vertex ∉ component.supp) second :=
    (edgeCrossesVertexSide_compl G
      (fun vertex => vertex ∈ component.supp) second).2 hsecondCross
  have hcomplementCrossingPair : ∀ edge : G.edgeSet,
      EdgeCrossesVertexSide G (fun vertex => vertex ∉ component.supp) edge →
        edge ∈ ({first, second} : Finset G.edgeSet) := by
    intro edge hcross
    apply hsideCrossingPair edge
    exact (edgeCrossesVertexSide_compl G
      (fun vertex => vertex ∈ component.supp) edge).1 hcross
  have hboundary : graphData.toRotationSystem.vertexSideEdgeBoundary side =
      ({first, second} : Finset G.edgeSet) := by
    rw [← vertexSetCrossingEdges_eq_vertexSideEdgeBoundary]
    ext edge
    rw [mem_simpleGraph_vertexSetCrossingEdges_iff]
    constructor
    · intro hcross
      exact hsideCrossingPair edge (by simpa [side] using hcross)
    · intro hedge
      simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
      rcases hedge with rfl | rfl
      · simpa [side] using hfirstCross
      · simpa [side] using hsecondCross
  have hsideSet : {vertex | vertex ∈ side} = component.supp := by
    ext vertex
    simp [side]
  have hcomplementSet : {vertex | vertex ∈ sideᶜ} =
      {vertex | vertex ∉ component.supp} := by
    ext vertex
    simp [side]
  have hsideConnected :
      (G.induce {vertex | vertex ∈ side}).Connected := by
    rw [hsideSet]
    exact connected_induce_component_of_delete_pair first second component
  have hcomplementConnected :
      (G.induce {vertex | vertex ∈ sideᶜ}).Connected := by
    rw [hcomplementSet]
    exact connected_induce_compl_delete_component_of_edgeBridgeFree
      graphData hconnected hfree first second component
        hfirstCross hsecondCross
  let cut : graphData.toRotationSystem.TwoEdgeCutPairData :=
    { side := side
      leftEdge := first
      rightEdge := second
      edges_ne := hedges
      boundary_eq := hboundary
      sideRetainedEndpointsDistinct := by
        intro left right hleft hright
        apply side_endpoints_ne_of_cubic_of_edgeBridgeFree
          graphData hCubic hfree first second hedges
          (fun vertex => vertex ∈ component.supp)
          hsideCrossingPair hfirstCross hsecondCross
        · exact boundaryDart_vertex_mem_graphEdge
            graphData (fun vertex => vertex ∈ side) left first hleft
        · simpa [side] using left.1.2
        · exact boundaryDart_vertex_mem_graphEdge
            graphData (fun vertex => vertex ∈ side) right second hright
        · simpa [side] using right.1.2
      complementRetainedEndpointsDistinct := by
        intro left right hleft hright
        apply side_endpoints_ne_of_cubic_of_edgeBridgeFree
          graphData hCubic hfree first second hedges
          (fun vertex => vertex ∉ component.supp)
          hcomplementCrossingPair hfirstComplement hsecondComplement
        · exact boundaryDart_vertex_mem_graphEdge
            graphData (fun vertex => vertex ∈ sideᶜ) left first hleft
        · simpa [side] using left.1.2
        · exact boundaryDart_vertex_mem_graphEdge
            graphData (fun vertex => vertex ∈ sideᶜ) right second hright
        · simpa [side] using right.1.2 }
  exact ⟨cut, hsideConnected, hcomplementConnected⟩

/-- If deleting two distinct edges disconnects a connected cubic bridge-free
graph, one deleted-graph component normalizes to exact cap data with both
induced sides connected. -/
theorem exists_twoEdgeCutPairData_of_not_connected_deleteEdges_pair
    (graphData : Data G) (hconnected : G.Connected)
    (hCubic : graphData.toRotationSystem.IsCubic)
    (hfree : EdgeBridgeFree graphData.toRotationSystem)
    (first second : G.edgeSet) (hedges : first ≠ second)
    (hdelete :
      ¬ (G.deleteEdges
        ({first.1, second.1} : Set (Sym2 V))).Connected) :
    ∃ cut : graphData.toRotationSystem.TwoEdgeCutPairData,
      (G.induce {vertex | vertex ∈ cut.side}).Connected ∧
        (G.induce {vertex | vertex ∈ cut.sideᶜ}).Connected := by
  classical
  let deleted := G.deleteEdges
    ({first.1, second.1} : Set (Sym2 V))
  letI : Nonempty V := hconnected.nonempty
  have hnotPreconnected : ¬ deleted.Preconnected := by
    intro hpreconnected
    exact hdelete ⟨hpreconnected⟩
  rw [SimpleGraph.Preconnected] at hnotPreconnected
  push Not at hnotPreconnected
  rcases hnotPreconnected with
    ⟨insideVertex, outsideVertex, hnotReachable⟩
  let component := deleted.connectedComponentMk insideVertex
  have houtside : outsideVertex ∉ component.supp := by
    intro hmem
    apply hnotReachable
    apply ConnectedComponent.exact
    exact ((ConnectedComponent.mem_supp_iff component outsideVertex).1 hmem).symm
  exact exists_twoEdgeCutPairData_of_delete_component
    graphData hconnected hCubic hfree first second hedges
      component outsideVertex houtside

/-- Strict two-edge connectivity of a graph-backed vertex-minimal Tait
counterexample: deleting any two distinct edges leaves the graph connected.
All exact-cut hypotheses are produced by the normalization theorem above. -/
theorem deleteEdges_pair_connected_of_vertexMinimalTaitCounterexample
    (graphData : Data G)
    (minimal :
      GoertzelV24TwoEdgeCutMinimality.GraphBackedVertexMinimalTaitCounterexample
        graphData)
    (first second : G.edgeSet) (hedges : first ≠ second) :
    (G.deleteEdges
      ({first.1, second.1} : Set (Sym2 V))).Connected := by
  by_contra hdelete
  have hconnected : G.Connected := by
    rw [← GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
      G graphData]
    exact minimal.primalConnected
  obtain ⟨cut, hsideConnected, hcomplementConnected⟩ :=
    exists_twoEdgeCutPairData_of_not_connected_deleteEdges_pair
      graphData hconnected minimal.spherical.cubic minimal.edgeBridgeFree
        first second hedges hdelete
  exact GoertzelV24TwoEdgeCutMinimality.no_connected_twoEdgeCutPairData
    graphData minimal cut hsideConnected hcomplementConnected

end

end GoertzelV24TwoEdgeCutNormalization

end Mettapedia.GraphTheory.FourColor
