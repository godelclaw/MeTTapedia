import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalSeparator
import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicSmallBoundaryCycle

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [hAdjDecidable : DecidableRel G.Adj]

noncomputable section

local instance finiteGraphLocallyFinite (G : SimpleGraph V)
    [decidableAdjacency : DecidableRel G.Adj] :
    G.LocallyFinite := fun vertex =>
  @Subtype.fintype V (Membership.mem (G.neighborSet vertex))
    (decidableAdjacency vertex) inferInstance

namespace GoertzelV24FiniteEdgeDeletion

/-- Values of a finite collection of graph-edge subtypes, viewed as an
ambient set of unordered vertex pairs. -/
def edgeFinsetValueSet (removed : Finset G.edgeSet) : Set (Sym2 V) :=
  Subtype.val '' (removed : Set G.edgeSet)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem mem_edgeFinsetValueSet_iff
    (removed : Finset G.edgeSet) (edge : Sym2 V) :
    edge ∈ edgeFinsetValueSet removed ↔
      ∃ graphEdge ∈ removed, graphEdge.1 = edge := by
  simp [edgeFinsetValueSet]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Passing from graph-edge subtypes to their unordered-pair values does not
change the finite cardinality. -/
theorem ncard_edgeFinsetValueSet (removed : Finset G.edgeSet) :
    (edgeFinsetValueSet removed).ncard = removed.card := by
  rw [edgeFinsetValueSet,
    Set.ncard_image_of_injective _ Subtype.val_injective,
    Set.ncard_coe_finset]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- An edge crossing a component after a finite edge deletion must be one of
the deleted edges. -/
theorem edge_mem_removed_of_crosses_delete_component
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

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every outgoing dart of a finite-deletion component is supported on the
deleted edge set. -/
theorem crossingSideDart_edge_mem_removed
    (removed : Finset G.edgeSet)
    (component :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent)
    (dart : CrossingSideDart G
      (fun vertex => vertex ∈ component.supp)) :
    (⟨dart.1.edge, dart.1.edge_mem⟩ : G.edgeSet) ∈ removed := by
  apply edge_mem_removed_of_crosses_delete_component removed component
  refine ⟨dart.1.fst, dart.1.snd, ?_, ?_, dart.2.1, dart.2.2⟩
  · change dart.1.fst ∈ s(dart.1.fst, dart.1.snd)
    simp
  · change dart.1.snd ∈ s(dart.1.fst, dart.1.snd)
    simp

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A component of a finite edge deletion remains connected when induced in
the original graph. -/
theorem connected_induce_delete_component
    (removed : Finset G.edgeSet)
    (component :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent) :
    (G.induce component.supp).Connected := by
  exact component.connected_toSimpleGraph.mono (by
    intro left right hadj
    exact (G.deleteEdges_le (edgeFinsetValueSet removed)) hadj)

/-- The exact boundary support of one finite-deletion component. -/
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

omit [DecidableEq V] in
/-- A deletion component's exact boundary is contained in the finite set
that was deleted. -/
theorem componentCrossingEdges_subset_removed
    (removed : Finset G.edgeSet)
    (component :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent) :
    componentCrossingEdges removed component ⊆ removed := by
  intro edge hedge
  exact edge_mem_removed_of_crosses_delete_component removed component edge
    ((mem_componentCrossingEdges_iff removed component edge).1 hedge)

omit [DecidableEq V] in
theorem card_componentCrossingEdges_le_removed
    (removed : Finset G.edgeSet)
    (component :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent) :
    (componentCrossingEdges removed component).card ≤ removed.card :=
  Finset.card_le_card (componentCrossingEdges_subset_removed removed component)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Disconnecting a connected graph by a finite edge deletion produces two
distinct deletion components. -/
theorem exists_distinct_components_of_not_connected
    (hconnected : G.Connected) (removed : Finset G.edgeSet)
    (hdelete :
      ¬ (G.deleteEdges (edgeFinsetValueSet removed)).Connected) :
    ∃ inside outside :
        (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent,
      inside ≠ outside := by
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
  refine ⟨inside, outside, ?_⟩
  intro heq
  exact hnotReachable (SimpleGraph.ConnectedComponent.exact heq)

end GoertzelV24FiniteEdgeDeletion

namespace GoertzelV24CubicSmallBoundaryCycle

/-- A connected nonempty side of a cubic graph behind at most four listed
boundary edges either contains a cycle or has at most two vertices. -/
theorem hasCycleOnSide_or_card_le_two_of_cubic_of_connected_induce_of_crossing_le_four
    (hregular : G.IsRegularOfDegree 3) (side : V → Prop)
    (hsideNonempty : ∃ vertex, side vertex)
    (hsideConnected : (G.induce {vertex | side vertex}).Connected)
    (removed : Finset G.edgeSet) (hremovedCard : removed.card ≤ 4)
    (hcrossingRemoved : ∀ dart : CrossingSideDart G side,
      (⟨dart.1.edge, dart.1.edge_mem⟩ : G.edgeSet) ∈ removed) :
    HasCycleOnSide G side ∨
      Nat.card {vertex : V // side vertex} ≤ 2 := by
  by_cases hcycle : HasCycleOnSide G side
  · exact Or.inl hcycle
  · right
    let sideFintype : Fintype {vertex : V // side vertex} :=
      Fintype.ofInjective (fun vertex => vertex.1) Subtype.val_injective
    letI sideSubtypeFintype : Fintype {vertex : V // side vertex} :=
      sideFintype
    letI sideSetFintype : Fintype ↑({vertex | side vertex} : Set V) :=
      sideFintype
    rw [Nat.card_eq_fintype_card]
    have hsideAcyclic : (G.induce {vertex | side vertex}).IsAcyclic := by
      intro vertex cycle hcycle'
      apply hcycle
      let inclusion :=
        (SimpleGraph.Embedding.induce (G := G) {vertex | side vertex}).toHom
      refine ⟨vertex.1, vertex.2, cycle.map inclusion, ?_, ?_⟩
      · exact hcycle'.map (fun _ _ heq => Subtype.ext heq)
      · intro other hother
        have hother' : other ∈ cycle.support.map inclusion := by
          exact SimpleGraph.Walk.support_map inclusion cycle ▸ hother
        rcases List.mem_map.mp hother' with
          ⟨source, _hsource, hsource⟩
        rw [← hsource]
        exact source.2
    have htree : (G.induce {vertex | side vertex}).IsTree :=
      ⟨hsideConnected, hsideAcyclic⟩
    have htreeCard := htree.card_edgeFinset
    have hpartition := Fintype.card_congr
      (sideDartEquivInternalSumCrossing G side)
    rw [Fintype.card_sum] at hpartition
    have hsideCard := card_sideDart_eq_three_mul hregular side
    have hinternalCard := card_internalSideDart_eq_twice_card_edges
      (G := G) side
    have hcrossingCard := card_crossingSideDart_le_card_removed
      side removed hcrossingRemoved
    have hsidePositive :
        0 < Fintype.card {vertex : V // side vertex} :=
      Fintype.card_pos_iff.mpr ⟨⟨hsideNonempty.choose,
        hsideNonempty.choose_spec⟩⟩
    have hsameSideCard :
        Fintype.card ↑({vertex | side vertex} : Set V) =
          Fintype.card {vertex : V // side vertex} := by
      rfl
    omega

end GoertzelV24CubicSmallBoundaryCycle

namespace GoertzelV24FiniteEdgeDeletion

/-- A component behind at most four deleted edges inherits the cubic
cycle-or-two-vertices dichotomy. -/
theorem component_hasCycle_or_card_le_two
    (hregular : G.IsRegularOfDegree 3)
    (removed : Finset G.edgeSet) (hremovedCard : removed.card ≤ 4)
    (component :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent) :
    HasCycleOnSide G (fun vertex => vertex ∈ component.supp) ∨
      Nat.card {vertex : V // vertex ∈ component.supp} ≤ 2 := by
  exact
    hasCycleOnSide_or_card_le_two_of_cubic_of_connected_induce_of_crossing_le_four
      hregular (fun vertex => vertex ∈ component.supp)
      component.nonempty_supp
      (connected_induce_delete_component removed component)
      removed hremovedCard
      (crossingSideDart_edge_mem_removed removed component)

/-- In a cyclically five-edge-connected cubic graph, any disconnecting
deletion of at most four edges has a component containing at most two
vertices. Otherwise two large components would supply cycles on opposite
sides of an exact small cyclic cut. -/
theorem exists_component_card_le_two_of_cyclicallyFive_of_not_connected
    (hregular : G.IsRegularOfDegree 3) (hconnected : G.Connected)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (removed : Finset G.edgeSet) (hremovedCard : removed.card ≤ 4)
    (hdelete :
      ¬ (G.deleteEdges (edgeFinsetValueSet removed)).Connected) :
    ∃ component :
        (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent,
      Nat.card {vertex : V // vertex ∈ component.supp} ≤ 2 := by
  rcases exists_distinct_components_of_not_connected hconnected removed hdelete
    with ⟨inside, outside, hcomponents⟩
  by_cases hinsideSmall :
      Nat.card {vertex : V // vertex ∈ inside.supp} ≤ 2
  · exact ⟨inside, hinsideSmall⟩
  by_cases houtsideSmall :
      Nat.card {vertex : V // vertex ∈ outside.supp} ≤ 2
  · exact ⟨outside, houtsideSmall⟩
  have hinsideCycle :
      HasCycleOnSide G (fun vertex => vertex ∈ inside.supp) :=
    (component_hasCycle_or_card_le_two hregular removed hremovedCard inside).resolve_right
      hinsideSmall
  have houtsideComponentCycle :
      HasCycleOnSide G (fun vertex => vertex ∈ outside.supp) :=
    (component_hasCycle_or_card_le_two hregular removed hremovedCard outside).resolve_right
      houtsideSmall
  have houtsideCycle :
      HasCycleOnSide G (fun vertex => ¬ vertex ∈ inside.supp) :=
    HasCycleOnSide.mono (fun vertex houtside hinside =>
      hcomponents
        (SimpleGraph.ConnectedComponent.eq_of_common_vertex
          hinside houtside)) houtsideComponentCycle
  let edgeCut := componentCrossingEdges removed inside
  have hedgeCutCard : edgeCut.card ≤ removed.card :=
    card_componentCrossingEdges_le_removed removed inside
  have hedgeCutCardFour : edgeCut.card ≤ 4 :=
    le_trans hedgeCutCard hremovedCard
  let realization : CyclicEdgeCutRealization G edgeCut :=
    { side := fun vertex => vertex ∈ inside.supp
      hcut_eq := fun edge =>
        mem_componentCrossingEdges_iff removed inside edge
      hinside_cycle := hinsideCycle
      houtside_cycle := houtsideCycle }
  exact False.elim
    (hcyclic.noCyclicEdgeCutOfSizeAtMostFour
      ⟨realization.toSmallCyclicEdgeCut hedgeCutCardFour,
        hedgeCutCardFour⟩)

end GoertzelV24FiniteEdgeDeletion

namespace GoertzelV24DualCycleSeparator

attribute [local instance] graphEdgeSetDecidableEq

/-- The set-valued primal cut of a dual walk is the ambient-value image of
its finite collection of crossing graph edges. -/
theorem dualWalkPrimalCut_eq_edgeFinsetValueSet_dualWalkCrossingEdges
    (data : Data G)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem)))
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Walk start start) :
    dualWalkPrimalCut data hunique walk =
      GoertzelV24FiniteEdgeDeletion.edgeFinsetValueSet
        (dualWalkCrossingEdges
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace data.toRotationSystem)) hunique walk) := by
  ext edge
  rw [GoertzelV24FiniteEdgeDeletion.mem_edgeFinsetValueSet_iff]
  constructor
  · rintro ⟨step, hstep⟩
    let crossing := dualWalkCrossingEdge
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk step
    refine ⟨crossing, ?_, hstep⟩
    exact (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
      crossing).2 ⟨step, rfl⟩
  · rintro ⟨crossing, hcrossing, hvalue⟩
    rcases (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
      crossing).1 hcrossing with ⟨step, hstep⟩
    exact ⟨step, congrArg Subtype.val hstep |>.trans hvalue⟩

/-- A separating simple dual cycle of length at most four in a cubic,
cyclically five-edge-connected graph cuts off a component with at most two
vertices. -/
theorem exists_primalCut_component_card_le_two_of_isCycle_of_length_le_four
    (data : Data G) (hregular : G.IsRegularOfDegree 3)
    (hconnected : G.Connected) (hcyclic : CyclicallyFiveEdgeConnected G)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem)))
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Walk start start)
    (hcycle : walk.IsCycle) (hlength : walk.length ≤ 4)
    (hdelete :
      ¬ (G.deleteEdges (dualWalkPrimalCut data hunique walk)).Connected) :
    ∃ component :
        (G.deleteEdges (dualWalkPrimalCut data hunique walk)).ConnectedComponent,
      Nat.card {vertex : V // vertex ∈ component.supp} ≤ 2 := by
  let removed := dualWalkCrossingEdges
    (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
  have hremovedCard : removed.card ≤ 4 := by
    rw [GoertzelV24DualPathTransversal.card_dualWalkCrossingEdges_eq_length_of_isCycle
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      (orbitFace_incidence_le_two data.toRotationSystem) hunique walk hcycle]
    exact hlength
  have hcutEq :=
    dualWalkPrimalCut_eq_edgeFinsetValueSet_dualWalkCrossingEdges
      data hunique walk
  rw [hcutEq] at hdelete ⊢
  exact
    GoertzelV24FiniteEdgeDeletion.exists_component_card_le_two_of_cyclicallyFive_of_not_connected
      hregular hconnected hcyclic removed hremovedCard hdelete

end GoertzelV24DualCycleSeparator

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

local instance canonicalGraphLocallyFinite (G : SimpleGraph V)
    [decidableAdjacency : DecidableRel G.Adj] :
    G.LocallyFinite := fun vertex =>
  @Subtype.fintype V (Membership.mem (G.neighborSet vertex))
    (decidableAdjacency vertex) inferInstance

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace ClosureRecoveryFaceTransferCircuit

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- Under cyclic five-connectivity, a saturated recovery circuit of length
at most four supplies a remote primal separator and a deletion component
with at most two vertices. -/
theorem exists_remote_primal_separator_with_small_component
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength)
    (hshort : rebaseCircuit.arcLength ≤ 4) :
    ∃ walk :
        (interiorDualGraph
          (orbitFaceBoundary graphData.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace graphData.toRotationSystem))).Walk
          rebaseCircuit.first.dualFace rebaseCircuit.first.dualFace,
      walk.IsCycle ∧
        ¬ (G.deleteEdges
          (GoertzelV24DualCycleSeparator.dualWalkPrimalCut graphData
            (pairwiseUniqueSharedInteriorEdges graphData minimal)
            walk)).Connected ∧
        (GoertzelV24DualCycleSeparator.dualWalkPrimalCut graphData
          (pairwiseUniqueSharedInteriorEdges graphData minimal) walk).ncard =
            rebaseCircuit.arcLength ∧
        (∃ component :
            (G.deleteEdges
              (GoertzelV24DualCycleSeparator.dualWalkPrimalCut graphData
                (pairwiseUniqueSharedInteriorEdges graphData minimal)
                walk)).ConnectedComponent,
          Nat.card {vertex : V // vertex ∈ component.supp} ≤ 2) ∧
        (∀ face ∈ walk.support,
          centralEdge
              (baseData.rotationOrderedData graphData
                minimal.spherical.cubic minimal.vertexRotationCyclic) ∉
            orbitFaceBoundary graphData.toRotationSystem face.1) ∧
        (∀ face ∈ walk.support, ∀ port : Fin 4,
          boundaryEdge
              (baseData.rotationOrderedData graphData
                minimal.spherical.cubic minimal.vertexRotationCyclic) port ∉
            orbitFaceBoundary graphData.toRotationSystem face.1) := by
  rcases circuit.exists_remote_primal_separator hminimal hlength with
    ⟨walk, hcycle, hdelete, hcard, hcentral, hboundary⟩
  have hregular : G.IsRegularOfDegree 3 :=
    graphData.toRotationSystem_isCubic_iff.mp minimal.spherical.cubic
  have hconnected : G.Connected := by
    rw [← GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
      G graphData]
    exact minimal.primalConnected
  have hwalkLength : walk.length = rebaseCircuit.arcLength := by
    rw [← GoertzelV24DualCycleSeparator.ncard_dualWalkPrimalCut_eq_length_of_isCycle
      graphData (pairwiseUniqueSharedInteriorEdges graphData minimal)
        walk hcycle]
    exact hcard
  have hsmall :=
    GoertzelV24DualCycleSeparator.exists_primalCut_component_card_le_two_of_isCycle_of_length_le_four
      graphData hregular hconnected hcyclic
        (pairwiseUniqueSharedInteriorEdges graphData minimal) walk hcycle
        (hwalkLength.trans_le hshort) hdelete
  exact ⟨walk, hcycle, hdelete, hcard, hsmall, hcentral, hboundary⟩

end ClosureRecoveryFaceTransferCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
