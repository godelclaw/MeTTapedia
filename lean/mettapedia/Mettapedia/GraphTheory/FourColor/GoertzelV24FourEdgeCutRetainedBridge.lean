import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicSmallBoundaryCycle
import Mettapedia.GraphTheory.FourColor.GoertzelV24FourEdgeCutPlanarClosures

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FourEdgeCutRetainedBridge

open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24CyclicExactCutConnectedSides
open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24FourEdgeCutNoncrossingInterfaces
open GoertzelV24FourEdgeCutPlanarClosures
open GoertzelV24FourEdgeCutBoundaryToggle
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RetainedSpliceEdgeDecomposition
open GoertzelV24RetainedSplicePrimalGraph
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationEdgeBridge
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24ThreeEdgeCutMinimality
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The graph induced on the complement side of a cyclic cut. -/
abbrev retainedCutGraph (G : SimpleGraph V) (cut : SmallCyclicEdgeCut G) :=
  G.induce {vertex | ¬ cut.side vertex}

/-- The ambient graph edge represented by a dart of the retained induced
graph. -/
def retainedDartAmbientEdge
    (cut : SmallCyclicEdgeCut G) (dart : (retainedCutGraph G cut).Dart) :
    G.edgeSet :=
  ⟨s(dart.fst.1, dart.snd.1), dart.adj⟩

@[simp]
theorem retainedDartAmbientEdge_value
    (cut : SmallCyclicEdgeCut G) (dart : (retainedCutGraph G cut).Dart) :
    (retainedDartAmbientEdge cut dart : Sym2 V) =
      s(dart.fst.1, dart.snd.1) :=
  rfl

/-- Lift one component of a retained-edge deletion back to an ambient
vertex-side predicate. -/
def retainedDeleteComponentSide
    (cut : SmallCyclicEdgeCut G)
    (removed : (retainedCutGraph G cut).Dart)
    (component : ((retainedCutGraph G cut).deleteEdges
      {removed.edge}).ConnectedComponent) : V → Prop :=
  fun vertex => ∃ hretained : ¬ cut.side vertex,
    (⟨vertex, hretained⟩ : {point : V // ¬ cut.side point}) ∈
      component.supp

theorem retainedDeleteComponentSide_retained
    (cut : SmallCyclicEdgeCut G)
    (removed : (retainedCutGraph G cut).Dart)
    (component : ((retainedCutGraph G cut).deleteEdges
      {removed.edge}).ConnectedComponent)
    {vertex : V}
    (hvertex : retainedDeleteComponentSide cut removed component vertex) :
    ¬ cut.side vertex := by
  exact hvertex.choose

/-- A retained deletion component is connected when viewed as an induced
subgraph of the ambient graph. -/
theorem retainedDeleteComponentSide_connected
    (cut : SmallCyclicEdgeCut G)
    (removed : (retainedCutGraph G cut).Dart)
    (component : ((retainedCutGraph G cut).deleteEdges
      {removed.edge}).ConnectedComponent) :
    (G.induce {vertex |
      retainedDeleteComponentSide cut removed component vertex}).Connected := by
  let source := component.toSimpleGraph
  let target := G.induce {vertex |
    retainedDeleteComponentSide cut removed component vertex}
  let mapVertex : component →
      {vertex : V |
        retainedDeleteComponentSide cut removed component vertex} :=
    fun vertex => ⟨vertex.1.1, ⟨vertex.1.2, vertex.2⟩⟩
  let hom : source →g target :=
    { toFun := mapVertex
      map_rel' := by
        intro left right hadj
        exact hadj.1 }
  let rootSource : component := ⟨component.out, component.out_eq⟩
  letI : Nonempty
      {vertex : V |
        retainedDeleteComponentSide cut removed component vertex} :=
    ⟨mapVertex rootSource⟩
  refine ⟨?_⟩
  intro left right
  rcases left.2 with ⟨hleftRetained, hleftComponent⟩
  rcases right.2 with ⟨hrightRetained, hrightComponent⟩
  let leftSource : component :=
    ⟨⟨left.1, hleftRetained⟩, hleftComponent⟩
  let rightSource : component :=
    ⟨⟨right.1, hrightRetained⟩, hrightComponent⟩
  have hreach := component.connected_toSimpleGraph leftSource rightSource
  have hmapped := hreach.map hom
  change target.Reachable left right
  convert hmapped using 1 <;> apply Subtype.ext <;> rfl

/-- An edge internal to the retained side is not one of the original cut
edges. -/
theorem retainedDartAmbientEdge_not_mem_cut
    (cut : SmallCyclicEdgeCut G)
    (dart : (retainedCutGraph G cut).Dart) :
    retainedDartAmbientEdge cut dart ∉ cut.edgeCut := by
  intro hedge
  have hcross := (cut.edge_mem_iff
    (retainedDartAmbientEdge cut dart)).1 hedge
  have hopposite := not_side_iff_of_edgeCrossesVertexSide_of_sym2_eq
    (retainedDartAmbientEdge_value cut dart) hcross
  apply hopposite
  constructor
  · intro hleft
    exact False.elim (dart.fst.2 hleft)
  · intro hright
    exact False.elim (dart.snd.2 hright)

/-- Every ambient edge leaving a component of a retained-edge deletion is
either the deleted retained edge itself or one of the original four cut
edges. -/
theorem retainedDeleteComponentSide_crossingEdge
    (cut : SmallCyclicEdgeCut G)
    (removed : (retainedCutGraph G cut).Dart)
    (component : ((retainedCutGraph G cut).deleteEdges
      {removed.edge}).ConnectedComponent)
    (dart : CrossingSideDart G
      (retainedDeleteComponentSide cut removed component)) :
    (⟨dart.1.edge, dart.1.edge_mem⟩ : G.edgeSet) =
        retainedDartAmbientEdge cut removed ∨
      (⟨dart.1.edge, dart.1.edge_mem⟩ : G.edgeSet) ∈ cut.edgeCut := by
  let edge : G.edgeSet := ⟨dart.1.edge, dart.1.edge_mem⟩
  by_cases hfinishDeleted : cut.side dart.1.snd
  · right
    apply (cut.edge_mem_iff edge).2
    refine ⟨dart.1.snd, dart.1.fst, ?_, ?_, hfinishDeleted, ?_⟩
    · change dart.1.snd ∈ s(dart.1.fst, dart.1.snd)
      simp
    · change dart.1.fst ∈ s(dart.1.fst, dart.1.snd)
      simp
    · exact retainedDeleteComponentSide_retained cut removed component
        dart.2.1
  · by_cases hedge : edge = retainedDartAmbientEdge cut removed
    · exact Or.inl hedge
    · exfalso
      rcases dart.2.1 with ⟨hstartRetained, hstartComponent⟩
      let start : {vertex : V // ¬ cut.side vertex} :=
        ⟨dart.1.fst, hstartRetained⟩
      let finish : {vertex : V // ¬ cut.side vertex} :=
        ⟨dart.1.snd, hfinishDeleted⟩
      have hnotRemoved : s(start, finish) ≠ removed.edge := by
        intro heq
        apply hedge
        apply Subtype.ext
        have hvalue := congrArg
          (Sym2.map (fun vertex : {point : V // ¬ cut.side point} =>
            vertex.1)) heq
        simpa [edge, start, finish, retainedDartAmbientEdge,
          SimpleGraph.Dart.edge, Sym2.map_mk] using hvalue
      have hadj :
          ((retainedCutGraph G cut).deleteEdges {removed.edge}).Adj
            start finish := by
        rw [SimpleGraph.deleteEdges_adj]
        refine ⟨dart.1.adj, ?_⟩
        intro hmem
        exact hnotRemoved (Set.mem_singleton_iff.mp hmem)
      have hfinishComponent : finish ∈ component.supp :=
        component.mem_supp_of_adj_mem_supp hstartComponent hadj
      exact dart.2.2 ⟨hfinishDeleted, hfinishComponent⟩

/-- Edge-level form of the retained-component crossing classification. -/
theorem retainedDeleteComponentSide_crossingEdge_mem
    (cut : SmallCyclicEdgeCut G)
    (removed : (retainedCutGraph G cut).Dart)
    (component : ((retainedCutGraph G cut).deleteEdges
      {removed.edge}).ConnectedComponent)
    (edge : G.edgeSet)
    (hcross : EdgeCrossesVertexSide G
      (retainedDeleteComponentSide cut removed component) edge) :
    edge = retainedDartAmbientEdge cut removed ∨ edge ∈ cut.edgeCut := by
  rcases hcross with
    ⟨start, finish, hstartEdge, hfinishEdge, hstartSide, hfinishSide⟩
  have hne : start ≠ finish := by
    intro heq
    exact hfinishSide (heq ▸ hstartSide)
  have hedgeValue : edge.1 = s(start, finish) :=
    sym2_eq_mk_of_mem_of_mem_of_ne hstartEdge hfinishEdge hne
  have hadj : G.Adj start finish :=
    (SimpleGraph.mem_edgeSet G).1 (by
      simpa [hedgeValue] using edge.2)
  let dart : CrossingSideDart G
      (retainedDeleteComponentSide cut removed component) :=
    ⟨⟨(start, finish), hadj⟩, hstartSide, hfinishSide⟩
  have hclassified := retainedDeleteComponentSide_crossingEdge
    cut removed component dart
  have hdartEdge :
      (⟨dart.1.edge, dart.1.edge_mem⟩ : G.edgeSet) = edge := by
    apply Subtype.ext
    exact hedgeValue.symm
  rw [hdartEdge] at hclassified
  exact hclassified

/-- The exact ambient edge boundary of one retained deletion component. -/
def retainedDeleteComponentEdgeCut
    (cut : SmallCyclicEdgeCut G)
    (removed : (retainedCutGraph G cut).Dart)
    (component : ((retainedCutGraph G cut).deleteEdges
      {removed.edge}).ConnectedComponent) : Finset G.edgeSet := by
  classical
  exact Finset.univ.filter fun edge =>
    EdgeCrossesVertexSide G
      (retainedDeleteComponentSide cut removed component) edge

@[simp]
theorem mem_retainedDeleteComponentEdgeCut_iff
    (cut : SmallCyclicEdgeCut G)
    (removed : (retainedCutGraph G cut).Dart)
    (component : ((retainedCutGraph G cut).deleteEdges
      {removed.edge}).ConnectedComponent)
    (edge : G.edgeSet) :
    edge ∈ retainedDeleteComponentEdgeCut cut removed component ↔
      EdgeCrossesVertexSide G
        (retainedDeleteComponentSide cut removed component) edge := by
  simp [retainedDeleteComponentEdgeCut]

/-- One original cut edge cannot cross two distinct retained deletion
components: its retained endpoint is unique. -/
theorem not_crosses_distinct_retainedDeleteComponents
    (cut : SmallCyclicEdgeCut G)
    (removed : (retainedCutGraph G cut).Dart)
    {first second : ((retainedCutGraph G cut).deleteEdges
      {removed.edge}).ConnectedComponent}
    (hcomponents : first ≠ second)
    (edge : G.edgeSet) (hedgeCut : edge ∈ cut.edgeCut)
    (hfirst : EdgeCrossesVertexSide G
      (retainedDeleteComponentSide cut removed first) edge)
    (hsecond : EdgeCrossesVertexSide G
      (retainedDeleteComponentSide cut removed second) edge) : False := by
  rcases hfirst with
    ⟨firstVertex, firstOutside, hfirstEdge, _hfirstOutsideEdge,
      hfirstSide, _hfirstOutside⟩
  rcases hsecond with
    ⟨secondVertex, secondOutside, hsecondEdge, _hsecondOutsideEdge,
      hsecondSide, _hsecondOutside⟩
  rcases hfirstSide with ⟨hfirstRetained, hfirstComponent⟩
  rcases hsecondSide with ⟨hsecondRetained, hsecondComponent⟩
  have hvertices : firstVertex ≠ secondVertex := by
    intro heq
    subst secondVertex
    apply hcomponents
    exact ConnectedComponent.eq_of_common_vertex
      hfirstComponent hsecondComponent
  have hedgeValue : edge.1 = s(firstVertex, secondVertex) :=
    sym2_eq_mk_of_mem_of_mem_of_ne
      hfirstEdge hsecondEdge hvertices
  have hcutCross := (cut.edge_mem_iff edge).1 hedgeCut
  have hopposite := not_side_iff_of_edgeCrossesVertexSide_of_sym2_eq
    hedgeValue hcutCross
  apply hopposite
  constructor
  · intro hfirstDeleted
    exact False.elim (hfirstRetained hfirstDeleted)
  · intro hsecondDeleted
    exact False.elim (hsecondRetained hsecondDeleted)

/-- For a finite connected acyclic side of a cubic graph, the number of
outgoing darts is exactly the number of side vertices plus two. -/
theorem card_crossingSideDart_eq_card_add_two_of_cubic_of_noCycle
    (hregular : G.IsRegularOfDegree 3) (side : V → Prop)
    (hsideConnected : (G.induce {vertex | side vertex}).Connected)
    (hnoCycle : ¬ HasCycleOnSide G side) :
    Fintype.card (CrossingSideDart G side) =
      Nat.card {vertex : V // side vertex} + 2 := by
  let sideFintype : Fintype {vertex : V // side vertex} :=
    Fintype.ofInjective (fun vertex => vertex.1) Subtype.val_injective
  letI sideSubtypeFintype : Fintype {vertex : V // side vertex} :=
    sideFintype
  letI sideSetFintype : Fintype ↑({vertex | side vertex} : Set V) :=
    sideFintype
  have hsideAcyclic :
      (G.induce {vertex | side vertex}).IsAcyclic := by
    intro vertex cycle hcycle
    apply hnoCycle
    let inclusion :=
      (SimpleGraph.Embedding.induce
        (G := G) {vertex | side vertex}).toHom
    refine ⟨vertex.1, vertex.2, cycle.map inclusion, ?_, ?_⟩
    · exact hcycle.map (fun _ _ heq => Subtype.ext heq)
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
  have hsideDartCard := card_sideDart_eq_three_mul hregular side
  have hinternalDartCard := card_internalSideDart_eq_twice_card_edges
    (G := G) side
  have hsidePositive :
      0 < Fintype.card {vertex : V // side vertex} :=
    Fintype.card_pos_iff.mpr hsideConnected.nonempty
  have hsameSideCard :
      Fintype.card ↑({vertex | side vertex} : Set V) =
        Fintype.card {vertex : V // side vertex} := by
    rfl
  have hnatCard : Nat.card {vertex : V // side vertex} =
      Fintype.card {vertex : V // side vertex} :=
    Nat.card_eq_fintype_card
  omega

/-- Distinct original cut edges cannot leave the same retained deletion
component at the same vertex. Consequently every such component contains
an ambient cycle. -/
theorem retainedDeleteComponentSide_hasCycle
    (hregular : G.IsRegularOfDegree 3)
    (hcubic : ∀ vertex, (incidentEdgeFinset G vertex).card = 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (removed : (retainedCutGraph G cut).Dart)
    (component : ((retainedCutGraph G cut).deleteEdges
      {removed.edge}).ConnectedComponent) :
    HasCycleOnSide G
      (retainedDeleteComponentSide cut removed component) := by
  let side := retainedDeleteComponentSide cut removed component
  let special := retainedDartAmbientEdge cut removed
  by_contra hnoCycle
  have hcount :=
    card_crossingSideDart_eq_card_add_two_of_cubic_of_noCycle
      hregular side
      (retainedDeleteComponentSide_connected cut removed component)
      hnoCycle
  let encode : CrossingSideDart G side →
      Option {vertex : V // side vertex} := fun dart =>
    if hedge : (⟨dart.1.edge, dart.1.edge_mem⟩ : G.edgeSet) = special
    then none
    else some ⟨dart.1.fst, dart.2.1⟩
  have hencode : Function.Injective encode := by
    intro left right heq
    let leftEdge : G.edgeSet := ⟨left.1.edge, left.1.edge_mem⟩
    let rightEdge : G.edgeSet := ⟨right.1.edge, right.1.edge_mem⟩
    by_cases hleftSpecial : leftEdge = special
    · by_cases hrightSpecial : rightEdge = special
      · apply crossingSideDart_edge_injective side
        exact hleftSpecial.trans hrightSpecial.symm
      · simp [encode, leftEdge, rightEdge, hleftSpecial,
          hrightSpecial] at heq
    · by_cases hrightSpecial : rightEdge = special
      · simp [encode, leftEdge, rightEdge, hleftSpecial,
          hrightSpecial] at heq
      · have hvertices : left.1.fst = right.1.fst := by
          have hsubtypes :
              (⟨left.1.fst, left.2.1⟩ : {vertex : V // side vertex}) =
                ⟨right.1.fst, right.2.1⟩ := by
            simpa [encode, leftEdge, rightEdge, hleftSpecial,
              hrightSpecial] using heq
          exact congrArg Subtype.val hsubtypes
        have hleftCut : leftEdge ∈ cut.edgeCut :=
          (retainedDeleteComponentSide_crossingEdge
            cut removed component left).resolve_left hleftSpecial
        have hrightCut : rightEdge ∈ cut.edgeCut :=
          (retainedDeleteComponentSide_crossingEdge
            cut removed component right).resolve_left hrightSpecial
        have hleftIncident : leftEdge ∈
            incidentEdgeFinset G left.1.fst := by
          simp [incidentEdgeFinset, leftEdge,
            SimpleGraph.Dart.edge]
        have hrightIncident : rightEdge ∈
            incidentEdgeFinset G left.1.fst := by
          simp [incidentEdgeFinset, rightEdge,
            SimpleGraph.Dart.edge, hvertices]
        have hedges : leftEdge = rightEdge := by
          by_contra hedges
          exact no_two_cut_edges_share_side_vertex hcubic hcyclic
            cut.compl (by simpa using hcard) left.1.fst
            (retainedDeleteComponentSide_retained
              cut removed component left.2.1)
            hedges hleftIncident hrightIncident
            (by simpa using hleftCut) (by simpa using hrightCut)
        apply crossingSideDart_edge_injective side
        exact hedges
  have hcardBound := Fintype.card_le_of_injective encode hencode
  have hoptionCard : Fintype.card
      (Option {vertex : V // side vertex}) =
        Nat.card {vertex : V // side vertex} + 1 := by
    rw [Fintype.card_option, Nat.card_eq_fintype_card]
  rw [hoptionCard] at hcardBound
  omega

/-- The complement side of an exact cyclic four-cut is bridge-free. A
hypothetical retained bridge has two deletion components. Cubic counting
and distinct cut incidences force a cycle in each component; cyclic
four-connectivity would then require at least three original cut edges on
each side of the bridge, contradicting the four-edge boundary. -/
theorem retainedCutGraph_edgeBridgeFree
    (graphData : Data G)
    (hregular : G.IsRegularOfDegree 3)
    (hcubic : ∀ vertex, (incidentEdgeFinset G vertex).card = 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (hambientFree : EdgeBridgeFree graphData.toRotationSystem) :
    ∀ removed : (retainedCutGraph G cut).Dart,
      ((retainedCutGraph G cut).deleteEdges {removed.edge}).Reachable
        removed.fst removed.snd := by
  intro removed
  by_contra hnotReachable
  let retained := retainedCutGraph G cut
  let deleted := retained.deleteEdges {removed.edge}
  let leftComponent := deleted.connectedComponentMk removed.fst
  let rightComponent := deleted.connectedComponentMk removed.snd
  have hcomponents : leftComponent ≠ rightComponent := by
    intro heq
    exact hnotReachable (ConnectedComponent.exact heq)
  let leftSide := retainedDeleteComponentSide cut removed leftComponent
  let rightSide := retainedDeleteComponentSide cut removed rightComponent
  have hleftRoot : leftSide removed.fst.1 := by
    exact ⟨removed.fst.2,
      ConnectedComponent.connectedComponentMk_mem⟩
  have hrightRoot : rightSide removed.snd.1 := by
    exact ⟨removed.snd.2,
      ConnectedComponent.connectedComponentMk_mem⟩
  have hrightNotLeft : ¬ leftSide removed.snd.1 := by
    rintro ⟨_hretained, hrightLeft⟩
    apply hcomponents
    exact ConnectedComponent.eq_of_common_vertex
      hrightLeft ConnectedComponent.connectedComponentMk_mem
  have hleftNotRight : ¬ rightSide removed.fst.1 := by
    rintro ⟨_hretained, hleftRight⟩
    apply hcomponents
    exact ConnectedComponent.eq_of_common_vertex
      ConnectedComponent.connectedComponentMk_mem hleftRight
  have hsidesDisjoint : ∀ vertex, rightSide vertex → ¬ leftSide vertex := by
    intro vertex hright hleft
    rcases hright with ⟨_hrightRetained, hrightComponent⟩
    rcases hleft with ⟨_hleftRetained, hleftComponent⟩
    apply hcomponents
    exact ConnectedComponent.eq_of_common_vertex
      hleftComponent hrightComponent
  have hsidesDisjoint' : ∀ vertex, leftSide vertex → ¬ rightSide vertex := by
    intro vertex hleft hright
    exact hsidesDisjoint vertex hright hleft
  have hleftCycle : HasCycleOnSide G leftSide := by
    exact retainedDeleteComponentSide_hasCycle hregular hcubic hcyclic
      cut hcard removed leftComponent
  have hrightCycle : HasCycleOnSide G rightSide := by
    exact retainedDeleteComponentSide_hasCycle hregular hcubic hcyclic
      cut hcard removed rightComponent
  let special := retainedDartAmbientEdge cut removed
  let ambientDart : G.Dart :=
    ⟨(removed.fst.1, removed.snd.1), removed.adj⟩
  have hambientEdge : graphData.toRotationSystem.edgeOf ambientDart =
      special := by
    apply Subtype.ext
    rfl
  have hreach := hambientFree ambientDart
  rw [hambientEdge,
    edgeDeletedPrimalGraph_toRotationSystem_eq graphData special] at hreach
  change (G.deleteEdges ({special.1} : Set (Sym2 V))).Reachable
    removed.fst.1 removed.snd.1 at hreach
  rcases hreach with ⟨avoidingWalk⟩
  let ambientWalk : G.Walk removed.fst.1 removed.snd.1 :=
    avoidingWalk.mapLe
      (G.deleteEdges_le ({special.1} : Set (Sym2 V)))
  have hambientEdges : ambientWalk.edges = avoidingWalk.edges :=
    avoidingWalk.edges_mapLe_eq_edges
      (G.deleteEdges_le ({special.1} : Set (Sym2 V)))
  have havoidsSpecial : special.1 ∉ ambientWalk.edges := by
    intro hmem
    have hdeleted := avoidingWalk.edges_subset_edgeSet
      (by simpa [hambientEdges] using hmem)
    simp at hdeleted
  rcases exists_edgeCrossesVertexSide_of_walk_endpoint_sides
      leftSide ambientWalk hleftRoot hrightNotLeft with
    ⟨leftPort, hleftPortWalk, hleftPortCross⟩
  have hleftPortNe : leftPort ≠ special := by
    intro heq
    apply havoidsSpecial
    simpa [heq] using hleftPortWalk
  have hleftPortCut : leftPort ∈ cut.edgeCut :=
    (retainedDeleteComponentSide_crossingEdge_mem
      cut removed leftComponent leftPort hleftPortCross).resolve_left
        hleftPortNe
  rcases exists_edgeCrossesVertexSide_of_walk_endpoint_sides
      rightSide ambientWalk.reverse hrightRoot hleftNotRight with
    ⟨rightPort, hrightPortWalkReverse, hrightPortCross⟩
  have hrightPortWalk : rightPort.1 ∈ ambientWalk.edges := by
    simpa using hrightPortWalkReverse
  have hrightPortNe : rightPort ≠ special := by
    intro heq
    apply havoidsSpecial
    simpa [heq] using hrightPortWalk
  have hrightPortCut : rightPort ∈ cut.edgeCut :=
    (retainedDeleteComponentSide_crossingEdge_mem
      cut removed rightComponent rightPort hrightPortCross).resolve_left
        hrightPortNe
  let leftBoundary :=
    retainedDeleteComponentEdgeCut cut removed leftComponent
  let rightBoundary :=
    retainedDeleteComponentEdgeCut cut removed rightComponent
  have hspecialNotCut : special ∉ cut.edgeCut :=
    retainedDartAmbientEdge_not_mem_cut cut removed
  have hspecialLeftCross : EdgeCrossesVertexSide G leftSide special := by
    refine ⟨removed.fst.1, removed.snd.1, ?_, ?_,
      hleftRoot, hrightNotLeft⟩
    · simp [special, retainedDartAmbientEdge]
    · simp [special, retainedDartAmbientEdge]
  have hspecialRightCross : EdgeCrossesVertexSide G rightSide special := by
    refine ⟨removed.snd.1, removed.fst.1, ?_, ?_,
      hrightRoot, hleftNotRight⟩
    · simp [special, retainedDartAmbientEdge]
    · simp [special, retainedDartAmbientEdge]
  have hspecialLeft : special ∈ leftBoundary :=
    (mem_retainedDeleteComponentEdgeCut_iff
      cut removed leftComponent special).2 hspecialLeftCross
  have hspecialRight : special ∈ rightBoundary :=
    (mem_retainedDeleteComponentEdgeCut_iff
      cut removed rightComponent special).2 hspecialRightCross
  have hleftBoundarySubset :
      leftBoundary ⊆ (insert special cut.edgeCut).erase rightPort := by
    intro edge hedge
    have hcross := (mem_retainedDeleteComponentEdgeCut_iff
      cut removed leftComponent edge).1 hedge
    have hclassified := retainedDeleteComponentSide_crossingEdge_mem
      cut removed leftComponent edge hcross
    have hinsert : edge ∈ insert special cut.edgeCut := by
      rcases hclassified with hedgeSpecial | hedgeCut
      · exact Finset.mem_insert.mpr (Or.inl hedgeSpecial)
      · simp [hedgeCut]
    have hne : edge ≠ rightPort := by
      intro heq
      subst edge
      exact not_crosses_distinct_retainedDeleteComponents
        cut removed hcomponents rightPort hrightPortCut
        hcross hrightPortCross
    exact Finset.mem_erase.mpr ⟨hne, hinsert⟩
  have hrightBoundarySubset :
      rightBoundary ⊆ (insert special cut.edgeCut).erase leftPort := by
    intro edge hedge
    have hcross := (mem_retainedDeleteComponentEdgeCut_iff
      cut removed rightComponent edge).1 hedge
    have hclassified := retainedDeleteComponentSide_crossingEdge_mem
      cut removed rightComponent edge hcross
    have hinsert : edge ∈ insert special cut.edgeCut := by
      rcases hclassified with hedgeSpecial | hedgeCut
      · exact Finset.mem_insert.mpr (Or.inl hedgeSpecial)
      · simp [hedgeCut]
    have hne : edge ≠ leftPort := by
      intro heq
      subst edge
      exact not_crosses_distinct_retainedDeleteComponents
        cut removed hcomponents leftPort hleftPortCut
        hleftPortCross hcross
    exact Finset.mem_erase.mpr ⟨hne, hinsert⟩
  have hinsertCard : (insert special cut.edgeCut).card = 5 := by
    simp [hspecialNotCut, hcard]
  have hrightPortInsert : rightPort ∈ insert special cut.edgeCut := by
    simp [hrightPortCut]
  have hleftPortInsert : leftPort ∈ insert special cut.edgeCut := by
    simp [hleftPortCut]
  have hleftBoundaryCard : leftBoundary.card ≤ 4 := by
    have hle := Finset.card_le_card hleftBoundarySubset
    rw [Finset.card_erase_of_mem hrightPortInsert, hinsertCard] at hle
    exact hle
  have hrightBoundaryCard : rightBoundary.card ≤ 4 := by
    have hle := Finset.card_le_card hrightBoundarySubset
    rw [Finset.card_erase_of_mem hleftPortInsert, hinsertCard] at hle
    exact hle
  let leftCyclicCut : SmallCyclicEdgeCut G :=
    { edgeCut := leftBoundary
      side := leftSide
      hcut_eq := fun edge =>
        mem_retainedDeleteComponentEdgeCut_iff
          cut removed leftComponent edge
      hcard_le_four := hleftBoundaryCard
      hinside_cycle := hleftCycle
      houtside_cycle := HasCycleOnSide.mono hsidesDisjoint hrightCycle }
  let rightCyclicCut : SmallCyclicEdgeCut G :=
    { edgeCut := rightBoundary
      side := rightSide
      hcut_eq := fun edge =>
        mem_retainedDeleteComponentEdgeCut_iff
          cut removed rightComponent edge
      hcard_le_four := hrightBoundaryCard
      hinside_cycle := hrightCycle
      houtside_cycle := HasCycleOnSide.mono hsidesDisjoint' hleftCycle }
  have hleftMinimum : 4 ≤ leftBoundary.card := by
    exact hcyclic leftCyclicCut
  have hrightMinimum : 4 ≤ rightBoundary.card := by
    exact hcyclic rightCyclicCut
  let leftPorts := leftBoundary.erase special
  let rightPorts := rightBoundary.erase special
  have hleftPortsSubset : leftPorts ⊆ cut.edgeCut := by
    intro edge hedge
    have hedgeBoundary := (Finset.mem_erase.mp hedge).2
    have hedgeNe := (Finset.mem_erase.mp hedge).1
    have hcross := (mem_retainedDeleteComponentEdgeCut_iff
      cut removed leftComponent edge).1 hedgeBoundary
    exact (retainedDeleteComponentSide_crossingEdge_mem
      cut removed leftComponent edge hcross).resolve_left hedgeNe
  have hrightPortsSubset : rightPorts ⊆ cut.edgeCut := by
    intro edge hedge
    have hedgeBoundary := (Finset.mem_erase.mp hedge).2
    have hedgeNe := (Finset.mem_erase.mp hedge).1
    have hcross := (mem_retainedDeleteComponentEdgeCut_iff
      cut removed rightComponent edge).1 hedgeBoundary
    exact (retainedDeleteComponentSide_crossingEdge_mem
      cut removed rightComponent edge hcross).resolve_left hedgeNe
  have hportsDisjoint : Disjoint leftPorts rightPorts := by
    rw [Finset.disjoint_left]
    intro edge hleft hright
    have hleftCross := (mem_retainedDeleteComponentEdgeCut_iff
      cut removed leftComponent edge).1 (Finset.mem_erase.mp hleft).2
    have hrightCross := (mem_retainedDeleteComponentEdgeCut_iff
      cut removed rightComponent edge).1 (Finset.mem_erase.mp hright).2
    exact not_crosses_distinct_retainedDeleteComponents
      cut removed hcomponents edge (hleftPortsSubset hleft)
      hleftCross hrightCross
  have hleftPortsCard : 3 ≤ leftPorts.card := by
    have herase := Finset.card_erase_of_mem hspecialLeft
    change (leftBoundary.erase special).card =
      leftBoundary.card - 1 at herase
    change 3 ≤ (leftBoundary.erase special).card
    omega
  have hrightPortsCard : 3 ≤ rightPorts.card := by
    have herase := Finset.card_erase_of_mem hspecialRight
    change (rightBoundary.erase special).card =
      rightBoundary.card - 1 at herase
    change 3 ≤ (rightBoundary.erase special).card
    omega
  have hunionSubset : leftPorts ∪ rightPorts ⊆ cut.edgeCut :=
    Finset.union_subset hleftPortsSubset hrightPortsSubset
  have hunionCard := Finset.card_le_card hunionSubset
  rw [Finset.card_union_of_disjoint hportsDisjoint, hcard] at hunionCard
  omega

namespace FourCutPlanarClosureData

variable {E : Type*} [Fintype E] [DecidableEq E]
  {RS : RotationSystem V E} {deleted : Finset V}
  (data : FourCutPlanarClosureData RS deleted)

/-- The output seam edge at one of the two matched positions. -/
def seamEdge (step : Fin 2) :=
  orderedCutSeamSpliceEdge RS (deletedRegionKeep deleted)
    data.interface.leftCrossing data.interface.rightCrossing
    data.leftCrosses data.rightCrosses
    data.interface.left_injective data.interface.right_injective
    data.boundaryCover data.interface.disjoint data.outer_retained
    data.seamEndpoints step

/-- The left-oriented output dart of a named closure seam. -/
def leftSeamDart (step : Fin 2) : data.closureRotationSystem.D :=
  Sum.inr (Sum.inl
    (orderedBoundaryDart RS (deletedRegionKeep deleted)
      data.interface.leftCrossing data.leftCrosses step))

/-- The right-oriented output dart of a named closure seam. -/
def rightSeamDart (step : Fin 2) : data.closureRotationSystem.D :=
  Sum.inr (Sum.inr
    (orderedBoundaryDart RS (deletedRegionKeep deleted)
      data.interface.rightCrossing data.rightCrosses step))

@[simp]
theorem closureRotationSystem_edgeOf_leftSeamDart (step : Fin 2) :
    data.closureRotationSystem.edgeOf (leftSeamDart data step) =
      seamEdge data step :=
  rfl

@[simp]
theorem closureRotationSystem_alpha_leftSeamDart (step : Fin 2) :
    data.closureRotationSystem.alpha (leftSeamDart data step) =
      rightSeamDart data step := by
  unfold GoertzelV24FourEdgeCutPlanarClosures.FourCutPlanarClosureData.closureRotationSystem
    leftSeamDart rightSeamDart
  rw [orderedCutRetainedVertexRotationSystem_alpha_left,
    orderedCutSeamMatching_apply]

@[simp]
theorem closureRotationSystem_alpha_rightSeamDart (step : Fin 2) :
    data.closureRotationSystem.alpha (rightSeamDart data step) =
      leftSeamDart data step := by
  rw [← closureRotationSystem_alpha_leftSeamDart data step]
  exact data.closureRotationSystem.alpha_involutive _

@[simp]
theorem closureRotationSystem_edgeOf_rightSeamDart (step : Fin 2) :
    data.closureRotationSystem.edgeOf (rightSeamDart data step) =
      seamEdge data step := by
  rw [← closureRotationSystem_alpha_leftSeamDart data step,
    data.closureRotationSystem.edge_alpha]
  rfl

@[simp]
theorem closureRotationSystem_vertOf_leftSeamDart (step : Fin 2) :
    data.closureRotationSystem.vertOf (leftSeamDart data step) =
      orderedBoundaryRetainedVertex RS (deletedRegionKeep deleted)
        data.interface.leftCrossing data.leftCrosses step := by
  apply Subtype.ext
  rfl

@[simp]
theorem closureRotationSystem_vertOf_rightSeamDart (step : Fin 2) :
    data.closureRotationSystem.vertOf (rightSeamDart data step) =
      orderedBoundaryRetainedVertex RS (deletedRegionKeep deleted)
        data.interface.rightCrossing data.rightCrosses step := by
  apply Subtype.ext
  rfl

/-- Distinct old edge identifiers remain distinct after the four-cut
closure splice. -/
theorem closureRotationSystem_edgeOf_internal_ne_of_edgeOf_ne
    (left right : InternalDart RS (deletedRegionKeep deleted))
    (hne : RS.edgeOf left.1.1 ≠ RS.edgeOf right.1.1) :
    data.closureRotationSystem.edgeOf (Sum.inl left) ≠
      data.closureRotationSystem.edgeOf (Sum.inl right) := by
  intro hedges
  apply hne
  exact (retainedInternalSpliceEdge_eq_iff RS
    (deletedRegionKeep deleted)
    data.interface.leftCrossing data.interface.rightCrossing
    data.leftCrosses data.rightCrosses
    data.interface.left_injective data.interface.right_injective
    data.boundaryCover data.interface.disjoint data.outer_retained
    data.seamEndpoints left right).1 hedges

/-- Every old retained adjacency survives deletion of an unrelated seam
edge in the closure. -/
theorem retainedAdj_edgeDeleted_seam
    (step : Fin 2) {left right : RetainedVertex
      (deletedRegionKeep deleted)}
    (hadj : (retainedAmbientPrimalGraph RS
      (deletedRegionKeep deleted)).Adj left right) :
    (edgeDeletedPrimalGraph data.closureRotationSystem
      (seamEdge data step)).Adj left right := by
  have hvertices : left ≠ right := hadj.ne
  change (rotationPrimalGraph RS).Adj left.1 right.1 at hadj
  rcases hadj with ⟨dart, hleft, hright⟩
  let internal : InternalDart RS (deletedRegionKeep deleted) :=
    ⟨⟨dart, by simpa [hleft] using left.2⟩,
      by simpa [hright] using right.2⟩
  let internalEdge := retainedInternalSpliceEdge RS
    (deletedRegionKeep deleted)
    data.interface.leftCrossing data.interface.rightCrossing
    data.leftCrosses data.rightCrosses
    data.interface.left_injective data.interface.right_injective
    data.boundaryCover data.interface.disjoint data.outer_retained
    data.seamEndpoints internal
  apply
    GoertzelV24AdjacentPairBoundary.AdjacentPairData.edgeDeletedPrimalGraph_adj_of_mem_endpoints
      data.closureRotationSystem (edge := internalEdge)
  · exact retainedInternalSpliceEdge_ne_orderedCutSeamSpliceEdge
      RS (deletedRegionKeep deleted)
      data.interface.leftCrossing data.interface.rightCrossing
      data.leftCrosses data.rightCrosses
      data.interface.left_injective data.interface.right_injective
      data.boundaryCover data.interface.disjoint data.outer_retained
      data.seamEndpoints internal step
  · unfold internalEdge
    unfold GoertzelV24FourEdgeCutPlanarClosures.FourCutPlanarClosureData.closureRotationSystem
    rw [endpoints_retainedInternalSpliceEdge]
    simp [retainedInternalEndpointPair, internal, hleft]
  · unfold internalEdge
    unfold GoertzelV24FourEdgeCutPlanarClosures.FourCutPlanarClosureData.closureRotationSystem
    rw [endpoints_retainedInternalSpliceEdge]
    simp [retainedInternalEndpointPair, internal, hright]
  · exact hvertices

/-- Connectedness of the retained induced graph supplies an old-edge path
around every new seam. -/
theorem seamEndpoints_reachable_without_seam
    (hretained : (retainedAmbientPrimalGraph RS
      (deletedRegionKeep deleted)).Connected)
    (step : Fin 2) :
    (edgeDeletedPrimalGraph data.closureRotationSystem
      (seamEdge data step)).Reachable
      (orderedBoundaryRetainedVertex RS (deletedRegionKeep deleted)
        data.interface.leftCrossing data.leftCrosses step)
      (orderedBoundaryRetainedVertex RS (deletedRegionKeep deleted)
        data.interface.rightCrossing data.rightCrosses step) := by
  exact hretained.mono (fun _ _ hadj =>
    retainedAdj_edgeDeleted_seam data step hadj) _ _

end FourCutPlanarClosureData

section ExactCutClosure

/-- Identify a vertex of the complement-side induced graph with the same
vertex in the retained carrier used by an exact-cut closure. -/
def retainedClosureVertex
    (cut : SmallCyclicEdgeCut G)
    (vertex : {vertex : V // ¬ cut.side vertex}) :
    RetainedVertex (deletedRegionKeep (cyclicCutVertexSide cut)) :=
  ⟨vertex.1, by
    simpa [deletedRegionKeep, mem_cyclicCutVertexSide_iff] using vertex.2⟩

@[simp]
theorem retainedClosureVertex_val
    (cut : SmallCyclicEdgeCut G)
    (vertex : {vertex : V // ¬ cut.side vertex}) :
    (retainedClosureVertex cut vertex).1 = vertex.1 :=
  rfl

/-- An old internal dart of a rooted exact-cut closure is the same oriented
edge in the complement-side induced graph. -/
def retainedCutDartOfInternal
    (graphData : Data G)
    (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (internal : InternalDart
      (cyclicData.rootedGraphData graphData).toRotationSystem
      (deletedRegionKeep (cyclicCutVertexSide cut))) :
    (retainedCutGraph G cut).Dart :=
  ⟨(⟨internal.1.1.fst, by
      simpa [deletedRegionKeep, mem_cyclicCutVertexSide_iff] using
        internal.1.2⟩,
    ⟨internal.1.1.snd, by
      simpa [deletedRegionKeep, mem_cyclicCutVertexSide_iff] using
        internal.2⟩),
    internal.1.1.adj⟩

@[simp]
theorem retainedCutDartOfInternal_fst
    (graphData : Data G)
    (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (internal : InternalDart
      (cyclicData.rootedGraphData graphData).toRotationSystem
      (deletedRegionKeep (cyclicCutVertexSide cut))) :
    (retainedCutDartOfInternal graphData cut cyclicData internal).fst.1 =
      internal.1.1.fst :=
  rfl

@[simp]
theorem retainedCutDartOfInternal_snd
    (graphData : Data G)
    (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (internal : InternalDart
      (cyclicData.rootedGraphData graphData).toRotationSystem
      (deletedRegionKeep (cyclicCutVertexSide cut))) :
    (retainedCutDartOfInternal graphData cut cyclicData internal).snd.1 =
      internal.1.1.snd :=
  rfl

/-- An adjacency in the complement-side induced graph avoiding one old
edge transports to an adjacency of the closure avoiding the corresponding
internal output edge. -/
theorem retainedCutDeleteAdj_mapsToClosure
    (graphData : Data G)
    (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (closure : FourCutPlanarClosureData
      (cyclicData.rootedGraphData graphData).toRotationSystem
      (cyclicCutVertexSide cut))
    (removed : InternalDart
      (cyclicData.rootedGraphData graphData).toRotationSystem
      (deletedRegionKeep (cyclicCutVertexSide cut)))
    {left right : {vertex : V // ¬ cut.side vertex}}
    (hadj : ((retainedCutGraph G cut).deleteEdges
      {(retainedCutDartOfInternal graphData cut cyclicData removed).edge}).Adj
        left right) :
    (edgeDeletedPrimalGraph closure.closureRotationSystem
      (closure.closureRotationSystem.edgeOf (Sum.inl removed))).Adj
      (retainedClosureVertex cut left)
      (retainedClosureVertex cut right) := by
  rcases SimpleGraph.deleteEdges_adj.mp hadj with
    ⟨hambient, hnotRemoved⟩
  let dart : G.Dart := ⟨(left.1, right.1), hambient⟩
  let internal : InternalDart
      (cyclicData.rootedGraphData graphData).toRotationSystem
      (deletedRegionKeep (cyclicCutVertexSide cut)) :=
    ⟨⟨dart, by
        simpa [dart, deletedRegionKeep,
          mem_cyclicCutVertexSide_iff] using left.2⟩,
      by
        simpa [dart, deletedRegionKeep,
          mem_cyclicCutVertexSide_iff] using right.2⟩
  refine ⟨Sum.inl internal, ?_, ?_, ?_⟩
  · apply FourCutPlanarClosureData.closureRotationSystem_edgeOf_internal_ne_of_edgeOf_ne
      closure internal removed
    intro hedges
    apply hnotRemoved
    rw [Set.mem_singleton_iff]
    apply Sym2.map.injective Subtype.val_injective
    have hvalues := congrArg Subtype.val hedges
    simpa [dart, internal, retainedCutDartOfInternal,
      SimpleGraph.Dart.edge, Sym2.map_mk] using hvalues
  · apply Subtype.ext
    rfl
  · apply Subtype.ext
    rfl

/-- Bridge-freedom of the complement-side induced graph transports an
avoiding path for every old internal closure edge. -/
theorem retainedInternalEndpoints_reachable_without_edge
    (graphData : Data G)
    (hregular : G.IsRegularOfDegree 3)
    (hcubic : ∀ vertex, (incidentEdgeFinset G vertex).card = 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (hambientFree : EdgeBridgeFree graphData.toRotationSystem)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (closure : FourCutPlanarClosureData
      (cyclicData.rootedGraphData graphData).toRotationSystem
      (cyclicCutVertexSide cut))
    (removed : InternalDart
      (cyclicData.rootedGraphData graphData).toRotationSystem
      (deletedRegionKeep (cyclicCutVertexSide cut))) :
    (edgeDeletedPrimalGraph closure.closureRotationSystem
      (closure.closureRotationSystem.edgeOf (Sum.inl removed))).Reachable
      (retainedClosureVertex cut
        (retainedCutDartOfInternal graphData cut cyclicData removed).fst)
      (retainedClosureVertex cut
        (retainedCutDartOfInternal graphData cut cyclicData removed).snd) := by
  let sourceRemoved :=
    retainedCutDartOfInternal graphData cut cyclicData removed
  have hsource := retainedCutGraph_edgeBridgeFree graphData hregular
    hcubic hcyclic cut hcard hambientFree sourceRemoved
  exact reachable_map_of_adj_eq_or_adj
    (retainedClosureVertex cut)
    (fun {_ _} hadj ↦ Or.inr
      (retainedCutDeleteAdj_mapsToClosure graphData cut cyclicData
        closure removed hadj)) hsource

/-- Either noncrossing planar closure of an exact cyclic four-cut is
bridge-free. Old edges use bridge-freedom of the retained induced side;
new seams use its connectedness. -/
theorem rootedPlanarClosure_edgeBridgeFree
    (graphData : Data G)
    (hregular : G.IsRegularOfDegree 3)
    (hcubic : ∀ vertex, (incidentEdgeFinset G vertex).card = 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (hconnected : G.Connected)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (side : SquareReductionSide)
    (hambientFree : EdgeBridgeFree graphData.toRotationSystem) :
    EdgeBridgeFree
      (rootedPlanarClosureData graphData hcubic hcyclic cut hcard
        cyclicData side).closureRotationSystem := by
  let closure := rootedPlanarClosureData graphData hcubic hcyclic
    cut hcard cyclicData side
  change EdgeBridgeFree closure.closureRotationSystem
  have hsides := induce_both_sides_connected_of_card_eq_four
    hconnected hcyclic cut hcard
  have hretained :
      (retainedAmbientPrimalGraph
        (cyclicData.rootedGraphData graphData).toRotationSystem
        (deletedRegionKeep (cyclicCutVertexSide cut))).Connected := by
    have hkeep : {vertex : V |
        deletedRegionKeep (cyclicCutVertexSide cut) vertex} =
        {vertex : V | ¬ cut.side vertex} := by
      ext vertex
      simp only [Set.mem_setOf_eq, deletedRegionKeep]
      rw [mem_cyclicCutVertexSide_iff]
    change ((rotationPrimalGraph
      (cyclicData.rootedGraphData graphData).toRotationSystem).induce
        {vertex : V |
          deletedRegionKeep (cyclicCutVertexSide cut) vertex}).Connected
    rw [rotationPrimalGraph_toRotationSystem_eq, hkeep]
    exact hsides.2
  intro dart
  rcases dart with internal | boundary
  · have hreach := retainedInternalEndpoints_reachable_without_edge
      graphData hregular hcubic hcyclic cut hcard hambientFree cyclicData
      closure internal
    have hleft : closure.closureRotationSystem.vertOf (Sum.inl internal) =
        retainedClosureVertex cut
          (retainedCutDartOfInternal graphData cut cyclicData internal).fst := by
      apply Subtype.ext
      rfl
    have hright : closure.closureRotationSystem.vertOf
          (closure.closureRotationSystem.alpha (Sum.inl internal)) =
        retainedClosureVertex cut
          (retainedCutDartOfInternal graphData cut cyclicData internal).snd := by
      apply Subtype.ext
      rfl
    rw [hleft, hright]
    exact hreach
  · rcases boundary with leftDart | rightDart
    · rcases orderedBoundaryDart_surjective
          (cyclicData.rootedGraphData graphData).toRotationSystem
          (deletedRegionKeep (cyclicCutVertexSide cut))
          closure.interface.leftCrossing closure.leftCrosses leftDart with
        ⟨step, rfl⟩
      have hreach := FourCutPlanarClosureData.seamEndpoints_reachable_without_seam
        closure hretained step
      change (edgeDeletedPrimalGraph closure.closureRotationSystem
        (closure.closureRotationSystem.edgeOf
          (FourCutPlanarClosureData.leftSeamDart closure step))).Reachable
        (closure.closureRotationSystem.vertOf
          (FourCutPlanarClosureData.leftSeamDart closure step))
        (closure.closureRotationSystem.vertOf
          (closure.closureRotationSystem.alpha
            (FourCutPlanarClosureData.leftSeamDart closure step)))
      simpa only [FourCutPlanarClosureData.closureRotationSystem_edgeOf_leftSeamDart,
        FourCutPlanarClosureData.closureRotationSystem_vertOf_leftSeamDart,
        FourCutPlanarClosureData.closureRotationSystem_alpha_leftSeamDart,
        FourCutPlanarClosureData.closureRotationSystem_vertOf_rightSeamDart]
        using hreach
    · rcases orderedBoundaryDart_surjective
          (cyclicData.rootedGraphData graphData).toRotationSystem
          (deletedRegionKeep (cyclicCutVertexSide cut))
          closure.interface.rightCrossing closure.rightCrosses rightDart with
        ⟨step, rfl⟩
      have hreach := FourCutPlanarClosureData.seamEndpoints_reachable_without_seam
        closure hretained step
      change (edgeDeletedPrimalGraph closure.closureRotationSystem
        (closure.closureRotationSystem.edgeOf
          (FourCutPlanarClosureData.rightSeamDart closure step))).Reachable
        (closure.closureRotationSystem.vertOf
          (FourCutPlanarClosureData.rightSeamDart closure step))
        (closure.closureRotationSystem.vertOf
          (closure.closureRotationSystem.alpha
            (FourCutPlanarClosureData.rightSeamDart closure step)))
      simpa only [FourCutPlanarClosureData.closureRotationSystem_edgeOf_rightSeamDart,
        FourCutPlanarClosureData.closureRotationSystem_vertOf_rightSeamDart,
        FourCutPlanarClosureData.closureRotationSystem_alpha_rightSeamDart,
        FourCutPlanarClosureData.closureRotationSystem_vertOf_leftSeamDart]
        using hreach.symm

/-- Vertex minimality colors both noncrossing planar closures of every
exact cyclic four-cut. All closure hypotheses, including bridge-freedom,
are consequences of the ambient minimal counterexample. -/
theorem rootedPlanarClosure_taitColorable
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (side : SquareReductionSide) :
    let hcubic : ∀ vertex : V,
        (incidentEdgeFinset G vertex).card = 3 := fun vertex => by
      rw [GoertzelV24DeletedEdgeTrail.incidentEdgeFinset_card_eq_degree]
      exact (graphData.toRotationSystem_isCubic_iff.mp
        minimal.spherical.cubic) vertex
    let hcyclic :=
      cyclicEdgeConnectivityAtLeast_four_of_vertexMinimalTaitCounterexample
        graphData minimal
    let closure := rootedPlanarClosureData graphData hcubic hcyclic
      cut hcard cyclicData side
    RotationSystemTaitColorable closure.closureRotationSystem := by
  dsimp only
  let hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 := fun vertex => by
    rw [GoertzelV24DeletedEdgeTrail.incidentEdgeFinset_card_eq_degree]
    exact (graphData.toRotationSystem_isCubic_iff.mp
      minimal.spherical.cubic) vertex
  let hcyclic :=
    cyclicEdgeConnectivityAtLeast_four_of_vertexMinimalTaitCounterexample
      graphData minimal
  have hregular : G.IsRegularOfDegree 3 := fun vertex => by
    have hmap :
        (incidentEdgeFinset G vertex).map
            (Function.Embedding.subtype
              (fun edge : Sym2 V => edge ∈ G.edgeSet)) =
          G.incidenceFinset vertex := by
      rw [SimpleGraph.incidenceFinset_eq_filter]
      ext edge
      simp [incidentEdgeFinset, and_comm]
    calc
      G.degree vertex = (G.incidenceFinset vertex).card := by simp
      _ = ((incidentEdgeFinset G vertex).map
          (Function.Embedding.subtype
            (fun edge : Sym2 V => edge ∈ G.edgeSet))).card := by rw [hmap]
      _ = (incidentEdgeFinset G vertex).card := by simp
      _ = 3 := hcubic vertex
  have hconnected : G.Connected := by
    rw [← rotationPrimalGraph_toRotationSystem_eq G graphData]
    exact minimal.primalConnected
  have hbridgeFree := rootedPlanarClosure_edgeBridgeFree graphData
    hregular hcubic hcyclic hconnected cut hcard cyclicData side
    minimal.edgeBridgeFree
  exact rootedPlanarClosure_taitColorable_of_edgeBridgeFree graphData
    minimal cut hcard cyclicData side hbridgeFree

end ExactCutClosure

end

end GoertzelV24FourEdgeCutRetainedBridge

end Mettapedia.GraphTheory.FourColor
