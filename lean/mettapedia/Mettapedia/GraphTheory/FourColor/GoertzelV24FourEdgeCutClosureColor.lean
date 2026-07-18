import Mettapedia.GraphTheory.FourColor.GoertzelV24FourEdgeCutBoundaryData
import Mettapedia.GraphTheory.FourColor.GoertzelV24FourEdgeCutRetainedBridge

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FourEdgeCutClosureColor

open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FourDefectBoundary
open GoertzelV24FourEdgeCutBoundaryData
open GoertzelV24FourEdgeCutBoundaryOrder
open GoertzelV24FourEdgeCutNoncrossingInterfaces
open GoertzelV24FourEdgeCutPlanarClosures
open GoertzelV24FourEdgeCutRetainedBridge
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open GoertzelV24RetainedSpliceEdgeDecomposition
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24ThreeEdgeCutMinimality
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- A cyclic boundary coordinate regarded as the corresponding member of
the exact four-edge cut. -/
def commonCutEdge
    (graphData : Data G)
    (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (port : Fin 4) : cut.compl.edgeCut :=
  ⟨boundaryCrossing graphData.toRotationSystem
      (cyclicCutVertexSide cut) cyclicData.boundaryOrder port,
    by
      change boundaryCrossing graphData.toRotationSystem
          (cyclicCutVertexSide cut) cyclicData.boundaryOrder port ∈
        cut.edgeCut
      rw [← vertexSetCrossingEdges_cyclicCutVertexSide graphData cut]
      exact boundaryDart_edge_mem_vertexSetCrossingEdges
        graphData.toRotationSystem (cyclicCutVertexSide cut)
          (cyclicData.boundaryOrder port)⟩

@[simp]
theorem commonCutEdge_val
    (graphData : Data G)
    (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (port : Fin 4) :
    (commonCutEdge graphData cut cyclicData port).1 =
      boundaryCrossing graphData.toRotationSystem
        (cyclicCutVertexSide cut) cyclicData.boundaryOrder port :=
  rfl

/-- The common cyclic coordinates enumerate the exact cut edges
bijectively. -/
theorem commonCutEdge_bijective
    (graphData : Data G)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut)) :
    Function.Bijective (commonCutEdge graphData cut cyclicData) := by
  apply (Fintype.bijective_iff_injective_and_card
    (commonCutEdge graphData cut cyclicData)).2
  refine ⟨?_, ?_⟩
  · intro first second heq
    apply boundaryCrossing_injective graphData.toRotationSystem
      (cyclicCutVertexSide cut) cyclicData.boundaryOrder
    exact congrArg Subtype.val heq
  · simpa using hcard.symm

/-- Translate the common cyclic boundary coordinates to the arbitrary
finite enumeration used by the generic exact-cut boundary package. -/
def commonPortReindex
    (graphData : Data G)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut)) : Equiv.Perm (Fin 4) :=
  (Equiv.ofBijective (commonCutEdge graphData cut cyclicData)
      (commonCutEdge_bijective graphData cut hcard cyclicData)).trans
    (Fintype.equivFinOfCardEq (by simpa using hcard) :
      cut.compl.edgeCut ≃ Fin 4)

/-- The generic cut enumeration at the translated coordinate is the
actual edge named by the common cyclic boundary coordinate. -/
theorem cyclicCutCrossingOfCardFour_commonPortReindex
    (graphData : Data G)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut)) (port : Fin 4) :
    cyclicCutCrossingOfCardFour cut.compl (by simpa using hcard)
        (commonPortReindex graphData cut hcard cyclicData port) =
      boundaryCrossing graphData.toRotationSystem
        (cyclicCutVertexSide cut) cyclicData.boundaryOrder port := by
  let edgeEquiv : cut.compl.edgeCut ≃ Fin 4 :=
    Fintype.equivFinOfCardEq (by simpa using hcard)
  have hsubtype :
      edgeEquiv.symm
          (commonPortReindex graphData cut hcard cyclicData port) =
        commonCutEdge graphData cut cyclicData port := by
    apply edgeEquiv.injective
    change edgeEquiv
        (edgeEquiv.symm
          (edgeEquiv (commonCutEdge graphData cut cyclicData port))) =
      edgeEquiv (commonCutEdge graphData cut cyclicData port)
    rw [edgeEquiv.apply_symm_apply]
  simpa [cyclicCutCrossingOfCardFour, edgeEquiv] using
    congrArg Subtype.val hsubtype

/-- The retained endpoint of an actual cyclic boundary dart, as a vertex
of the complement-side induced graph. -/
def commonRetainedPort
    (graphData : Data G)
    (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (port : Fin 4) : CyclicCutSideVertex cut.compl :=
  ⟨graphData.toRotationSystem.vertOf
      (cyclicData.boundaryOrder port).1.1,
    by
      change ¬ cut.side (graphData.toRotationSystem.vertOf
        (cyclicData.boundaryOrder port).1.1)
      simpa [deletedRegionKeep, mem_cyclicCutVertexSide_iff] using
        (cyclicData.boundaryOrder port).1.2⟩

@[simp]
theorem commonRetainedPort_val
    (graphData : Data G)
    (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (port : Fin 4) :
    (commonRetainedPort graphData cut cyclicData port).1 =
      graphData.toRotationSystem.vertOf
        (cyclicData.boundaryOrder port).1.1 :=
  rfl

/-- Common cyclic ports are the generic complement-side ports after the
explicit edge-coordinate translation. -/
theorem commonRetainedPort_eq_cyclicCutSidePort
    (graphData : Data G)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut)) (port : Fin 4) :
    commonRetainedPort graphData cut cyclicData port =
      cyclicCutSidePort cut.compl (by simpa using hcard)
        (commonPortReindex graphData cut hcard cyclicData port) := by
  let hcompCard : cut.compl.edgeCut.card = 4 := by simpa using hcard
  apply Subtype.ext
  let edge := boundaryCrossing graphData.toRotationSystem
    (cyclicCutVertexSide cut) cyclicData.boundaryOrder port
  have hedgeCut : edge ∈ cut.compl.edgeCut :=
    (commonCutEdge graphData cut cyclicData port).2
  have hcross : EdgeCrossesVertexSide G cut.compl.side edge :=
    (cut.compl.hcut_eq edge).1 hedgeCut
  apply side_endpoint_unique_of_crossing cut.compl.side edge hcross
  · have hrotationEndpoint :
        graphData.toRotationSystem.vertOf
            (cyclicData.boundaryOrder port).1.1 ∈
          graphData.toRotationSystem.endpoints edge := by
      apply graphData.toRotationSystem.mem_endpoints_iff.2
      exact ⟨(cyclicData.boundaryOrder port).1.1,
        graphData.toRotationSystem.mem_dartsOn.2 rfl, rfl⟩
    exact (mem_simpleGraphRotationSystem_endpoints_iff
      graphData edge _).1 hrotationEndpoint
  · have hmem := cyclicCutSideEndpoint_mem_edge cut.compl hcompCard
      (commonPortReindex graphData cut hcard cyclicData port)
    rw [cyclicCutCrossingOfCardFour_commonPortReindex
      graphData cut hcard cyclicData port] at hmem
    exact hmem
  · exact (commonRetainedPort graphData cut cyclicData port).2
  · exact cyclicCutSideEndpoint_side cut.compl
      hcompCard _

/-- The genuine complement-side degree-two boundary, in the common cyclic
coordinates supplied by the planar rotation system. -/
def commonRetainedBoundaryData
    (graphData : Data G)
    (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut)) :
    DegreeTwoBoundaryData (CyclicCutSideGraph cut.compl) 4 where
  defectVertex := commonRetainedPort graphData cut cyclicData

/-- The common-coordinate boundary is exactly a relabeling of the generic
exact-cut boundary. -/
theorem commonRetainedBoundaryData_eq_reindex
    (graphData : Data G)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut)) :
    commonRetainedBoundaryData graphData cut cyclicData =
      (cyclicCutSideDegreeTwoBoundaryData cut.compl
        (by simpa using hcard)).reindex
          (commonPortReindex graphData cut hcard cyclicData) := by
  change DegreeTwoBoundaryData.mk
      (commonRetainedPort graphData cut cyclicData) =
    DegreeTwoBoundaryData.mk
      (fun port ↦ cyclicCutSidePort cut.compl (by simpa using hcard)
        (commonPortReindex graphData cut hcard cyclicData port))
  apply congrArg DegreeTwoBoundaryData.mk
  funext port
  exact commonRetainedPort_eq_cyclicCutSidePort
    graphData cut hcard cyclicData port

/-- Hence the actual common-coordinate boundary is structurally
well-formed. -/
theorem commonRetainedBoundaryData_wellFormed
    (graphData : Data G)
    (hcubic : ∀ vertex, (incidentEdgeFinset G vertex).card = 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut)) :
    (commonRetainedBoundaryData graphData cut cyclicData).WellFormed := by
  rw [commonRetainedBoundaryData_eq_reindex
    graphData cut hcard cyclicData]
  exact (cyclicCutSideDegreeTwoBoundaryData_wellFormed
    hcubic hcyclic cut.compl (by simpa using hcard)).reindex _

/-- Embed an edge of the genuine complement-side induced graph back into
the ambient graph. -/
def retainedCutEdgeToAmbientEdge
    (cut : SmallCyclicEdgeCut G)
    (edge : (retainedCutGraph G cut).edgeSet) : G.edgeSet :=
  ⟨edge.1.map Subtype.val, by
    rcases edge with ⟨edge, hedge⟩
    induction edge using Sym2.inductionOn with
    | _ left right => exact hedge⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem retainedCutEdgeToAmbientEdge_val
    (cut : SmallCyclicEdgeCut G)
    (edge : (retainedCutGraph G cut).edgeSet) :
    (retainedCutEdgeToAmbientEdge cut edge).1 =
      edge.1.map Subtype.val :=
  rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Embedding retained induced edges into the ambient graph is injective. -/
theorem retainedCutEdgeToAmbientEdge_injective
    (cut : SmallCyclicEdgeCut G) :
    Function.Injective (retainedCutEdgeToAmbientEdge cut) := by
  intro first second heq
  apply Subtype.ext
  apply Sym2.map.injective Subtype.val_injective
  exact congrArg Subtype.val heq

/-- Select an oriented internal representative of a genuine retained-side
edge in the rooted rotation system used by either planar closure. -/
def retainedCutEdgeInternalDart
    (graphData : Data G)
    (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (edge : (retainedCutGraph G cut).edgeSet) :
    InternalDart
      (cyclicData.rootedGraphData graphData).toRotationSystem
      (deletedRegionKeep (cyclicCutVertexSide cut)) := by
  let rooted := cyclicData.rootedGraphData graphData
  let RS := rooted.toRotationSystem
  let ambient := retainedCutEdgeToAmbientEdge cut edge
  let dart := RS.dartRepresentative ambient
  have hdartEdge : RS.edgeOf dart = ambient :=
    RS.dartRepresentative_edgeOf ambient
  have endpointKeep : ∀ vertex : V,
      vertex ∈ (ambient.1 : Sym2 V) →
        deletedRegionKeep (cyclicCutVertexSide cut) vertex := by
    intro vertex hvertex
    have hmapped : vertex ∈ edge.1.map Subtype.val := by
      simpa [ambient] using hvertex
    rcases Sym2.mem_map.mp hmapped with
      ⟨retained, _hretained, hvalue⟩
    subst vertex
    exact (retainedClosureVertex cut retained).2
  refine ⟨⟨dart, endpointKeep _ ?_⟩, endpointKeep _ ?_⟩
  · apply (mem_simpleGraphRotationSystem_endpoints_iff
      rooted ambient _).1
    apply RS.mem_endpoints_iff.2
    exact ⟨dart, RS.mem_dartsOn.2 hdartEdge, rfl⟩
  · apply (mem_simpleGraphRotationSystem_endpoints_iff
      rooted ambient _).1
    apply RS.mem_endpoints_iff.2
    exact ⟨RS.alpha dart,
      RS.mem_dartsOn.2 (RS.edge_alpha dart |>.trans hdartEdge), rfl⟩

@[simp]
theorem retainedCutEdgeInternalDart_edgeOf
    (graphData : Data G)
    (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (edge : (retainedCutGraph G cut).edgeSet) :
    (cyclicData.rootedGraphData graphData).toRotationSystem.edgeOf
        (retainedCutEdgeInternalDart graphData cut cyclicData edge).1.1 =
      retainedCutEdgeToAmbientEdge cut edge := by
  simp only [retainedCutEdgeInternalDart]
  exact (cyclicData.rootedGraphData graphData).toRotationSystem
    |>.dartRepresentative_edgeOf _

/-- An unchanged retained-side edge as an internal edge of one planar
closure. -/
abbrev closureRewiredDartSystem
    (graphData : Data G)
    (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (closure : FourCutPlanarClosureData
      (cyclicData.rootedGraphData graphData).toRotationSystem
      (cyclicCutVertexSide cut)) :=
  orderedCutRetainedVertexRewiredDartSystem
    (cyclicData.rootedGraphData graphData).toRotationSystem
    (deletedRegionKeep (cyclicCutVertexSide cut))
    closure.interface.leftCrossing closure.interface.rightCrossing
    closure.leftCrosses closure.rightCrosses
    closure.interface.left_injective closure.interface.right_injective
    closure.boundaryCover closure.interface.disjoint closure.outer_retained
    closure.seamEndpoints

def closureEdgeOfRetainedEdge
    (graphData : Data G)
    (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (closure : FourCutPlanarClosureData
      (cyclicData.rootedGraphData graphData).toRotationSystem
      (cyclicCutVertexSide cut))
    (edge : (retainedCutGraph G cut).edgeSet) :
    (closureRewiredDartSystem graphData cut cyclicData closure).Edge :=
  retainedInternalSpliceEdge
    (cyclicData.rootedGraphData graphData).toRotationSystem
    (deletedRegionKeep (cyclicCutVertexSide cut))
    closure.interface.leftCrossing closure.interface.rightCrossing
    closure.leftCrosses closure.rightCrosses
    closure.interface.left_injective closure.interface.right_injective
    closure.boundaryCover closure.interface.disjoint closure.outer_retained
    closure.seamEndpoints
    (retainedCutEdgeInternalDart graphData cut cyclicData edge)

/-- Distinct genuine retained-side edges remain distinct in either planar
closure. -/
theorem closureEdgeOfRetainedEdge_injective
    (graphData : Data G)
    (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (closure : FourCutPlanarClosureData
      (cyclicData.rootedGraphData graphData).toRotationSystem
      (cyclicCutVertexSide cut)) :
    Function.Injective
      (closureEdgeOfRetainedEdge graphData cut cyclicData closure) := by
  intro first second hedges
  apply retainedCutEdgeToAmbientEdge_injective cut
  rw [← retainedCutEdgeInternalDart_edgeOf graphData cut cyclicData first,
    ← retainedCutEdgeInternalDart_edgeOf graphData cut cyclicData second]
  exact (retainedInternalSpliceEdge_eq_iff
    (cyclicData.rootedGraphData graphData).toRotationSystem
    (deletedRegionKeep (cyclicCutVertexSide cut))
    closure.interface.leftCrossing closure.interface.rightCrossing
    closure.leftCrosses closure.rightCrosses
    closure.interface.left_injective closure.interface.right_injective
    closure.boundaryCover closure.interface.disjoint closure.outer_retained
    closure.seamEndpoints
    (retainedCutEdgeInternalDart graphData cut cyclicData first)
    (retainedCutEdgeInternalDart graphData cut cyclicData second)).1 hedges

/-- Endpoint incidence of a genuine retained-side edge is preserved by its
internal image in either planar closure. -/
theorem retainedClosureVertex_mem_endpoints_closureEdge
    (graphData : Data G)
    (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (closure : FourCutPlanarClosureData
      (cyclicData.rootedGraphData graphData).toRotationSystem
      (cyclicCutVertexSide cut))
    (edge : (retainedCutGraph G cut).edgeSet)
    (vertex : {vertex : V // ¬ cut.side vertex})
    (hvertex : vertex ∈ (edge.1 : Sym2 _)) :
    retainedClosureVertex cut vertex ∈
      closure.closureRotationSystem.endpoints
        (closureEdgeOfRetainedEdge graphData cut cyclicData closure edge) := by
  unfold closureEdgeOfRetainedEdge
  unfold FourCutPlanarClosureData.closureRotationSystem
  rw [endpoints_retainedInternalSpliceEdge]
  have hambientSym : vertex.1 ∈
      ((retainedCutEdgeToAmbientEdge cut edge).1 : Sym2 V) := by
    change vertex.1 ∈ edge.1.map Subtype.val
    exact Sym2.mem_map.mpr ⟨vertex, hvertex, rfl⟩
  have hambientEndpoints : vertex.1 ∈
      (cyclicData.rootedGraphData graphData).toRotationSystem.endpoints
        ((cyclicData.rootedGraphData graphData).toRotationSystem.edgeOf
          (retainedCutEdgeInternalDart
            graphData cut cyclicData edge).1.1) := by
    rw [retainedCutEdgeInternalDart_edgeOf]
    exact (mem_simpleGraphRotationSystem_endpoints_iff
      (cyclicData.rootedGraphData graphData)
      (retainedCutEdgeToAmbientEdge cut edge) vertex.1).2 hambientSym
  have himage : vertex.1 ∈
      (retainedInternalEndpointPair
        (cyclicData.rootedGraphData graphData).toRotationSystem
        (deletedRegionKeep (cyclicCutVertexSide cut))
        (retainedCutEdgeInternalDart
          graphData cut cyclicData edge)).image Subtype.val := by
    rw [image_val_retainedInternalEndpointPair]
    exact hambientEndpoints
  rcases Finset.mem_image.mp himage with
    ⟨retained, hretained, hvalue⟩
  have heq : retained = retainedClosureVertex cut vertex := by
    apply Subtype.ext
    exact hvalue
  simpa [heq] using hretained

/-- Restrict a closure coloring to the unchanged edges of the genuine
complement-side induced graph. -/
def retainedCutColoring
    (graphData : Data G)
    (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (closure : FourCutPlanarClosureData
      (cyclicData.rootedGraphData graphData).toRotationSystem
      (cyclicCutVertexSide cut))
    (C : closure.closureRotationSystem.EdgeColoring Color) :
    (retainedCutGraph G cut).EdgeColoring Color :=
  SimpleGraph.Coloring.mk
    (fun edge ↦ C
      (closureEdgeOfRetainedEdge graphData cut cyclicData closure edge)) <| by
      intro first second hadjacent
      rcases (SimpleGraph.lineGraph_adj_iff_exists).1 hadjacent with
        ⟨hne, vertex, hfirst, hsecond⟩
      apply C.valid
      apply closure.closureRotationSystem.edgeAdjacencyGraph_adj_iff.2
      exact ⟨(closureEdgeOfRetainedEdge_injective
          graphData cut cyclicData closure).ne hne,
        retainedClosureVertex cut vertex,
        retainedClosureVertex_mem_endpoints_closureEdge
          graphData cut cyclicData closure first vertex hfirst,
        retainedClosureVertex_mem_endpoints_closureEdge
          graphData cut cyclicData closure second vertex hsecond⟩

@[simp]
theorem retainedCutColoring_apply
    (graphData : Data G)
    (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (closure : FourCutPlanarClosureData
      (cyclicData.rootedGraphData graphData).toRotationSystem
      (cyclicCutVertexSide cut))
    (C : closure.closureRotationSystem.EdgeColoring Color)
    (edge : (retainedCutGraph G cut).edgeSet) :
    retainedCutColoring graphData cut cyclicData closure C edge =
      C (closureEdgeOfRetainedEdge
        graphData cut cyclicData closure edge) :=
  rfl

/-- Nonzero closure colors remain nonzero after forgetting the seams. -/
theorem retainedCutColoring_isTait
    (graphData : Data G)
    (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (closure : FourCutPlanarClosureData
      (cyclicData.rootedGraphData graphData).toRotationSystem
      (cyclicCutVertexSide cut))
    (C : closure.closureRotationSystem.EdgeColoring Color)
    (hC : closure.closureRotationSystem.IsTaitEdgeColoring C) :
    IsTaitEdgeColoring (retainedCutGraph G cut)
      (retainedCutColoring graphData cut cyclicData closure C) := by
  intro edge
  exact hC (closureEdgeOfRetainedEdge
    graphData cut cyclicData closure edge)

/-- In the rooted `left` interface, the selected ordered boundary dart is
the boundary dart at the corresponding common cyclic port. -/
theorem rootedPlanarClosure_leftBoundaryDart
    (graphData : Data G)
    (hcubic : ∀ vertex, (incidentEdgeFinset G vertex).card = 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (side : SquareReductionSide) (step : Fin 2) :
    let closure := rootedPlanarClosureData graphData hcubic hcyclic
      cut hcard cyclicData side
    orderedBoundaryDart
        (cyclicData.rootedGraphData graphData).toRotationSystem
        (deletedRegionKeep (cyclicCutVertexSide cut))
        closure.interface.leftCrossing closure.leftCrosses step |>.1 =
      (cyclicData.rootedBoundaryData graphData).boundaryOrder
        (side.leftPort step) := by
  dsimp only
  apply boundaryDart_eq_of_edgeOf_eq
  rw [orderedBoundaryDart_edgeOf]
  rfl

/-- The analogous identity for the rooted `right` interface. -/
theorem rootedPlanarClosure_rightBoundaryDart
    (graphData : Data G)
    (hcubic : ∀ vertex, (incidentEdgeFinset G vertex).card = 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (side : SquareReductionSide) (step : Fin 2) :
    let closure := rootedPlanarClosureData graphData hcubic hcyclic
      cut hcard cyclicData side
    orderedBoundaryDart
        (cyclicData.rootedGraphData graphData).toRotationSystem
        (deletedRegionKeep (cyclicCutVertexSide cut))
        closure.interface.rightCrossing closure.rightCrosses step |>.1 =
      (cyclicData.rootedBoundaryData graphData).boundaryOrder
        (side.rightPort step) := by
  dsimp only
  apply boundaryDart_eq_of_edgeOf_eq
  rw [orderedBoundaryDart_edgeOf]
  rfl

/-- A common cyclic left port is an endpoint of its newly inserted planar
closure seam. -/
theorem commonRetainedPort_mem_endpoints_leftSeam
    (graphData : Data G)
    (hcubic : ∀ vertex, (incidentEdgeFinset G vertex).card = 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (side : SquareReductionSide) (step : Fin 2) :
    let closure := rootedPlanarClosureData graphData hcubic hcyclic
      cut hcard cyclicData side
    retainedClosureVertex cut
        (commonRetainedPort graphData cut cyclicData (side.leftPort step)) ∈
      closure.closureRotationSystem.endpoints
        (FourCutPlanarClosureData.seamEdge closure step) := by
  dsimp only
  let closure := rootedPlanarClosureData graphData hcubic hcyclic
    cut hcard cyclicData side
  change retainedClosureVertex cut
        (commonRetainedPort graphData cut cyclicData (side.leftPort step)) ∈
      closure.closureRotationSystem.endpoints
        (FourCutPlanarClosureData.seamEdge closure step)
  unfold FourCutPlanarClosureData.seamEdge
  unfold FourCutPlanarClosureData.closureRotationSystem
  rw [endpoints_orderedCutSeamSpliceEdge]
  apply Finset.mem_insert.mpr
  left
  apply Subtype.ext
  change graphData.toRotationSystem.vertOf
      (cyclicData.boundaryOrder (side.leftPort step)).1.1 =
    (cyclicData.rootedGraphData graphData).toRotationSystem.vertOf
      (orderedBoundaryDart
        (cyclicData.rootedGraphData graphData).toRotationSystem
        (deletedRegionKeep (cyclicCutVertexSide cut))
        closure.interface.leftCrossing closure.leftCrosses step).1.1.1
  rw [rootedPlanarClosure_leftBoundaryDart
    graphData hcubic hcyclic cut hcard cyclicData side step]
  rfl

/-- A common cyclic right port is the other endpoint of its newly inserted
planar closure seam. -/
theorem commonRetainedPort_mem_endpoints_rightSeam
    (graphData : Data G)
    (hcubic : ∀ vertex, (incidentEdgeFinset G vertex).card = 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (side : SquareReductionSide) (step : Fin 2) :
    let closure := rootedPlanarClosureData graphData hcubic hcyclic
      cut hcard cyclicData side
    retainedClosureVertex cut
        (commonRetainedPort graphData cut cyclicData (side.rightPort step)) ∈
      closure.closureRotationSystem.endpoints
        (FourCutPlanarClosureData.seamEdge closure step) := by
  dsimp only
  let closure := rootedPlanarClosureData graphData hcubic hcyclic
    cut hcard cyclicData side
  change retainedClosureVertex cut
        (commonRetainedPort graphData cut cyclicData (side.rightPort step)) ∈
      closure.closureRotationSystem.endpoints
        (FourCutPlanarClosureData.seamEdge closure step)
  unfold FourCutPlanarClosureData.seamEdge
  unfold FourCutPlanarClosureData.closureRotationSystem
  rw [endpoints_orderedCutSeamSpliceEdge]
  apply Finset.mem_insert.mpr
  right
  apply Finset.mem_singleton.mpr
  apply Subtype.ext
  change graphData.toRotationSystem.vertOf
      (cyclicData.boundaryOrder (side.rightPort step)).1.1 =
    (cyclicData.rootedGraphData graphData).toRotationSystem.vertOf
      (orderedBoundaryDart
        (cyclicData.rootedGraphData graphData).toRotationSystem
        (deletedRegionKeep (cyclicCutVertexSide cut))
        closure.interface.rightCrossing closure.rightCrosses step).1.1.1
  rw [rootedPlanarClosure_rightBoundaryDart
    graphData hcubic hcyclic cut hcard cyclicData side step]
  rfl

/-- No unchanged retained-side edge is one of the newly inserted closure
seams. -/
theorem closureEdgeOfRetainedEdge_ne_seamEdge
    (graphData : Data G)
    (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (closure : FourCutPlanarClosureData
      (cyclicData.rootedGraphData graphData).toRotationSystem
      (cyclicCutVertexSide cut))
    (edge : (retainedCutGraph G cut).edgeSet) (step : Fin 2) :
    closureEdgeOfRetainedEdge graphData cut cyclicData closure edge ≠
      FourCutPlanarClosureData.seamEdge closure step := by
  exact retainedInternalSpliceEdge_ne_orderedCutSeamSpliceEdge
    (cyclicData.rootedGraphData graphData).toRotationSystem
    (deletedRegionKeep (cyclicCutVertexSide cut))
    closure.interface.leftCrossing closure.interface.rightCrossing
    closure.leftCrosses closure.rightCrosses
    closure.interface.left_injective closure.interface.right_injective
    closure.boundaryCover closure.interface.disjoint closure.outer_retained
    closure.seamEndpoints
    (retainedCutEdgeInternalDart graphData cut cyclicData edge) step

/-- Among the three nonzero Klein-four colors, the color distinct from two
distinct given colors is their sum. -/
private theorem add_eq_of_three_nonzero_pairwise_distinct :
    ∀ first second third : Color,
      first ≠ 0 → second ≠ 0 → third ≠ 0 →
      first ≠ second → third ≠ first → third ≠ second →
      first + second = third := by
  decide

/-- At a genuine cut port incident with a new seam, the missing color of
the two retained edges is exactly the seam color. -/
theorem commonBoundaryColorWord_eq_seamColor_of_port
    (graphData : Data G)
    (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (hdata : (commonRetainedBoundaryData
      graphData cut cyclicData).WellFormed)
    (closure : FourCutPlanarClosureData
      (cyclicData.rootedGraphData graphData).toRotationSystem
      (cyclicCutVertexSide cut))
    (C : closure.closureRotationSystem.EdgeColoring Color)
    (hC : closure.closureRotationSystem.IsTaitEdgeColoring C)
    (port : Fin 4) (step : Fin 2)
    (hseamEndpoint : retainedClosureVertex cut
        (commonRetainedPort graphData cut cyclicData port) ∈
      closure.closureRotationSystem.endpoints
        (FourCutPlanarClosureData.seamEdge closure step)) :
    (commonRetainedBoundaryData graphData cut cyclicData).colorWord
        (retainedCutColoring graphData cut cyclicData closure C) port =
      C (FourCutPlanarClosureData.seamEdge closure step) := by
  let retained := retainedCutGraph G cut
  let retainedColoring :=
    retainedCutColoring graphData cut cyclicData closure C
  have hcard :
      (incidentEdgeFinset retained
        (commonRetainedPort graphData cut cyclicData port)).card = 2 := by
    exact hdata.2.1 port
  rcases Finset.card_eq_two.mp hcard with
    ⟨first, second, hne, hincident⟩
  have hfirstMem : first ∈ incidentEdgeFinset retained
      (commonRetainedPort graphData cut cyclicData port) := by
    rw [hincident]
    exact Finset.mem_insert_self first {second}
  have hsecondMem : second ∈ incidentEdgeFinset retained
      (commonRetainedPort graphData cut cyclicData port) := by
    rw [hincident]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self second)
  have hfirstEndpoint :
      commonRetainedPort graphData cut cyclicData port ∈
        (first.1 : Sym2 _) := by
    exact (Finset.mem_filter.mp hfirstMem).2
  have hsecondEndpoint :
      commonRetainedPort graphData cut cyclicData port ∈
        (second.1 : Sym2 _) := by
    exact (Finset.mem_filter.mp hsecondMem).2
  have hretainedTait : IsTaitEdgeColoring retained retainedColoring :=
    retainedCutColoring_isTait graphData cut cyclicData closure C hC
  have hfirstSecond : retainedColoring first ≠ retainedColoring second := by
    apply retainedColoring.valid
    apply (SimpleGraph.lineGraph_adj_iff_exists).2
    exact ⟨hne, commonRetainedPort graphData cut cyclicData port,
      hfirstEndpoint, hsecondEndpoint⟩
  have hseamFirst :
      C (FourCutPlanarClosureData.seamEdge closure step) ≠
        retainedColoring first := by
    change C (FourCutPlanarClosureData.seamEdge closure step) ≠
      C (closureEdgeOfRetainedEdge
        graphData cut cyclicData closure first)
    apply C.valid
    apply closure.closureRotationSystem.edgeAdjacencyGraph_adj_iff.2
    exact ⟨(closureEdgeOfRetainedEdge_ne_seamEdge
        graphData cut cyclicData closure first step).symm,
      retainedClosureVertex cut
        (commonRetainedPort graphData cut cyclicData port),
      hseamEndpoint,
      retainedClosureVertex_mem_endpoints_closureEdge
        graphData cut cyclicData closure first
          (commonRetainedPort graphData cut cyclicData port) hfirstEndpoint⟩
  have hseamSecond :
      C (FourCutPlanarClosureData.seamEdge closure step) ≠
        retainedColoring second := by
    change C (FourCutPlanarClosureData.seamEdge closure step) ≠
      C (closureEdgeOfRetainedEdge
        graphData cut cyclicData closure second)
    apply C.valid
    apply closure.closureRotationSystem.edgeAdjacencyGraph_adj_iff.2
    exact ⟨(closureEdgeOfRetainedEdge_ne_seamEdge
        graphData cut cyclicData closure second step).symm,
      retainedClosureVertex cut
        (commonRetainedPort graphData cut cyclicData port),
      hseamEndpoint,
      retainedClosureVertex_mem_endpoints_closureEdge
        graphData cut cyclicData closure second
          (commonRetainedPort graphData cut cyclicData port) hsecondEndpoint⟩
  have hsum : retainedColoring first + retainedColoring second =
      C (FourCutPlanarClosureData.seamEdge closure step) :=
    add_eq_of_three_nonzero_pairwise_distinct
      (retainedColoring first) (retainedColoring second)
      (C (FourCutPlanarClosureData.seamEdge closure step))
      (hretainedTait first) (hretainedTait second)
      (hC (FourCutPlanarClosureData.seamEdge closure step))
      hfirstSecond hseamFirst hseamSecond
  change vertexKirchhoffSum retained retainedColoring
      (commonRetainedPort graphData cut cyclicData port) = _
  unfold vertexKirchhoffSum
  rw [hincident]
  have hnot : first ∉ ({second} : Finset _) := by
    intro hmem
    exact hne (Finset.mem_singleton.mp hmem)
  rw [Finset.sum_insert hnot, Finset.sum_singleton]
  exact hsum

/-- The two ends named by the left interface position request its seam
color. -/
theorem commonBoundaryColorWord_leftPort_eq_seamColor
    (graphData : Data G)
    (hcubic : ∀ vertex, (incidentEdgeFinset G vertex).card = 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (side : SquareReductionSide)
    (C : (rootedPlanarClosureData graphData hcubic hcyclic
      cut hcard cyclicData side).closureRotationSystem.EdgeColoring Color)
    (hC : (rootedPlanarClosureData graphData hcubic hcyclic
      cut hcard cyclicData side).closureRotationSystem.IsTaitEdgeColoring C)
    (step : Fin 2) :
    (commonRetainedBoundaryData graphData cut cyclicData).colorWord
        (retainedCutColoring graphData cut cyclicData
          (rootedPlanarClosureData graphData hcubic hcyclic
            cut hcard cyclicData side) C)
        (side.leftPort step) =
      C (FourCutPlanarClosureData.seamEdge
        (rootedPlanarClosureData graphData hcubic hcyclic
          cut hcard cyclicData side) step) := by
  apply commonBoundaryColorWord_eq_seamColor_of_port
    graphData cut cyclicData
    (commonRetainedBoundaryData_wellFormed
      graphData hcubic hcyclic cut hcard cyclicData)
      _ C hC (side.leftPort step) step
  exact commonRetainedPort_mem_endpoints_leftSeam
    graphData hcubic hcyclic cut hcard cyclicData side step

/-- The two ends named by the right interface position request the same
seam color. -/
theorem commonBoundaryColorWord_rightPort_eq_seamColor
    (graphData : Data G)
    (hcubic : ∀ vertex, (incidentEdgeFinset G vertex).card = 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (side : SquareReductionSide)
    (C : (rootedPlanarClosureData graphData hcubic hcyclic
      cut hcard cyclicData side).closureRotationSystem.EdgeColoring Color)
    (hC : (rootedPlanarClosureData graphData hcubic hcyclic
      cut hcard cyclicData side).closureRotationSystem.IsTaitEdgeColoring C)
    (step : Fin 2) :
    (commonRetainedBoundaryData graphData cut cyclicData).colorWord
        (retainedCutColoring graphData cut cyclicData
          (rootedPlanarClosureData graphData hcubic hcyclic
            cut hcard cyclicData side) C)
        (side.rightPort step) =
      C (FourCutPlanarClosureData.seamEdge
        (rootedPlanarClosureData graphData hcubic hcyclic
          cut hcard cyclicData side) step) := by
  apply commonBoundaryColorWord_eq_seamColor_of_port
    graphData cut cyclicData
    (commonRetainedBoundaryData_wellFormed
      graphData hcubic hcyclic cut hcard cyclicData)
      _ C hC (side.rightPort step) step
  exact commonRetainedPort_mem_endpoints_rightSeam
    graphData hcubic hcyclic cut hcard cyclicData side step

/-- Restricting a Tait coloring of either planar closure yields an honest
retained-side state compatible with that noncrossing pairing. -/
theorem rootedPlanarClosure_retainedColorWord_compatible
    (graphData : Data G)
    (hcubic : ∀ vertex, (incidentEdgeFinset G vertex).card = 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (side : SquareReductionSide)
    (C : (rootedPlanarClosureData graphData hcubic hcyclic
      cut hcard cyclicData side).closureRotationSystem.EdgeColoring Color)
    (hC : (rootedPlanarClosureData graphData hcubic hcyclic
      cut hcard cyclicData side).closureRotationSystem.IsTaitEdgeColoring C) :
    side.Compatible
      ((commonRetainedBoundaryData graphData cut cyclicData).colorWord
        (retainedCutColoring graphData cut cyclicData
          (rootedPlanarClosureData graphData hcubic hcyclic
            cut hcard cyclicData side) C)) := by
  rw [side.compatible_iff_pair_colors]
  intro step
  exact (commonBoundaryColorWord_leftPort_eq_seamColor
    graphData hcubic hcyclic cut hcard cyclicData side C hC step).trans
      (commonBoundaryColorWord_rightPort_eq_seamColor
        graphData hcubic hcyclic cut hcard cyclicData side C hC step).symm

/-- Colorability of one rooted planar closure produces a genuine Tait
coloring of the induced cut side together with its exact paired boundary
certificate. -/
theorem exists_retainedCutColoring_compatible_of_rootedPlanarClosure
    (graphData : Data G)
    (hcubic : ∀ vertex, (incidentEdgeFinset G vertex).card = 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (side : SquareReductionSide)
    (hcolorable : RotationSystemTaitColorable
      (rootedPlanarClosureData graphData hcubic hcyclic
        cut hcard cyclicData side).closureRotationSystem) :
    ∃ retainedColoring : (retainedCutGraph G cut).EdgeColoring Color,
      IsTaitEdgeColoring (retainedCutGraph G cut) retainedColoring ∧
        side.Compatible
          ((commonRetainedBoundaryData graphData cut cyclicData).colorWord
            retainedColoring) := by
  rcases hcolorable with ⟨C, hC⟩
  exact ⟨retainedCutColoring graphData cut cyclicData
      (rootedPlanarClosureData graphData hcubic hcyclic
        cut hcard cyclicData side) C,
    retainedCutColoring_isTait graphData cut cyclicData
      (rootedPlanarClosureData graphData hcubic hcyclic
        cut hcard cyclicData side) C hC,
    rootedPlanarClosure_retainedColorWord_compatible
      graphData hcubic hcyclic cut hcard cyclicData side C hC⟩

/-- In a graph-backed vertex-minimal counterexample, either noncrossing
pairing is therefore realized by an honest coloring of the actual cut
side. -/
theorem exists_retainedCutColoring_compatible
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (side : SquareReductionSide) :
    ∃ retainedColoring : (retainedCutGraph G cut).EdgeColoring Color,
      IsTaitEdgeColoring (retainedCutGraph G cut) retainedColoring ∧
        side.Compatible
          ((commonRetainedBoundaryData graphData cut cyclicData).colorWord
            retainedColoring) := by
  let hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 := fun vertex => by
    rw [GoertzelV24DeletedEdgeTrail.incidentEdgeFinset_card_eq_degree]
    exact (graphData.toRotationSystem_isCubic_iff.mp
      minimal.spherical.cubic) vertex
  let hcyclic :=
    cyclicEdgeConnectivityAtLeast_four_of_vertexMinimalTaitCounterexample
      graphData minimal
  apply exists_retainedCutColoring_compatible_of_rootedPlanarClosure
    graphData hcubic hcyclic cut hcard cyclicData side
  exact rootedPlanarClosure_taitColorable graphData minimal cut hcard
    cyclicData side

/-- The concrete state family of the actual complement-side four-pole in
the common cyclic coordinates. -/
def commonRetainedStateSet
    (graphData : Data G)
    (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut)) : Set SquareBoundaryWord :=
  {word | ∃ retainedColoring : (retainedCutGraph G cut).EdgeColoring Color,
    IsTaitEdgeColoring (retainedCutGraph G cut) retainedColoring ∧
      (commonRetainedBoundaryData graphData cut cyclicData).colorWord
        retainedColoring = word}

/-- Every realized state is a nonzero four-color boundary word. -/
theorem commonRetainedStateSet_nonzero
    (graphData : Data G)
    (hcubic : ∀ vertex, (incidentEdgeFinset G vertex).card = 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (word : SquareBoundaryWord)
    (hword : word ∈ commonRetainedStateSet graphData cut cyclicData) :
    word.Nonzero := by
  rcases hword with ⟨C, _hC, rfl⟩
  let data := commonRetainedBoundaryData graphData cut cyclicData
  have hdata : data.WellFormed :=
    commonRetainedBoundaryData_wellFormed
      graphData hcubic hcyclic cut hcard cyclicData
  exact ⟨data.colorWord_ne_zero hdata C 0,
    data.colorWord_ne_zero hdata C 1,
    data.colorWord_ne_zero hdata C 2,
    data.colorWord_ne_zero hdata C 3⟩

/-- Each of the two noncrossing closure states belongs to the actual
realized state family. -/
theorem commonRetainedStateSet_has_compatible
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (side : SquareReductionSide) :
    ∃ word, word ∈ commonRetainedStateSet graphData cut cyclicData ∧
      side.Compatible word := by
  rcases exists_retainedCutColoring_compatible graphData minimal cut hcard
      cyclicData side with ⟨C, hC, hcompatible⟩
  refine ⟨(commonRetainedBoundaryData graphData cut cyclicData).colorWord C,
    ?_, hcompatible⟩
  exact ⟨C, hC, rfl⟩

end

end GoertzelV24FourEdgeCutClosureColor

end Mettapedia.GraphTheory.FourColor
