import Mettapedia.GraphTheory.FourColor.GoertzelV24FourEdgeCutNoncrossingInterfaces
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedVertexTaitSplice

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FourEdgeCutPlanarClosures

open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24CyclicExactCutConnectedSides
open GoertzelV24FaceDualConnectedness
open GoertzelV24FourEdgeCutBoundaryOrder
open GoertzelV24FourEdgeCutBoundaryToggle
open GoertzelV24FourEdgeCutNoncrossingInterfaces
open GoertzelV24FourEdgeCutPlanarInterfaces
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24PlanarBondSpliceEuler
open GoertzelV24RetainedSpliceEdgeDecomposition
open GoertzelV24RetainedSplicePrimalGraph
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationEdgeBridge
open GoertzelV24RotationSpliceConstructor
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24ThreeEdgeCutMinimality
open GoertzelV24TwoEdgeCutCapGeometry
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
variable {E : Type*} [Fintype E] [DecidableEq E]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Planar four-cut interface data together with the two point-set premises
needed to construct the retained-vertex seam closure: a retained root and
distinct endpoints for each new seam. -/
structure FourCutPlanarClosureData
    (RS : RotationSystem V E) (deleted : Finset V) where
  interface : FourCutPlanarInterfaceData RS deleted
  outer_retained : deletedRegionKeep deleted (RS.vertOf RS.outer)
  seamEndpoints : ∀ step,
    RS.vertOf
        (orderedBoundaryDart RS (deletedRegionKeep deleted)
          interface.leftCrossing
          (leftCrossing_outward RS deleted interface.leftCrossing
            interface.rightCrossing interface.boundary) step).1.1.1 ≠
      RS.vertOf
        (orderedBoundaryDart RS (deletedRegionKeep deleted)
          interface.rightCrossing
          (rightCrossing_outward RS deleted interface.leftCrossing
            interface.rightCrossing interface.boundary) step).1.1.1

namespace FourCutPlanarClosureData

variable {RS : RotationSystem V E} {deleted : Finset V}
  (data : FourCutPlanarClosureData RS deleted)

/-- Outward orientations of the first interface. -/
def leftCrosses :=
  leftCrossing_outward RS deleted data.interface.leftCrossing
    data.interface.rightCrossing data.interface.boundary

/-- Outward orientations of the second interface. -/
def rightCrosses :=
  rightCrossing_outward RS deleted data.interface.leftCrossing
    data.interface.rightCrossing data.interface.boundary

/-- Exact coverage of every retained boundary dart by the two interfaces. -/
def boundaryCover :=
  deletedRegionBoundaryCover RS deleted data.interface.leftCrossing
    data.interface.rightCrossing data.interface.boundary

/-- Close the retained side by joining equal-index positions of the two
oppositely ordered interfaces. -/
def closureRotationSystem :=
  orderedCutRetainedVertexRotationSystem RS
    (deletedRegionKeep deleted)
    data.interface.leftCrossing data.interface.rightCrossing
    data.leftCrosses data.rightCrosses
    data.interface.left_injective data.interface.right_injective
    data.boundaryCover data.interface.disjoint data.outer_retained
    data.seamEndpoints

/-- Removing at least one deleted vertex makes every four-cut closure
strictly smaller than the ambient vertex carrier. -/
theorem closureVertex_card_lt
    (removed : V) (hremoved : removed ∈ deleted) :
    Fintype.card (RetainedVertex (deletedRegionKeep deleted)) <
      Fintype.card V := by
  apply card_retainedVertex_lt (deletedRegionKeep deleted) removed
  simpa [deletedRegionKeep] using hremoved

/-- A retained seam closure only transports the old cyclic vertex rotations
to the surviving dart fibers. -/
theorem closure_vertexRotationCyclic
    (hcyclic : VertexRotationCyclic RS) :
    VertexRotationCyclic data.closureRotationSystem := by
  intro left right hvertex
  let keep := deletedRegionKeep deleted
  let parts := retainedDartEquivMatchedParts RS keep
    (orderedCut data.interface.leftCrossing)
    (orderedCut data.interface.rightCrossing)
    data.boundaryCover data.interface.disjoint
  have hunderlyingVertex :
      RS.vertOf (parts.symm left).1 = RS.vertOf (parts.symm right).1 := by
    rw [← matchedPartUnderlyingDart_eq_equiv_symm_val RS keep
      (orderedCut data.interface.leftCrossing)
      (orderedCut data.interface.rightCrossing)
      data.boundaryCover data.interface.disjoint left]
    rw [← matchedPartUnderlyingDart_eq_equiv_symm_val RS keep
      (orderedCut data.interface.leftCrossing)
      (orderedCut data.interface.rightCrossing)
      data.boundaryCover data.interface.disjoint right]
    change (data.closureRotationSystem.vertOf left).1 =
      (data.closureRotationSystem.vertOf right).1
    exact congrArg Subtype.val hvertex
  have hambient :
      RS.rho.SameCycle (parts.symm left).1 (parts.symm right).1 :=
    hcyclic _ _ hunderlyingVertex
  have hretained :
      (retainedRho RS keep).SameCycle (parts.symm left) (parts.symm right) :=
    Equiv.Perm.SameCycle.subtypePerm hambient
  rcases hretained with ⟨power, hpower⟩
  refine ⟨power, ?_⟩
  have hrho : data.closureRotationSystem.rho =
      matchedPartsRho RS keep
        (orderedCut data.interface.leftCrossing)
        (orderedCut data.interface.rightCrossing)
        data.boundaryCover data.interface.disjoint := by
    rfl
  rw [hrho]
  change ((parts.permCongr (retainedRho RS keep)) ^ power) left = right
  have hmap :
      parts.permCongr ((retainedRho RS keep) ^ power) =
        (parts.permCongr (retainedRho RS keep)) ^ power :=
    map_zpow parts.permCongrHom (retainedRho RS keep) power
  rw [← hmap]
  change parts (((retainedRho RS keep) ^ power) (parts.symm left)) = right
  rw [hpower, parts.apply_symm_apply]

/-- Connectedness of the retained induced graph makes its seam closure
connected. -/
theorem closure_primalConnected
    (hretained :
      (retainedAmbientPrimalGraph RS
        (deletedRegionKeep deleted)).Connected) :
    (rotationPrimalGraph data.closureRotationSystem).Connected := by
  exact
    rotationPrimalGraph_orderedCutRetainedVertexRotationSystem_connected_of_retained
      RS (deletedRegionKeep deleted)
      data.interface.leftCrossing data.interface.rightCrossing
      data.leftCrosses data.rightCrosses
      data.interface.left_injective data.interface.right_injective
      data.boundaryCover data.interface.disjoint data.outer_retained
      data.seamEndpoints hretained

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The planar-bond theorem proves that a four-cut seam closure is a
spherical cubic map once both ambient sides are connected. -/
theorem closure_orbitSphericalCubicMapData
    (graphData : Data G)
    (data : FourCutPlanarClosureData graphData.toRotationSystem deleted)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (hretainedConnected :
      (G.induce {vertex |
        deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex |
        Not (deletedRegionKeep deleted vertex)}).Connected) :
    OrbitSphericalCubicMapData data.closureRotationSystem := by
  exact orbitSphericalCubicMapData_orderedCutSplice_of_planar_bond
    graphData deleted
    data.interface.leftCrossing data.interface.rightCrossing
    data.interface.boundary
    data.interface.left_injective data.interface.right_injective
    data.interface.disjoint (by omega) data.interface.order
    hsphere htwoSided hconnected hrotation
    hretainedConnected hdeletedConnected data.outer_retained
    data.seamEndpoints

/-- All fields of the minimality class for a four-cut closure reduce to its
single remaining bridge-freeness proof. -/
def closureBridgelessSphericalCubicMapData
    (graphData : Data G)
    (data : FourCutPlanarClosureData graphData.toRotationSystem deleted)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (hretainedConnected :
      (G.induce {vertex |
        deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex |
        Not (deletedRegionKeep deleted vertex)}).Connected)
    (hbridgeFree : EdgeBridgeFree data.closureRotationSystem) :
    BridgelessSphericalCubicMapData data.closureRotationSystem where
  spherical := data.closure_orbitSphericalCubicMapData graphData hsphere
    htwoSided hconnected hrotation hretainedConnected hdeletedConnected
  primalConnected := data.closure_primalConnected (by
    simpa [retainedAmbientPrimalGraph,
      rotationPrimalGraph_toRotationSystem_eq] using hretainedConnected)
  vertexRotationCyclic := data.closure_vertexRotationCyclic hrotation
  edgeBridgeFree := hbridgeFree

/-- Vertex minimality colors every bridge-free four-cut closure. The
ambient minimal counterexample and the rerooted graph data may differ only
in their rotation-system presentation; they share the same vertex bound. -/
theorem closureTaitColorable_of_vertexMinimal
    (ambientGraphData closureGraphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample ambientGraphData)
    (data : FourCutPlanarClosureData
      closureGraphData.toRotationSystem deleted)
    (hsphere : OrbitSphericalCubicMapData
      closureGraphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided closureGraphData.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic closureGraphData.toRotationSystem)
    (hretainedConnected :
      (G.induce {vertex |
        deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex |
        Not (deletedRegionKeep deleted vertex)}).Connected)
    (removed : V) (hremoved : removed ∈ deleted)
    (hbridgeFree : EdgeBridgeFree data.closureRotationSystem) :
    RotationSystemTaitColorable data.closureRotationSystem := by
  apply minimal.smallerColorable data.closureRotationSystem
    (closureVertex_card_lt removed hremoved)
  exact data.closureBridgelessSphericalCubicMapData closureGraphData
    hsphere htwoSided hconnected hrotation hretainedConnected
    hdeletedConnected hbridgeFree

end FourCutPlanarClosureData

/-- A retained boundary dart is incident with its underlying graph edge at
its retained endpoint. -/
theorem orderedBoundaryDart_edge_incident
    (graphData : Data G) (deleted : Finset V)
    (crossing : Fin n → G.edgeSet)
    (hcrosses : ∀ step, ∃ dart : graphData.toRotationSystem.D,
      graphData.toRotationSystem.edgeOf dart = crossing step ∧
      deletedRegionKeep deleted
        (graphData.toRotationSystem.vertOf dart) ∧
      ¬ deletedRegionKeep deleted
        (graphData.toRotationSystem.vertOf
          (graphData.toRotationSystem.alpha dart)))
    (step : Fin n) :
    crossing step ∈ incidentEdgeFinset G
      (graphData.toRotationSystem.vertOf
        (orderedBoundaryDart graphData.toRotationSystem
          (deletedRegionKeep deleted) crossing hcrosses step).1.1.1) := by
  let boundary := orderedBoundaryDart graphData.toRotationSystem
    (deletedRegionKeep deleted) crossing hcrosses step
  have hendpoint : graphData.toRotationSystem.vertOf boundary.1.1.1 ∈
      graphData.toRotationSystem.endpoints
        (graphData.toRotationSystem.edgeOf boundary.1.1.1) := by
    apply graphData.toRotationSystem.mem_endpoints_iff.2
    exact ⟨boundary.1.1.1,
      graphData.toRotationSystem.mem_dartsOn.2 rfl, rfl⟩
  have hendpoint' : graphData.toRotationSystem.vertOf boundary.1.1.1 ∈
      graphData.toRotationSystem.endpoints (crossing step) := by
    rw [← orderedBoundaryDart_edgeOf graphData.toRotationSystem
      (deletedRegionKeep deleted) crossing hcrosses step]
    exact hendpoint
  have hvalue : graphData.toRotationSystem.vertOf boundary.1.1.1 ∈
      ((crossing step).1 : Sym2 V) :=
    (mem_simpleGraphRotationSystem_endpoints_iff graphData
      (crossing step)
      (graphData.toRotationSystem.vertOf boundary.1.1.1)).1 hendpoint'
  simpa [incidentEdgeFinset] using hvalue

/-- Cyclic four-connectivity makes the endpoint pair of every proposed
noncrossing seam distinct on the retained side of an exact four-cut. -/
theorem rootedInterface_seamEndpoints
    (graphData : Data G)
    (hcubic : ∀ vertex, (incidentEdgeFinset G vertex).card = 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (side : SquareReductionSide) (step : Fin 2) :
    let rootedGraphData := cyclicData.rootedGraphData graphData
    let rootedBoundaryData := cyclicData.rootedBoundaryData graphData
    let interface := rootedBoundaryData.interface side
    rootedGraphData.toRotationSystem.vertOf
        (orderedBoundaryDart rootedGraphData.toRotationSystem
          (deletedRegionKeep (cyclicCutVertexSide cut))
          interface.leftCrossing
          (leftCrossing_outward rootedGraphData.toRotationSystem
            (cyclicCutVertexSide cut) interface.leftCrossing
            interface.rightCrossing interface.boundary) step).1.1.1 ≠
      rootedGraphData.toRotationSystem.vertOf
        (orderedBoundaryDart rootedGraphData.toRotationSystem
          (deletedRegionKeep (cyclicCutVertexSide cut))
          interface.rightCrossing
          (rightCrossing_outward rootedGraphData.toRotationSystem
            (cyclicCutVertexSide cut) interface.leftCrossing
            interface.rightCrossing interface.boundary) step).1.1.1 := by
  dsimp only
  let rootedGraphData := cyclicData.rootedGraphData graphData
  let rootedBoundaryData := cyclicData.rootedBoundaryData graphData
  let interface := rootedBoundaryData.interface side
  let leftCrosses := leftCrossing_outward rootedGraphData.toRotationSystem
    (cyclicCutVertexSide cut) interface.leftCrossing
      interface.rightCrossing interface.boundary
  let rightCrosses := rightCrossing_outward rootedGraphData.toRotationSystem
    (cyclicCutVertexSide cut) interface.leftCrossing
      interface.rightCrossing interface.boundary
  let leftBoundary := orderedBoundaryDart rootedGraphData.toRotationSystem
    (deletedRegionKeep (cyclicCutVertexSide cut))
      interface.leftCrossing leftCrosses step
  let rightBoundary := orderedBoundaryDart rootedGraphData.toRotationSystem
    (deletedRegionKeep (cyclicCutVertexSide cut))
      interface.rightCrossing rightCrosses step
  intro hendpoints
  change rootedGraphData.toRotationSystem.vertOf leftBoundary.1.1.1 =
    rootedGraphData.toRotationSystem.vertOf rightBoundary.1.1.1 at hendpoints
  have hedgesNe : interface.leftCrossing step ≠
      interface.rightCrossing step := by
    intro hedges
    have hleft : interface.leftCrossing step ∈
        orderedCut interface.leftCrossing :=
      Finset.mem_image.mpr ⟨step, Finset.mem_univ step, rfl⟩
    have hright : interface.rightCrossing step ∈
        orderedCut interface.rightCrossing :=
      Finset.mem_image.mpr ⟨step, Finset.mem_univ step, rfl⟩
    exact Finset.disjoint_left.mp interface.disjoint
      hleft (hedges ▸ hright)
  have hleftBoundary : interface.leftCrossing step ∈
      vertexSetCrossingEdges rootedGraphData.toRotationSystem
        (cyclicCutVertexSide cut) := by
    rw [← interface.boundary]
    exact Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨step, Finset.mem_univ step, rfl⟩)
  have hrightBoundary : interface.rightCrossing step ∈
      vertexSetCrossingEdges rootedGraphData.toRotationSystem
        (cyclicCutVertexSide cut) := by
    rw [← interface.boundary]
    exact Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨step, Finset.mem_univ step, rfl⟩)
  have hleftCut : interface.leftCrossing step ∈ cut.edgeCut := by
    rw [← vertexSetCrossingEdges_cyclicCutVertexSide
      rootedGraphData cut]
    exact hleftBoundary
  have hrightCut : interface.rightCrossing step ∈ cut.edgeCut := by
    rw [← vertexSetCrossingEdges_cyclicCutVertexSide
      rootedGraphData cut]
    exact hrightBoundary
  let vertex := rootedGraphData.toRotationSystem.vertOf leftBoundary.1.1.1
  have hvertex : cut.compl.side vertex := by
    change ¬ cut.side vertex
    have hkeep := leftBoundary.1.1.2
    simpa [vertex, leftBoundary, deletedRegionKeep,
      mem_cyclicCutVertexSide_iff] using hkeep
  have hleftIncident : interface.leftCrossing step ∈
      incidentEdgeFinset G vertex := by
    exact orderedBoundaryDart_edge_incident rootedGraphData
      (cyclicCutVertexSide cut) interface.leftCrossing leftCrosses step
  have hrightIncident : interface.rightCrossing step ∈
      incidentEdgeFinset G vertex := by
    have hright := orderedBoundaryDart_edge_incident rootedGraphData
      (cyclicCutVertexSide cut) interface.rightCrossing rightCrosses step
    change interface.rightCrossing step ∈ incidentEdgeFinset G
      (rootedGraphData.toRotationSystem.vertOf rightBoundary.1.1.1) at hright
    rw [← hendpoints] at hright
    simpa [vertex] using hright
  exact no_two_cut_edges_share_side_vertex hcubic hcyclic cut.compl
    (by simpa using hcard) vertex hvertex hedgesNe
    hleftIncident hrightIncident (by simpa using hleftCut)
    (by simpa using hrightCut)

/-- Either noncrossing presentation of an exact cyclic four-cut supplies a
well-defined rooted planar closure. -/
def rootedPlanarClosureData
    (graphData : Data G)
    (hcubic : ∀ vertex, (incidentEdgeFinset G vertex).card = 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (side : SquareReductionSide) :
    FourCutPlanarClosureData
      (cyclicData.rootedGraphData graphData).toRotationSystem
      (cyclicCutVertexSide cut) where
  interface := (cyclicData.rootedBoundaryData graphData).interface side
  outer_retained := cyclicData.rooted_outer_retained graphData
  seamEndpoints := rootedInterface_seamEndpoints graphData hcubic hcyclic
    cut hcard cyclicData side

/-- Once its seam closure is bridge-free, either noncrossing presentation
of an exact cyclic four-cut is colored by vertex minimality. All other
structural premises are forced by the ambient minimal counterexample and
cyclic four-connectivity. -/
theorem rootedPlanarClosure_taitColorable_of_edgeBridgeFree
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
    EdgeBridgeFree closure.closureRotationSystem →
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
  let rootedGraphData := cyclicData.rootedGraphData graphData
  let closure := rootedPlanarClosureData graphData hcubic hcyclic
    cut hcard cyclicData side
  intro hbridgeFree
  have hconnected : G.Connected := by
    rw [← rotationPrimalGraph_toRotationSystem_eq G graphData]
    exact minimal.primalConnected
  have hsides := induce_both_sides_connected_of_card_eq_four
    hconnected hcyclic cut hcard
  have hrootSphere : OrbitSphericalCubicMapData
      rootedGraphData.toRotationSystem := by
    change OrbitSphericalCubicMapData
      (graphData.toRotationSystem.withOuter
        (cyclicData.boundaryOrder 0).1.1)
    exact (orbitSphericalCubicMapData_withOuter_iff
      graphData.toRotationSystem
      (cyclicData.boundaryOrder 0).1.1).2 minimal.spherical
  have hrootTwoSided : OrbitFacesTwoSided
      rootedGraphData.toRotationSystem := by
    change OrbitFacesTwoSided
      (graphData.toRotationSystem.withOuter
        (cyclicData.boundaryOrder 0).1.1)
    exact (orbitFacesTwoSided_withOuter_iff
      graphData.toRotationSystem
      (cyclicData.boundaryOrder 0).1.1).2 minimal.facesTwoSided
  have hrootRotation : VertexRotationCyclic
      rootedGraphData.toRotationSystem := by
    change VertexRotationCyclic
      (graphData.toRotationSystem.withOuter
        (cyclicData.boundaryOrder 0).1.1)
    exact (vertexRotationCyclic_withOuter_iff
      graphData.toRotationSystem
      (cyclicData.boundaryOrder 0).1.1).2
        minimal.vertexRotationCyclic
  have hretainedConnected :
      (G.induce {vertex |
        deletedRegionKeep (cyclicCutVertexSide cut) vertex}).Connected := by
    have hkeep :
        {vertex : V |
          deletedRegionKeep (cyclicCutVertexSide cut) vertex} =
          {vertex : V | ¬ cut.side vertex} := by
      ext vertex
      simp only [Set.mem_setOf_eq, deletedRegionKeep]
      rw [mem_cyclicCutVertexSide_iff]
    rw [hkeep]
    exact hsides.2
  have hdeletedConnected :
      (G.induce {vertex |
        Not (deletedRegionKeep
          (cyclicCutVertexSide cut) vertex)}).Connected := by
    have hdeleted :
        {vertex : V |
          Not (deletedRegionKeep
            (cyclicCutVertexSide cut) vertex)} =
          {vertex : V | cut.side vertex} := by
      ext vertex
      simp only [Set.mem_setOf_eq, deletedRegionKeep]
      rw [mem_cyclicCutVertexSide_iff]
      simp
    rw [hdeleted]
    exact hsides.1
  rcases cut.hinside_cycle with
    ⟨removed, hremoved, walk, hwalkCycle, hwalkSide⟩
  have hremovedFin : removed ∈ cyclicCutVertexSide cut :=
    (mem_cyclicCutVertexSide_iff cut removed).2 hremoved
  exact FourCutPlanarClosureData.closureTaitColorable_of_vertexMinimal
    graphData rootedGraphData minimal closure hrootSphere hrootTwoSided
    hconnected hrootRotation hretainedConnected hdeletedConnected
    removed hremovedFin hbridgeFree

end

end GoertzelV24FourEdgeCutPlanarClosures

end Mettapedia.GraphTheory.FourColor
