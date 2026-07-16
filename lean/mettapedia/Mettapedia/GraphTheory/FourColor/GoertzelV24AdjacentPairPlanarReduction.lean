import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairReduction
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutNormalization

namespace Mettapedia.GraphTheory.FourColor

namespace SquareReductionSide

open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24OrderedCutFaceReturnProfile

@[simp] theorem join01_23_leftPort_zero :
    SquareReductionSide.join01_23.leftPort (0 : Fin 2) = 1 := by
  decide

@[simp] theorem join01_23_leftPort_one :
    SquareReductionSide.join01_23.leftPort (1 : Fin 2) = 2 := by
  decide

@[simp] theorem join01_23_rightPort_zero :
    SquareReductionSide.join01_23.rightPort (0 : Fin 2) = 0 := by
  decide

@[simp] theorem join01_23_rightPort_one :
    SquareReductionSide.join01_23.rightPort (1 : Fin 2) = 3 := by
  decide

/-- The physical square-boundary port represented by an ordered seam
position.  Left positions are followed by right positions in reverse order,
as prescribed by `oppositeBoundaryCycle`. -/
def boundaryPort (side : SquareReductionSide) :
    OrderedSeamPosition 2 → Fin 4
  | Sum.inl step => side.leftPort step
  | Sum.inr step => side.rightPort step

/-- Both noncrossing square pairings present the same positive cyclic order
on their four physical ports. -/
theorem boundaryPort_oppositeBoundaryCycle
    (side : SquareReductionSide) (position : OrderedSeamPosition 2) :
    side.boundaryPort (oppositeBoundaryCycle 2 position) =
      finRotate 4 (side.boundaryPort position) := by
  fin_cases side <;> rcases position with step | step <;>
    fin_cases step <;>
    decide

end SquareReductionSide

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

open GoertzelV24AdjacentPairBoundary
open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24PlanarBondSpliceEuler
open GoertzelV24RetainedSpliceEdgeDecomposition
open GoertzelV24RetainedSplicePrimalGraph
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationEdgeBridge
open GoertzelV24RotationSpliceConstructor
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24TwoEdgeCutCapGeometry
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoEdgeCutNormalization
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance planarGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance planarRetainedVertexSetFintype (first second : V) :
    Fintype (retainedVertexSet first second) :=
  retainedVertexSetFintype first second

local instance planarRetainedVertexSetDecidableEq (first second : V) :
    DecidableEq (retainedVertexSet first second) :=
  retainedVertexSetDecidableEq first second

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Two distinct named endpoints of a nonremoved rotation edge are adjacent
in the edge-deleted primal graph. -/
theorem edgeDeletedPrimalGraph_adj_of_mem_endpoints
    {W F : Type*} [Fintype W] [DecidableEq W]
    [Fintype F] [DecidableEq F]
    (RS : RotationSystem W F) {edge removed : F} {left right : W}
    (hedge : edge ≠ removed)
    (hleft : left ∈ RS.endpoints edge)
    (hright : right ∈ RS.endpoints edge)
    (hvertices : left ≠ right) :
    (edgeDeletedPrimalGraph RS removed).Adj left right := by
  rcases RS.mem_endpoints_iff.1 hleft with ⟨dart, hdart, hvert⟩
  have hdartEdge : RS.edgeOf dart = edge := RS.mem_dartsOn.1 hdart
  refine ⟨dart, ?_, hvert, ?_⟩
  · intro hremoved
    exact hedge (hdartEdge.symm.trans hremoved)
  · have hrightPair : right ∈
        ({RS.vertOf dart, RS.vertOf (RS.alpha dart)} : Finset W) := by
      rw [← RS.endpoints_eq_pair_of_mem hdart]
      exact hright
    simp only [Finset.mem_insert, Finset.mem_singleton] at hrightPair
    rcases hrightPair with hrightLeft | hrightAlpha
    · exact False.elim (hvertices (hvert.symm.trans hrightLeft.symm))
    · exact hrightAlpha.symm

/-- The boundary cycle predicted by one of the two noncrossing square
pairings, transported from its ordered seam coordinates to the actual
outward boundary darts. -/
def squareExpectedBoundaryCycle
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide) :
    Equiv.Perm (BoundaryDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices)) :=
  (orderedBoundaryPositionEquiv
    (data.rootedRotationSystem graphData) data.deletedVertices
    (data.leftCrossing side) (data.rightCrossing side)
    (data.pairedCut_boundary (data.rootedGraphData graphData) side)
    (data.leftCrossing_injective side)
    (data.rightCrossing_injective side)
    (data.pairedCuts_disjoint side)).permCongr
      (oppositeBoundaryCycle 2)

/-- The edge under an ordered boundary position is the boundary edge named
by its physical port. -/
theorem orderedBoundaryPosition_edgeOf
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide) (position : OrderedSeamPosition 2) :
    (data.rootedRotationSystem graphData).edgeOf
        ((orderedBoundaryPositionEquiv
          (data.rootedRotationSystem graphData) data.deletedVertices
          (data.leftCrossing side) (data.rightCrossing side)
          (data.pairedCut_boundary (data.rootedGraphData graphData) side)
          (data.leftCrossing_injective side)
          (data.rightCrossing_injective side)
          (data.pairedCuts_disjoint side) position).1.1) =
      data.boundaryEdge (side.boundaryPort position) := by
  rcases position with step | step
  · rw [orderedBoundaryPositionEquiv_apply_left,
      orderedBoundaryDart_edgeOf]
    rfl
  · rw [orderedBoundaryPositionEquiv_apply_right,
      orderedBoundaryDart_edgeOf]
    rfl

/-- Independently of which noncrossing pairing is chosen, its predicted
cycle advances the physical port by one positive cyclic step. -/
theorem squareExpectedBoundaryCycle_edgeOf
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide)
    (dart : BoundaryDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices))
    (port : Fin 4)
    (hport : (data.rootedRotationSystem graphData).edgeOf dart.1.1 =
      data.boundaryEdge port) :
    (data.rootedRotationSystem graphData).edgeOf
        ((data.squareExpectedBoundaryCycle graphData side dart).1.1) =
      data.boundaryEdge (finRotate 4 port) := by
  let positionEquiv := orderedBoundaryPositionEquiv
    (data.rootedRotationSystem graphData) data.deletedVertices
    (data.leftCrossing side) (data.rightCrossing side)
    (data.pairedCut_boundary (data.rootedGraphData graphData) side)
    (data.leftCrossing_injective side)
    (data.rightCrossing_injective side)
    (data.pairedCuts_disjoint side)
  let position := positionEquiv.symm dart
  have hdart : positionEquiv position = dart :=
    positionEquiv.apply_symm_apply dart
  have hpositionPort : side.boundaryPort position = port := by
    apply data.boundaryEdge_injective
    calc
      data.boundaryEdge (side.boundaryPort position) =
          (data.rootedRotationSystem graphData).edgeOf
            (positionEquiv position).1.1 :=
        (data.orderedBoundaryPosition_edgeOf graphData side position).symm
      _ = (data.rootedRotationSystem graphData).edgeOf dart.1.1 := by
        rw [hdart]
      _ = data.boundaryEdge port := hport
  calc
    (data.rootedRotationSystem graphData).edgeOf
        ((data.squareExpectedBoundaryCycle graphData side dart).1.1) =
      (data.rootedRotationSystem graphData).edgeOf
        ((data.squareExpectedBoundaryCycle graphData side
          (positionEquiv position)).1.1) := by rw [hdart]
    _ = (data.rootedRotationSystem graphData).edgeOf
        (positionEquiv (oppositeBoundaryCycle 2 position)).1.1 := by
      simp [squareExpectedBoundaryCycle, positionEquiv]
    _ = data.boundaryEdge
        (side.boundaryPort (oppositeBoundaryCycle 2 position)) :=
      data.orderedBoundaryPosition_edgeOf graphData side _
    _ = data.boundaryEdge
        (finRotate 4 (side.boundaryPort position)) := by
      rw [side.boundaryPort_oppositeBoundaryCycle]
    _ = data.boundaryEdge (finRotate 4 port) := by rw [hpositionPort]

/-- The two square presentations induce exactly the same expected boundary
cycle.  This is the formal statement that reorienting and cyclically shifting
the endpoints of the two noncrossing chord systems does not change the
ambient boundary order. -/
theorem squareExpectedBoundaryCycle_eq
    (graphData : Data G) (data : AdjacentPairData G)
    (first second : SquareReductionSide) :
    data.squareExpectedBoundaryCycle graphData first =
      data.squareExpectedBoundaryCycle graphData second := by
  apply Equiv.ext
  intro dart
  apply boundaryDart_eq_of_edgeOf_eq
  have hedgeMem :
      (data.rootedRotationSystem graphData).edgeOf dart.1.1 ∈
        vertexSetCrossingEdges (data.rootedRotationSystem graphData)
          data.deletedVertices :=
    boundaryDart_edge_mem_vertexSetCrossingEdges
      (data.rootedRotationSystem graphData) data.deletedVertices dart
  rw [← data.boundaryEdgeSet_eq_vertexSetCrossingEdges
    (data.rootedGraphData graphData)] at hedgeMem
  rcases Finset.mem_image.mp hedgeMem with ⟨port, _hport, hedge⟩
  have hport :
      (data.rootedRotationSystem graphData).edgeOf dart.1.1 =
        data.boundaryEdge port := hedge.symm
  exact
    (data.squareExpectedBoundaryCycle_edgeOf graphData first dart port hport).trans
      (data.squareExpectedBoundaryCycle_edgeOf graphData second dart port hport).symm

/-- A single canonical facial-order certificate for the ports.  With the
chosen port labels this says that the deleted-region boundary advances
`0,1,2,3` cyclically. -/
def PortsFollowCyclicDeletedBoundaryOrder
    (graphData : Data G) (data : AdjacentPairData G) : Prop :=
  deletedRegionBoundarySuccessor (data.rootedRotationSystem graphData)
      data.deletedVertices =
    data.squareExpectedBoundaryCycle graphData
      SquareReductionSide.join12_30

/-- One canonical cyclic port-order certificate supplies the precise
planar-bond order required by either noncrossing square reduction. -/
theorem cutsFollowOppositeDeletedBoundaryOrder
    (graphData : Data G) (data : AdjacentPairData G)
    (horder : data.PortsFollowCyclicDeletedBoundaryOrder graphData)
    (side : SquareReductionSide) :
    CutsFollowOppositeDeletedBoundaryOrder
      (data.rootedRotationSystem graphData) data.deletedVertices
      (data.leftCrossing side) (data.rightCrossing side)
      (data.pairedCut_boundary (data.rootedGraphData graphData) side)
      (data.leftCrossing_injective side)
      (data.rightCrossing_injective side)
      (data.pairedCuts_disjoint side) := by
  change deletedRegionBoundarySuccessor
      (data.rootedRotationSystem graphData) data.deletedVertices =
    data.squareExpectedBoundaryCycle graphData side
  exact horder.trans
    (data.squareExpectedBoundaryCycle_eq graphData
      SquareReductionSide.join12_30 side)

omit [Fintype V] [DecidableRel G.Adj] in
/-- The deleted side is the connected graph on the central adjacent pair. -/
theorem deletedRegion_connected
    (data : AdjacentPairData G) :
    (G.induce {vertex |
      Not (deletedRegionKeep data.deletedVertices vertex)}).Connected := by
  have hvertices : {vertex |
      Not (deletedRegionKeep data.deletedVertices vertex)} =
      ({data.firstVertex, data.secondVertex} : Set V) := by
    ext vertex
    by_cases hfirst : vertex = data.firstVertex <;>
      by_cases hsecond : vertex = data.secondVertex <;>
      simp [deletedRegionKeep, deletedVertices, hfirst, hsecond]
  rw [hvertices]
  exact SimpleGraph.induce_pair_connected_of_adj data.centralAdjacent

omit [DecidableRel G.Adj] in
/-- Removing the adjacent pair strictly decreases the vertex carrier. -/
theorem reductionVertex_card_lt
    (data : AdjacentPairData G) :
    Fintype.card (RetainedVertex
        (deletedRegionKeep data.deletedVertices)) <
      Fintype.card V := by
  apply card_retainedVertex_lt
    (deletedRegionKeep data.deletedVertices) data.firstVertex
  simp [deletedRegionKeep, deletedVertices]

/-- An ordered retained splice merely transports the old vertex rotations to
the surviving dart fibers, so cyclicity at every retained vertex is
preserved. -/
theorem reduction_vertexRotationCyclic
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide)
    (hcyclic : VertexRotationCyclic
      (data.rootedRotationSystem graphData)) :
    VertexRotationCyclic (data.reductionRotationSystem graphData side) := by
  intro left right hvertex
  let RS := data.rootedRotationSystem graphData
  let keep := deletedRegionKeep data.deletedVertices
  let parts := retainedDartEquivMatchedParts RS keep
    (orderedCut (data.leftCrossing side))
    (orderedCut (data.rightCrossing side))
    (data.boundaryCover graphData side) (data.pairedCuts_disjoint side)
  have hunderlyingVertex :
      RS.vertOf (parts.symm left).1 = RS.vertOf (parts.symm right).1 := by
    rw [← matchedPartUnderlyingDart_eq_equiv_symm_val RS keep
      (orderedCut (data.leftCrossing side))
      (orderedCut (data.rightCrossing side))
      (data.boundaryCover graphData side) (data.pairedCuts_disjoint side) left]
    rw [← matchedPartUnderlyingDart_eq_equiv_symm_val RS keep
      (orderedCut (data.leftCrossing side))
      (orderedCut (data.rightCrossing side))
      (data.boundaryCover graphData side) (data.pairedCuts_disjoint side) right]
    change
      ((data.reductionRotationSystem graphData side).vertOf left).1 =
        ((data.reductionRotationSystem graphData side).vertOf right).1
    exact congrArg Subtype.val hvertex
  have hambient :
      RS.rho.SameCycle (parts.symm left).1 (parts.symm right).1 :=
    hcyclic _ _ hunderlyingVertex
  have hretained :
      (retainedRho RS keep).SameCycle (parts.symm left) (parts.symm right) :=
    Equiv.Perm.SameCycle.subtypePerm hambient
  rcases hretained with ⟨power, hpower⟩
  refine ⟨power, ?_⟩
  have hrho : (data.reductionRotationSystem graphData side).rho =
      matchedPartsRho RS keep
        (orderedCut (data.leftCrossing side))
        (orderedCut (data.rightCrossing side))
        (data.boundaryCover graphData side)
        (data.pairedCuts_disjoint side) := by
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

/-- Connectedness of the retained induced graph makes either square
reduction connected after its two seam edges are added. -/
theorem reduction_primalConnected
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide)
    (hretainedConnected :
      (G.induce {vertex |
        deletedRegionKeep data.deletedVertices vertex}).Connected) :
    (rotationPrimalGraph
      (data.reductionRotationSystem graphData side)).Connected := by
  apply
    rotationPrimalGraph_orderedCutRetainedVertexRotationSystem_connected_of_retained
      (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices)
      (data.leftCrossing side) (data.rightCrossing side)
      (data.leftCrosses graphData side) (data.rightCrosses graphData side)
      (data.leftCrossing_injective side)
      (data.rightCrossing_injective side)
      (data.boundaryCover graphData side) (data.pairedCuts_disjoint side)
      (data.outer_retained graphData) (data.seamEndpoints graphData side)
  simpa [retainedAmbientPrimalGraph, rootedRotationSystem, rootedGraphData,
    rotationPrimalGraph_toRotationSystem_eq]
    using hretainedConnected

/-- The planar-bond Euler theorem discharges spherical cubicity for either
square reduction once the actual port order and retained-side connectedness
are known. -/
theorem reduction_orbitSphericalCubicMapData
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (hretainedConnected :
      (G.induce {vertex |
        deletedRegionKeep data.deletedVertices vertex}).Connected)
    (horder : data.PortsFollowCyclicDeletedBoundaryOrder graphData)
    (side : SquareReductionSide) :
    OrbitSphericalCubicMapData
      (data.reductionRotationSystem graphData side) := by
  apply orbitSphericalCubicMapData_orderedCutSplice_of_planar_bond
    (data.rootedGraphData graphData) data.deletedVertices
    (data.leftCrossing side) (data.rightCrossing side)
    (data.pairedCut_boundary (data.rootedGraphData graphData) side)
    (data.leftCrossing_injective side)
    (data.rightCrossing_injective side)
    (data.pairedCuts_disjoint side) (by omega)
    (data.cutsFollowOppositeDeletedBoundaryOrder graphData horder side)
  · simpa [rootedRotationSystem, rootedGraphData] using minimal.spherical
  · simpa [rootedRotationSystem, rootedGraphData] using minimal.facesTwoSided
  · rw [← rotationPrimalGraph_toRotationSystem_eq G graphData]
    exact minimal.primalConnected
  · simpa [rootedRotationSystem, rootedGraphData] using
      minimal.vertexRotationCyclic
  · exact hretainedConnected
  · exact data.deletedRegion_connected

/-- All structural fields needed by vertex minimality except bridge-freeness
are now consequences of the adjacent-pair geometry. -/
def reductionBridgelessSphericalCubicMapData
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (hretainedConnected :
      (G.induce {vertex |
        deletedRegionKeep data.deletedVertices vertex}).Connected)
    (horder : data.PortsFollowCyclicDeletedBoundaryOrder graphData)
    (side : SquareReductionSide)
    (hbridgeFree : EdgeBridgeFree
      (data.reductionRotationSystem graphData side)) :
    BridgelessSphericalCubicMapData
      (data.reductionRotationSystem graphData side) where
  spherical := data.reduction_orbitSphericalCubicMapData graphData minimal
    hretainedConnected horder side
  primalConnected := data.reduction_primalConnected graphData side
    hretainedConnected
  vertexRotationCyclic := data.reduction_vertexRotationCyclic graphData side
    (by simpa [rootedRotationSystem, rootedGraphData] using
      minimal.vertexRotationCyclic)
  edgeBridgeFree := hbridgeFree

/-- Consequently, each bridge-free square reduction is Tait-colorable by
vertex minimality; no Euler, connectedness, or cyclic-rotation premise remains
at this application site. -/
theorem reductionTaitColorable_of_edgeBridgeFree
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (hretainedConnected :
      (G.induce {vertex |
        deletedRegionKeep data.deletedVertices vertex}).Connected)
    (horder : data.PortsFollowCyclicDeletedBoundaryOrder graphData)
    (side : SquareReductionSide)
    (hbridgeFree : EdgeBridgeFree
      (data.reductionRotationSystem graphData side)) :
    RotationSystemTaitColorable
      (data.reductionRotationSystem graphData side) := by
  apply minimal.smallerColorable (data.reductionRotationSystem graphData side)
    data.reductionVertex_card_lt
  exact data.reductionBridgelessSphericalCubicMapData graphData minimal
    hretainedConnected horder side hbridgeFree

/-- Regard one connected component of the induced adjacent-pair deletion as
an ambient vertex-side predicate. -/
def retainedComponentSide
    (data : AdjacentPairData G)
    (component : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).ConnectedComponent) (vertex : V) : Prop :=
  ∃ retained : retainedVertexSet data.firstVertex data.secondVertex,
    retained ∈ component.supp ∧ retained.1 = vertex

omit [Fintype V] [DecidableRel G.Adj] in
/-- Every ambient edge leaving a component of the retained deletion is one
of the four exposed boundary edges, and its retained port lies in that
component. -/
theorem exists_boundaryPort_of_crosses_retainedComponent
    (data : AdjacentPairData G)
    (component : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).ConnectedComponent)
    (edge : G.edgeSet)
    (hcross : EdgeCrossesVertexSide G
      (data.retainedComponentSide component) edge) :
    ∃ port : Fin 4,
      edge = data.boundaryEdge port ∧
        data.retainedPort port ∈ component.supp := by
  rcases hcross with
    ⟨inside, outside, hinsideEdge, houtsideEdge,
      hinsideSide, houtsideSide⟩
  rcases hinsideSide with ⟨insideRetained, hinsideComponent, hinsideValue⟩
  have hvertices : inside ≠ outside := by
    intro heq
    apply houtsideSide
    exact ⟨insideRetained, hinsideComponent, hinsideValue.trans heq⟩
  have hedgeValue : edge.1 = s(inside, outside) :=
    sym2_eq_mk_of_mem_of_mem_of_ne hinsideEdge houtsideEdge hvertices
  have hadj : G.Adj inside outside :=
    (SimpleGraph.mem_edgeSet G).1 (by simpa [hedgeValue] using edge.2)
  have houtsideDeleted :
      outside = data.firstVertex ∨ outside = data.secondVertex := by
    by_contra hretained
    push Not at hretained
    let outsideRetained : retainedVertexSet data.firstVertex
        data.secondVertex := ⟨outside, hretained⟩
    have hinduced :
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).Adj
          insideRetained outsideRetained := by
      change G.Adj insideRetained.1 outsideRetained.1
      simpa [hinsideValue] using hadj
    have houtsideComponent : outsideRetained ∈ component.supp :=
      (component.mem_supp_congr_adj hinduced).mp hinsideComponent
    exact houtsideSide
      ⟨outsideRetained, houtsideComponent, rfl⟩
  have hinsideRetained :
      inside ∉ data.deletedVertices := by
    simp only [deletedVertices, Finset.mem_insert, Finset.mem_singleton]
    rintro (hfirst | hsecond)
    · exact insideRetained.2.1 (hinsideValue.trans hfirst)
    · exact insideRetained.2.2 (hinsideValue.trans hsecond)
  have houtsideMem : outside ∈ data.deletedVertices := by
    rcases houtsideDeleted with rfl | rfl <;>
      simp [deletedVertices]
  have hcrossDeleted : EdgeCrossesVertexSide G
      (fun vertex => vertex ∈ data.deletedVertices) edge :=
    ⟨outside, inside, houtsideEdge, hinsideEdge,
      houtsideMem, hinsideRetained⟩
  rcases (data.edgeCrosses_deletedVertices_iff_exists_boundaryEdge edge).1
      hcrossDeleted with ⟨port, hedge⟩
  refine ⟨port, hedge, ?_⟩
  subst edge
  change inside ∈ (data.boundaryEdgeValue port : Sym2 V) at hinsideEdge
  rw [data.boundaryEdgeValue_eq] at hinsideEdge
  simp only [Sym2.mem_iff] at hinsideEdge
  have hinsidePort : inside = data.portVertex port := by
    rcases hinsideEdge with hdeleted | hport
    · exfalso
      apply hinsideRetained
      fin_cases port <;>
        simp [deletedVertices,
          GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryDeletedVertex,
          hdeleted]
    · exact hport
  have hretainedEq : data.retainedPort port = insideRetained := by
    apply Subtype.ext
    exact hinsidePort.symm.trans hinsideValue.symm
  rw [hretainedEq]
  exact hinsideComponent

/-- If all boundary ports other than `left` and `right` are the two deleted
edges, strict two-edge connectivity forces every retained vertex into the
component of one of those two surviving ports. -/
theorem retained_reachable_port_or_port_of_complement
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (left right removedFirst removedSecond : Fin 4)
    (hcomplement : ∀ port : Fin 4, port ≠ left → port ≠ right →
      port = removedFirst ∨ port = removedSecond)
    (hremoved : removedFirst ≠ removedSecond)
    (vertex : retainedVertexSet data.firstVertex data.secondVertex) :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).Reachable
        vertex (data.retainedPort left) ∨
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).Reachable
        vertex (data.retainedPort right) := by
  let retained := DeletedAdjacentPairGraph G data.firstVertex
    data.secondVertex
  by_cases hleft : retained.Reachable vertex (data.retainedPort left)
  · exact Or.inl hleft
  by_cases hright : retained.Reachable vertex (data.retainedPort right)
  · exact Or.inr hright
  exfalso
  let component := retained.connectedComponentMk vertex
  let side : V → Prop := data.retainedComponentSide component
  have hvertexSide : side vertex.1 :=
    ⟨vertex, ConnectedComponent.connectedComponentMk_mem, rfl⟩
  have portOutside : ∀ port : Fin 4,
      ¬ retained.Reachable vertex (data.retainedPort port) →
        ¬ side (data.portVertex port) := by
    intro port hnot
    rintro ⟨portRetained, hportComponent, hportValue⟩
    have hportRetained : portRetained = data.retainedPort port := by
      apply Subtype.ext
      exact hportValue
    subst portRetained
    have hcomponents :=
      (ConnectedComponent.mem_supp_iff component
        (data.retainedPort port)).1 hportComponent
    change retained.connectedComponentMk (data.retainedPort port) =
      retained.connectedComponentMk vertex at hcomponents
    exact hnot (ConnectedComponent.exact hcomponents |>.symm)
  have hleftOutside : ¬ side (data.portVertex left) :=
    portOutside left hleft
  have hdelete :=
    deleteEdges_pair_connected_of_vertexMinimalTaitCounterexample
      graphData minimal (data.boundaryEdge removedFirst)
      (data.boundaryEdge removedSecond)
      (fun hedge => hremoved (data.boundaryEdge_injective hedge))
  rcases hdelete vertex.1 (data.portVertex left) with ⟨deletedWalk⟩
  let ambientWalk : G.Walk vertex.1 (data.portVertex left) :=
    deletedWalk.mapLe (G.deleteEdges_le
      ({(data.boundaryEdge removedFirst).1,
        (data.boundaryEdge removedSecond).1} : Set (Sym2 V)))
  have hambientEdges : ambientWalk.edges = deletedWalk.edges :=
    deletedWalk.edges_mapLe_eq_edges _
  rcases exists_edgeCrossesVertexSide_of_walk_endpoint_sides
      side ambientWalk hvertexSide hleftOutside with
    ⟨crossing, hcrossingWalk, hcrossing⟩
  rcases data.exists_boundaryPort_of_crosses_retainedComponent
      component crossing hcrossing with
    ⟨port, hedge, hportComponent⟩
  have hportLeft : port ≠ left := by
    intro hport
    subst port
    exact hleftOutside
      ⟨data.retainedPort left, hportComponent, rfl⟩
  have hportRight : port ≠ right := by
    intro hport
    subst port
    exact portOutside right hright
      ⟨data.retainedPort right, hportComponent, rfl⟩
  rcases hcomplement port hportLeft hportRight with
    hportRemoved | hportRemoved
  · have havoids : (data.boundaryEdge removedFirst).1 ∉
        ambientWalk.edges := by
      intro hmem
      have hdeleted := deletedWalk.edges_subset_edgeSet
        (by simpa [hambientEdges] using hmem)
      simp at hdeleted
    have hedgeRemoved : crossing = data.boundaryEdge removedFirst :=
      hedge.trans (congrArg data.boundaryEdge hportRemoved)
    exact havoids (by simpa [hedgeRemoved] using hcrossingWalk)
  · have havoids : (data.boundaryEdge removedSecond).1 ∉
        ambientWalk.edges := by
      intro hmem
      have hdeleted := deletedWalk.edges_subset_edgeSet
        (by simpa [hambientEdges] using hmem)
      simp at hdeleted
    have hedgeRemoved : crossing = data.boundaryEdge removedSecond :=
      hedge.trans (congrArg data.boundaryEdge hportRemoved)
    exact havoids (by simpa [hedgeRemoved] using hcrossingWalk)

/-- Strict two-edge connectivity of a vertex-minimal counterexample makes
the graph left after deleting any adjacent cubic pair connected.  The proof
uses four complementary two-edge deletions: ports `0` and `1` first cover all
components, while the other three covers force those two ports themselves
into one component. -/
theorem retainedRegion_connected_of_vertexMinimalTaitCounterexample
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G) :
    (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Connected := by
  let retained := DeletedAdjacentPairGraph G data.firstVertex
    data.secondVertex
  have cover01 : ∀ vertex,
      retained.Reachable vertex (data.retainedPort 0) ∨
        retained.Reachable vertex (data.retainedPort 1) := by
    intro vertex
    apply data.retained_reachable_port_or_port_of_complement
      graphData minimal 0 1 2 3
    · intro port hzero hone
      fin_cases port <;> simp_all
    · decide
  have cover02 : ∀ vertex,
      retained.Reachable vertex (data.retainedPort 0) ∨
        retained.Reachable vertex (data.retainedPort 2) := by
    intro vertex
    apply data.retained_reachable_port_or_port_of_complement
      graphData minimal 0 2 1 3
    · intro port hzero htwo
      fin_cases port <;> simp_all
    · decide
  have cover03 : ∀ vertex,
      retained.Reachable vertex (data.retainedPort 0) ∨
        retained.Reachable vertex (data.retainedPort 3) := by
    intro vertex
    apply data.retained_reachable_port_or_port_of_complement
      graphData minimal 0 3 1 2
    · intro port hzero hthree
      fin_cases port <;> simp_all
    · decide
  have cover23 : ∀ vertex,
      retained.Reachable vertex (data.retainedPort 2) ∨
        retained.Reachable vertex (data.retainedPort 3) := by
    intro vertex
    apply data.retained_reachable_port_or_port_of_complement
      graphData minimal 2 3 0 1
    · intro port htwo hthree
      fin_cases port <;> simp_all
    · decide
  have hzeroOne :
      retained.Reachable (data.retainedPort 0) (data.retainedPort 1) := by
    by_contra hnot
    have honeTwo :
        retained.Reachable (data.retainedPort 1) (data.retainedPort 2) := by
      rcases cover02 (data.retainedPort 1) with honeZero | honeTwo
      · exact False.elim (hnot honeZero.symm)
      · exact honeTwo
    have honeThree :
        retained.Reachable (data.retainedPort 1) (data.retainedPort 3) := by
      rcases cover03 (data.retainedPort 1) with honeZero | honeThree
      · exact False.elim (hnot honeZero.symm)
      · exact honeThree
    rcases cover23 (data.retainedPort 0) with hzeroTwo | hzeroThree
    · exact hnot (hzeroTwo.trans honeTwo.symm)
    · exact hnot (hzeroThree.trans honeThree.symm)
  change retained.Connected
  letI : Nonempty (retainedVertexSet data.firstVertex data.secondVertex) :=
    ⟨data.retainedPort 0⟩
  refine ⟨?_⟩
  intro left right
  rcases cover01 left with hleftZero | hleftOne <;>
    rcases cover01 right with hrightZero | hrightOne
  · exact hleftZero.trans hrightZero.symm
  · exact (hleftZero.trans hzeroOne).trans hrightOne.symm
  · exact (hleftOne.trans hzeroOne.symm).trans hrightZero.symm
  · exact hleftOne.trans hrightOne.symm

/-- A seam edge is never a bridge when the retained graph is connected: an
old retained path joins its two ports and uses only internal output edges. -/
theorem reductionSeamEndpoints_reachable_without_seam
    (graphData : Data G) (data : AdjacentPairData G)
    (hretained : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Connected)
    (side : SquareReductionSide) (step : Fin 2) :
    (edgeDeletedPrimalGraph (data.reductionRotationSystem graphData side)
      (data.reductionSeamEdge graphData side step)).Reachable
        (data.reductionVertexOfDeletedVertex
          (data.retainedPort (side.leftPort step)))
        (data.reductionVertexOfDeletedVertex
          (data.retainedPort (side.rightPort step))) := by
  let retained := DeletedAdjacentPairGraph G data.firstVertex
    data.secondVertex
  apply reachable_map_of_adj_eq_or_adj
    data.reductionVertexOfDeletedVertex
    (source := retained)
    (target := edgeDeletedPrimalGraph
      (data.reductionRotationSystem graphData side)
      (data.reductionSeamEdge graphData side step))
  · intro left right hadj
    apply Or.inr
    let edge : retained.edgeSet :=
      ⟨s(left, right), (SimpleGraph.mem_edgeSet retained).2 hadj⟩
    apply edgeDeletedPrimalGraph_adj_of_mem_endpoints
      (data.reductionRotationSystem graphData side)
      (edge := data.reductionEdgeOfDeletedEdge graphData side edge)
    · exact data.reductionEdgeOfDeletedEdge_ne_reductionSeamEdge
        graphData side edge step
    · apply data.reductionVertex_mem_endpoints_reductionEdgeOfDeletedEdge
      change left ∈ s(left, right)
      rw [Sym2.mem_iff]
      exact Or.inl rfl
    · apply data.reductionVertex_mem_endpoints_reductionEdgeOfDeletedEdge
      change right ∈ s(left, right)
      rw [Sym2.mem_iff]
      exact Or.inr rfl
    · intro heq
      apply hadj.ne
      apply Subtype.ext
      exact congrArg
        (fun vertex : RetainedVertex
          (deletedRegionKeep data.deletedVertices) => vertex.1) heq
  · exact hretained (data.retainedPort (side.leftPort step))
      (data.retainedPort (side.rightPort step))

/-- The left-oriented dart of a named square-reduction seam. -/
def reductionLeftSeamDart
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide) (step : Fin 2) :
    (data.reductionRotationSystem graphData side).D :=
  Sum.inr (Sum.inl
    (orderedBoundaryDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices)
      (data.leftCrossing side) (data.leftCrosses graphData side) step))

/-- The right-oriented dart of a named square-reduction seam. -/
def reductionRightSeamDart
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide) (step : Fin 2) :
    (data.reductionRotationSystem graphData side).D :=
  Sum.inr (Sum.inr
    (orderedBoundaryDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices)
      (data.rightCrossing side) (data.rightCrosses graphData side) step))

@[simp]
theorem reductionRotationSystem_alpha_leftSeamDart
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide) (step : Fin 2) :
    (data.reductionRotationSystem graphData side).alpha
      (data.reductionLeftSeamDart graphData side step) =
        data.reductionRightSeamDart graphData side step := by
  unfold reductionRotationSystem reductionLeftSeamDart
    reductionRightSeamDart
  rw [orderedCutRetainedVertexRotationSystem_alpha_left,
    orderedCutSeamMatching_apply]

@[simp]
theorem reductionRotationSystem_alpha_rightSeamDart
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide) (step : Fin 2) :
    (data.reductionRotationSystem graphData side).alpha
      (data.reductionRightSeamDart graphData side step) =
        data.reductionLeftSeamDart graphData side step := by
  rw [← data.reductionRotationSystem_alpha_leftSeamDart graphData side step]
  exact (data.reductionRotationSystem graphData side).alpha_involutive _

@[simp]
theorem reductionRotationSystem_edgeOf_leftSeamDart
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide) (step : Fin 2) :
    (data.reductionRotationSystem graphData side).edgeOf
      (data.reductionLeftSeamDart graphData side step) =
        data.reductionSeamEdge graphData side step :=
  rfl

@[simp]
theorem reductionRotationSystem_edgeOf_rightSeamDart
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide) (step : Fin 2) :
    (data.reductionRotationSystem graphData side).edgeOf
      (data.reductionRightSeamDart graphData side step) =
        data.reductionSeamEdge graphData side step := by
  rw [← data.reductionRotationSystem_alpha_leftSeamDart graphData side step,
    (data.reductionRotationSystem graphData side).edge_alpha]
  rfl

@[simp]
theorem reductionRotationSystem_vertOf_leftSeamDart
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide) (step : Fin 2) :
    (data.reductionRotationSystem graphData side).vertOf
      (data.reductionLeftSeamDart graphData side step) =
        data.reductionVertexOfDeletedVertex
          (data.retainedPort (side.leftPort step)) := by
  apply Subtype.ext
  exact data.leftBoundaryDart_vertex graphData side step

@[simp]
theorem reductionRotationSystem_vertOf_rightSeamDart
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide) (step : Fin 2) :
    (data.reductionRotationSystem graphData side).vertOf
      (data.reductionRightSeamDart graphData side step) =
        data.reductionVertexOfDeletedVertex
          (data.retainedPort (side.rightPort step)) := by
  apply Subtype.ext
  exact data.rightBoundaryDart_vertex graphData side step

/-- The central edge as an ambient graph edge. -/
abbrev ambientCentralEdge (data : AdjacentPairData G) : G.edgeSet :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.centralEdge data

/-- Contract the first deleted vertex to port `0` and the second to port `2`.
The remaining boundary edges then become precisely the two seams of the
`join01_23` reduction. -/
def centralPairContractionVertex
    (data : AdjacentPairData G) (vertex : V) :
    RetainedVertex (deletedRegionKeep data.deletedVertices) :=
  if hfirst : vertex = data.firstVertex then
    data.reductionVertexOfDeletedVertex (data.retainedPort 0)
  else if hsecond : vertex = data.secondVertex then
    data.reductionVertexOfDeletedVertex (data.retainedPort 2)
  else
    ⟨vertex, by
      change vertex ∉ data.deletedVertices
      simp only [deletedVertices, Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h)
      · exact hfirst h
      · exact hsecond h⟩

omit [Fintype V] [DecidableRel G.Adj] in
@[simp]
theorem centralPairContractionVertex_first
    (data : AdjacentPairData G) :
    data.centralPairContractionVertex data.firstVertex =
      data.reductionVertexOfDeletedVertex (data.retainedPort 0) := by
  simp [centralPairContractionVertex]

omit [Fintype V] [DecidableRel G.Adj] in
@[simp]
theorem centralPairContractionVertex_second
    (data : AdjacentPairData G) :
    data.centralPairContractionVertex data.secondVertex =
      data.reductionVertexOfDeletedVertex (data.retainedPort 2) := by
  simp [centralPairContractionVertex, data.centralAdjacent.ne']

omit [Fintype V] [DecidableRel G.Adj] in
@[simp]
theorem centralPairContractionVertex_retained
    (data : AdjacentPairData G)
    (vertex : retainedVertexSet data.firstVertex data.secondVertex) :
    data.centralPairContractionVertex vertex.1 =
      data.reductionVertexOfDeletedVertex vertex := by
  rw [centralPairContractionVertex]
  split
  · rename_i hfirst
    exact False.elim (vertex.2.1 hfirst)
  · split
    · rename_i hsecond
      exact False.elim (vertex.2.2 hsecond)
    · apply Subtype.ext
      rfl

omit [Fintype V] [DecidableRel G.Adj] in
@[simp]
theorem centralPairContractionVertex_port
    (data : AdjacentPairData G) (port : Fin 4) :
    data.centralPairContractionVertex (data.portVertex port) =
      data.reductionVertexOfDeletedVertex (data.retainedPort port) :=
  data.centralPairContractionVertex_retained (data.retainedPort port)

/-- A seam remains available after an unrelated retained internal edge is
removed. -/
theorem reductionSeam_adj_edgeDeleted_internalDart
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide)
    (removed : InternalDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices))
    (step : Fin 2) :
    (edgeDeletedPrimalGraph (data.reductionRotationSystem graphData side)
      ((data.reductionRotationSystem graphData side).edgeOf
        (Sum.inl removed))).Adj
      (data.reductionVertexOfDeletedVertex
        (data.retainedPort (side.leftPort step)))
      (data.reductionVertexOfDeletedVertex
        (data.retainedPort (side.rightPort step))) := by
  apply edgeDeletedPrimalGraph_adj_of_mem_endpoints
    (data.reductionRotationSystem graphData side)
    (edge := data.reductionSeamEdge graphData side step)
  · exact (retainedInternalSpliceEdge_ne_orderedCutSeamSpliceEdge
      (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices)
      (data.leftCrossing side) (data.rightCrossing side)
      (data.leftCrosses graphData side) (data.rightCrosses graphData side)
      (data.leftCrossing_injective side)
      (data.rightCrossing_injective side)
      (data.boundaryCover graphData side) (data.pairedCuts_disjoint side)
      (data.outer_retained graphData) (data.seamEndpoints graphData side)
      removed step).symm
  · exact data.reductionLeftPort_mem_endpoints_reductionSeamEdge
      graphData side step
  · exact data.reductionRightPort_mem_endpoints_reductionSeamEdge
      graphData side step
  · intro heq
    apply data.portVertex_ne (side.leftPort_ne_rightPort step step)
    exact congrArg
      (fun vertex : RetainedVertex
        (deletedRegionKeep data.deletedVertices) => vertex.1) heq

/-- Contracting the two deleted vertices sends every edge surviving deletion
of one retained edge and the central edge either to a vertex equality or to
an edge of the `join01_23` reduction with that retained edge removed. -/
theorem centralPairContraction_adj_eq_or_adj
    (graphData : Data G) (data : AdjacentPairData G)
    (removed : InternalDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices))
    {left right : V}
    (hadj : (G.deleteEdges
      ({((data.rootedRotationSystem graphData).edgeOf removed.1.1).1,
        data.ambientCentralEdge.1} : Set (Sym2 V))).Adj left right) :
    data.centralPairContractionVertex left =
        data.centralPairContractionVertex right ∨
      (edgeDeletedPrimalGraph
        (data.reductionRotationSystem graphData
          SquareReductionSide.join01_23)
        ((data.reductionRotationSystem graphData
          SquareReductionSide.join01_23).edgeOf
          (Sum.inl removed))).Adj
        (data.centralPairContractionVertex left)
        (data.centralPairContractionVertex right) := by
  let RS := data.rootedRotationSystem graphData
  let keep := deletedRegionKeep data.deletedVertices
  let side := SquareReductionSide.join01_23
  let newRS := data.reductionRotationSystem graphData side
  rcases SimpleGraph.deleteEdges_adj.mp hadj with ⟨hambient, hnotDeleted⟩
  have hnotPair :
      s(left, right) ≠ (RS.edgeOf removed.1.1).1 ∧
        s(left, right) ≠ data.ambientCentralEdge.1 := by
    simpa [RS] using hnotDeleted
  have seamAdj (step : Fin 2) :
      (edgeDeletedPrimalGraph newRS
        (newRS.edgeOf (Sum.inl removed))).Adj
        (data.reductionVertexOfDeletedVertex
          (data.retainedPort (side.leftPort step)))
        (data.reductionVertexOfDeletedVertex
          (data.retainedPort (side.rightPort step))) := by
    exact data.reductionSeam_adj_edgeDeleted_internalDart
      graphData side removed step
  by_cases hleftFirst : left = data.firstVertex
  · subst left
    have hrightSecond : right ≠ data.secondVertex := by
      intro hright
      subst right
      apply hnotPair.2
      rfl
    have hrightCases : right = data.portVertex 0 ∨
        right = data.portVertex 1 := by
      have hmem : right ∈ G.neighborSet data.firstVertex := hambient
      rw [data.firstNeighbors] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with hsecond | hzero | hone
      · exact False.elim (hrightSecond hsecond)
      · exact Or.inl hzero
      · exact Or.inr hone
    rcases hrightCases with rfl | rfl
    · exact Or.inl (by
        rw [data.centralPairContractionVertex_first,
          data.centralPairContractionVertex_port])
    · apply Or.inr
      simpa only [newRS, side, data.centralPairContractionVertex_first,
        data.centralPairContractionVertex_port,
        SquareReductionSide.join01_23_leftPort_zero,
        SquareReductionSide.join01_23_rightPort_zero] using
          (seamAdj 0).symm
  · by_cases hleftSecond : left = data.secondVertex
    · subst left
      have hrightFirst : right ≠ data.firstVertex := by
        intro hright
        subst right
        apply hnotPair.2
        exact Sym2.eq_swap
      have hrightCases : right = data.portVertex 2 ∨
          right = data.portVertex 3 := by
        have hmem : right ∈ G.neighborSet data.secondVertex := hambient
        rw [data.secondNeighbors] at hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with hfirst | htwo | hthree
        · exact False.elim (hrightFirst hfirst)
        · exact Or.inl htwo
        · exact Or.inr hthree
      rcases hrightCases with rfl | rfl
      · exact Or.inl (by
          rw [data.centralPairContractionVertex_second,
            data.centralPairContractionVertex_port])
      · apply Or.inr
        simpa only [newRS, side, data.centralPairContractionVertex_second,
          data.centralPairContractionVertex_port,
          SquareReductionSide.join01_23_leftPort_one,
          SquareReductionSide.join01_23_rightPort_one] using seamAdj 1
    · by_cases hrightFirst : right = data.firstVertex
      · subst right
        have hleftCases : left = data.portVertex 0 ∨
            left = data.portVertex 1 := by
          have hmem : left ∈ G.neighborSet data.firstVertex := hambient.symm
          rw [data.firstNeighbors] at hmem
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
          rcases hmem with hsecond | hzero | hone
          · exact False.elim (hleftSecond hsecond)
          · exact Or.inl hzero
          · exact Or.inr hone
        rcases hleftCases with rfl | rfl
        · exact Or.inl (by
            rw [data.centralPairContractionVertex_first,
              data.centralPairContractionVertex_port])
        · apply Or.inr
          simpa only [newRS, side, data.centralPairContractionVertex_first,
            data.centralPairContractionVertex_port,
            SquareReductionSide.join01_23_leftPort_zero,
            SquareReductionSide.join01_23_rightPort_zero] using seamAdj 0
      · by_cases hrightSecond : right = data.secondVertex
        · subst right
          have hleftCases : left = data.portVertex 2 ∨
              left = data.portVertex 3 := by
            have hmem : left ∈ G.neighborSet data.secondVertex := hambient.symm
            rw [data.secondNeighbors] at hmem
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
            rcases hmem with hfirst | htwo | hthree
            · exact False.elim (hleftFirst hfirst)
            · exact Or.inl htwo
            · exact Or.inr hthree
          rcases hleftCases with rfl | rfl
          · exact Or.inl (by
              rw [data.centralPairContractionVertex_second,
                data.centralPairContractionVertex_port])
          · apply Or.inr
            simpa only [newRS, side, data.centralPairContractionVertex_second,
              data.centralPairContractionVertex_port,
              SquareReductionSide.join01_23_leftPort_one,
              SquareReductionSide.join01_23_rightPort_one] using
                (seamAdj 1).symm
        · apply Or.inr
          let leftRetained : retainedVertexSet data.firstVertex
              data.secondVertex := ⟨left, hleftFirst, hleftSecond⟩
          let rightRetained : retainedVertexSet data.firstVertex
              data.secondVertex := ⟨right, hrightFirst, hrightSecond⟩
          let ambientDart : G.Dart := ⟨(left, right), hambient⟩
          let internal : InternalDart RS keep :=
            ⟨⟨ambientDart, by
              change left ∉ data.deletedVertices
              simp [deletedVertices, hleftFirst, hleftSecond]⟩,
              by
                change right ∉ data.deletedVertices
                simp [deletedVertices, hrightFirst, hrightSecond]⟩
          have hinternalEdge : RS.edgeOf internal.1.1 ≠
              RS.edgeOf removed.1.1 := by
            intro hedge
            apply hnotPair.1
            exact congrArg Subtype.val hedge
          refine ⟨Sum.inl internal, ?_, ?_, ?_⟩
          · intro hedge
            apply hinternalEdge
            exact (retainedInternalSpliceEdge_eq_iff RS keep
              (data.leftCrossing side) (data.rightCrossing side)
              (data.leftCrosses graphData side)
              (data.rightCrosses graphData side)
              (data.leftCrossing_injective side)
              (data.rightCrossing_injective side)
              (data.boundaryCover graphData side)
              (data.pairedCuts_disjoint side)
              (data.outer_retained graphData)
              (data.seamEndpoints graphData side) internal removed).1 hedge
          · rw [data.centralPairContractionVertex_retained leftRetained]
            apply Subtype.ext
            rfl
          · rw [data.centralPairContractionVertex_retained rightRetained]
            apply Subtype.ext
            rfl

/-- An internal dart retained after deleting the adjacent pair cannot belong
to the central edge between the two deleted vertices. -/
theorem internalDart_edgeOf_ne_ambientCentralEdge
    (graphData : Data G) (data : AdjacentPairData G)
    (dart : InternalDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices)) :
    (data.rootedRotationSystem graphData).edgeOf dart.1.1 ≠
      data.ambientCentralEdge := by
  intro hedge
  let RS := data.rootedRotationSystem graphData
  have hendpoint : RS.vertOf dart.1.1 ∈
      RS.endpoints (RS.edgeOf dart.1.1) := by
    apply RS.mem_endpoints_iff.2
    exact ⟨dart.1.1, RS.mem_dartsOn.2 rfl, rfl⟩
  rw [hedge] at hendpoint
  have hcentral : RS.vertOf dart.1.1 ∈
      (data.ambientCentralEdge : Sym2 V) :=
    (mem_simpleGraphRotationSystem_endpoints_iff
      (data.rootedGraphData graphData) data.ambientCentralEdge _).1
        hendpoint
  have hdeleted : RS.vertOf dart.1.1 = data.firstVertex ∨
      RS.vertOf dart.1.1 = data.secondVertex := by
    simpa [ambientCentralEdge,
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.centralEdge,
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.centralEdgeValue]
      using hcentral
  apply dart.1.2
  change RS.vertOf dart.1.1 ∈ data.deletedVertices
  simpa [deletedVertices] using hdeleted

/-- Strict two-edge connectivity supplies a return path around every retained
internal edge of the `join01_23` reduction.  The central pair is contracted
onto the two seams along that path. -/
theorem reductionInternalDart_reachable_without_edge_join01_23
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (removed : InternalDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices)) :
    (edgeDeletedPrimalGraph
      (data.reductionRotationSystem graphData
        SquareReductionSide.join01_23)
      ((data.reductionRotationSystem graphData
        SquareReductionSide.join01_23).edgeOf
        (Sum.inl removed))).Reachable
      ((data.reductionRotationSystem graphData
        SquareReductionSide.join01_23).vertOf (Sum.inl removed))
      ((data.reductionRotationSystem graphData
        SquareReductionSide.join01_23).vertOf
        ((data.reductionRotationSystem graphData
          SquareReductionSide.join01_23).alpha (Sum.inl removed))) := by
  let RS := data.rootedRotationSystem graphData
  have hconnected :=
    deleteEdges_pair_connected_of_vertexMinimalTaitCounterexample
      graphData minimal (RS.edgeOf removed.1.1)
        data.ambientCentralEdge
        (data.internalDart_edgeOf_ne_ambientCentralEdge graphData removed)
  have hsource := hconnected (RS.vertOf removed.1.1)
    (RS.vertOf (RS.alpha removed.1.1))
  have hmapped := reachable_map_of_adj_eq_or_adj
    data.centralPairContractionVertex
    (source := G.deleteEdges
      ({(RS.edgeOf removed.1.1).1,
        data.ambientCentralEdge.1} : Set (Sym2 V)))
    (target := edgeDeletedPrimalGraph
      (data.reductionRotationSystem graphData
        SquareReductionSide.join01_23)
      ((data.reductionRotationSystem graphData
        SquareReductionSide.join01_23).edgeOf (Sum.inl removed)))
    (fun {left right} hadj =>
      data.centralPairContraction_adj_eq_or_adj graphData removed
        (by simpa only [RS] using hadj))
    hsource
  have hleftFirst : RS.vertOf removed.1.1 ≠ data.firstVertex := by
    intro heq
    apply removed.1.2
    change RS.vertOf removed.1.1 ∈ data.deletedVertices
    simp [deletedVertices, heq]
  have hleftSecond : RS.vertOf removed.1.1 ≠ data.secondVertex := by
    intro heq
    apply removed.1.2
    change RS.vertOf removed.1.1 ∈ data.deletedVertices
    simp [deletedVertices, heq]
  have hrightFirst : RS.vertOf (RS.alpha removed.1.1) ≠
      data.firstVertex := by
    intro heq
    apply removed.2
    change RS.vertOf (RS.alpha removed.1.1) ∈ data.deletedVertices
    simp [deletedVertices, heq]
  have hrightSecond : RS.vertOf (RS.alpha removed.1.1) ≠
      data.secondVertex := by
    intro heq
    apply removed.2
    change RS.vertOf (RS.alpha removed.1.1) ∈ data.deletedVertices
    simp [deletedVertices, heq]
  have hleftMapped : data.centralPairContractionVertex
      (RS.vertOf removed.1.1) =
      (data.reductionRotationSystem graphData
        SquareReductionSide.join01_23).vertOf (Sum.inl removed) := by
    simp only [centralPairContractionVertex, hleftFirst, hleftSecond,
      ↓reduceDIte]
    apply Subtype.ext
    rfl
  have hrightMapped : data.centralPairContractionVertex
      (RS.vertOf (RS.alpha removed.1.1)) =
      (data.reductionRotationSystem graphData
        SquareReductionSide.join01_23).vertOf
        ((data.reductionRotationSystem graphData
          SquareReductionSide.join01_23).alpha (Sum.inl removed)) := by
    simp only [centralPairContractionVertex, hrightFirst, hrightSecond,
      ↓reduceDIte]
    apply Subtype.ext
    rfl
  rw [hleftMapped, hrightMapped] at hmapped
  exact hmapped

/-- The canonical `join01_23` square reduction of a vertex-minimal
counterexample is bridge-free.  Old edges inherit avoiding paths from strict
two-edge connectivity; each new seam inherits one from retained-side
connectedness. -/
theorem reductionJoin01_23_edgeBridgeFree
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G) :
    EdgeBridgeFree (data.reductionRotationSystem graphData
      SquareReductionSide.join01_23) := by
  intro dart
  rcases dart with internal | seam
  · exact data.reductionInternalDart_reachable_without_edge_join01_23
      graphData minimal internal
  · have hretained :
        (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Connected :=
      retainedRegion_connected_of_vertexMinimalTaitCounterexample
        graphData minimal data
    rcases seam with left | right
    · rcases orderedBoundaryDart_surjective
        (data.rootedRotationSystem graphData)
        (deletedRegionKeep data.deletedVertices)
        (data.leftCrossing SquareReductionSide.join01_23)
        (data.leftCrosses graphData SquareReductionSide.join01_23) left with
        ⟨step, hstep⟩
      subst left
      change (edgeDeletedPrimalGraph
        (data.reductionRotationSystem graphData
          SquareReductionSide.join01_23)
        ((data.reductionRotationSystem graphData
          SquareReductionSide.join01_23).edgeOf
          (data.reductionLeftSeamDart graphData
            SquareReductionSide.join01_23 step))).Reachable
        ((data.reductionRotationSystem graphData
          SquareReductionSide.join01_23).vertOf
          (data.reductionLeftSeamDart graphData
            SquareReductionSide.join01_23 step))
        ((data.reductionRotationSystem graphData
          SquareReductionSide.join01_23).vertOf
          ((data.reductionRotationSystem graphData
            SquareReductionSide.join01_23).alpha
            (data.reductionLeftSeamDart graphData
              SquareReductionSide.join01_23 step)))
      rw [data.reductionRotationSystem_edgeOf_leftSeamDart,
        data.reductionRotationSystem_vertOf_leftSeamDart,
        data.reductionRotationSystem_alpha_leftSeamDart,
        data.reductionRotationSystem_vertOf_rightSeamDart]
      exact data.reductionSeamEndpoints_reachable_without_seam
        graphData hretained SquareReductionSide.join01_23 step
    · rcases orderedBoundaryDart_surjective
        (data.rootedRotationSystem graphData)
        (deletedRegionKeep data.deletedVertices)
        (data.rightCrossing SquareReductionSide.join01_23)
        (data.rightCrosses graphData SquareReductionSide.join01_23) right with
        ⟨step, hstep⟩
      subst right
      change (edgeDeletedPrimalGraph
        (data.reductionRotationSystem graphData
          SquareReductionSide.join01_23)
        ((data.reductionRotationSystem graphData
          SquareReductionSide.join01_23).edgeOf
          (data.reductionRightSeamDart graphData
            SquareReductionSide.join01_23 step))).Reachable
        ((data.reductionRotationSystem graphData
          SquareReductionSide.join01_23).vertOf
          (data.reductionRightSeamDart graphData
            SquareReductionSide.join01_23 step))
        ((data.reductionRotationSystem graphData
          SquareReductionSide.join01_23).vertOf
          ((data.reductionRotationSystem graphData
            SquareReductionSide.join01_23).alpha
            (data.reductionRightSeamDart graphData
              SquareReductionSide.join01_23 step)))
      rw [data.reductionRotationSystem_edgeOf_rightSeamDart,
        data.reductionRotationSystem_vertOf_rightSeamDart,
        data.reductionRotationSystem_alpha_rightSeamDart,
        data.reductionRotationSystem_vertOf_leftSeamDart]
      exact (data.reductionSeamEndpoints_reachable_without_seam
        graphData hretained SquareReductionSide.join01_23 step).symm

/-- Vertex minimality therefore colors every bridge-free planar square
reduction once only the canonical facial port order is supplied. -/
theorem reductionTaitColorable_of_edgeBridgeFree_of_order
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (horder : data.PortsFollowCyclicDeletedBoundaryOrder graphData)
    (side : SquareReductionSide)
    (hbridgeFree : EdgeBridgeFree
      (data.reductionRotationSystem graphData side)) :
    RotationSystemTaitColorable
      (data.reductionRotationSystem graphData side) := by
  have hretainedConnected :
      (G.induce {vertex |
        deletedRegionKeep data.deletedVertices vertex}).Connected := by
    have hkeep : {vertex |
        deletedRegionKeep data.deletedVertices vertex} =
        retainedVertexSet data.firstVertex data.secondVertex := by
      ext vertex
      simp [deletedRegionKeep, deletedVertices,
        retainedVertexSet]
    rw [hkeep]
    exact retainedRegion_connected_of_vertexMinimalTaitCounterexample
      graphData minimal data
  apply data.reductionTaitColorable_of_edgeBridgeFree graphData minimal
    hretainedConnected horder side hbridgeFree

/-- For the canonical first square pairing, cyclic facial port order is the
only remaining input: all graph-theoretic hypotheses of vertex minimality
are consequences of the adjacent-pair configuration. -/
theorem reductionJoin01_23_taitColorable_of_order
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (horder : data.PortsFollowCyclicDeletedBoundaryOrder graphData) :
    RotationSystemTaitColorable
      (data.reductionRotationSystem graphData
        SquareReductionSide.join01_23) := by
  exact data.reductionTaitColorable_of_edgeBridgeFree_of_order
    graphData minimal horder SquareReductionSide.join01_23
      (data.reductionJoin01_23_edgeBridgeFree graphData minimal)

/-- The preceding planar reduction theorem, restricted back to the induced
deletion, produces the exact `join01_23` four-port compatibility certificate
needed by adjacent-pair insertion. -/
theorem exists_deletedColoring_join01_23_compatible_of_order
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (horder : data.PortsFollowCyclicDeletedBoundaryOrder graphData) :
    ∃ deletedColoring :
        (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).EdgeColoring Color,
      IsTaitEdgeColoring
          (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
          deletedColoring ∧
        SquareReductionSide.join01_23.Compatible
          (data.degreeTwoBoundaryData.colorWord deletedColoring) := by
  apply data.exists_deletedColoring_compatible_of_reductionTaitColorable
    graphData
  · intro vertex
    rw [GoertzelV24DeletedEdgeTrail.incidentEdgeFinset_card_eq_degree]
    exact (graphData.toRotationSystem_isCubic_iff.mp
      minimal.spherical.cubic) vertex
  · exact data.reductionJoin01_23_taitColorable_of_order
      graphData minimal horder

end

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
