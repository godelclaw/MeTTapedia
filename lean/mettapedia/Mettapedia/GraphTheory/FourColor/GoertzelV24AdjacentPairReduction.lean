import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairInsertion
import Mettapedia.GraphTheory.FourColor.GoertzelV24SquareProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24PlanarBondSpliceEuler
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedSpliceEdgeCount
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutCapGeometry
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality

namespace Mettapedia.GraphTheory.FourColor

namespace SquareReductionSide

/-- The first endpoint at each of the two seam positions.  The endpoints are
ordered along one arc of the square boundary, rather than merely choosing the
numerically first endpoint of each pair.  Thus both square reductions use the
same positive cyclic boundary order in the planar-bond constructor. -/
def leftPort (side : SquareReductionSide) (step : Fin 2) : Fin 4 :=
  if side = .join01_23 then
    if step = 0 then 1 else 2
  else
    if step = 0 then 0 else 1

/-- The matching endpoint on the oppositely ordered boundary arc. -/
def rightPort (side : SquareReductionSide) (step : Fin 2) : Fin 4 :=
  if side = .join01_23 then
    if step = 0 then 0 else 3
  else
    if step = 0 then 3 else 2

theorem leftPort_injective (side : SquareReductionSide) :
    Function.Injective side.leftPort := by
  intro first second heq
  fin_cases side <;> fin_cases first <;> fin_cases second <;>
    simp [leftPort, SquareReductionSide.join01_23] at heq ⊢

theorem rightPort_injective (side : SquareReductionSide) :
    Function.Injective side.rightPort := by
  intro first second heq
  fin_cases side <;> fin_cases first <;> fin_cases second <;>
    simp [rightPort, SquareReductionSide.join01_23] at heq ⊢

theorem leftPort_ne_rightPort (side : SquareReductionSide)
    (left right : Fin 2) :
    side.leftPort left ≠ side.rightPort right := by
  fin_cases side <;> fin_cases left <;> fin_cases right <;>
    simp [leftPort, rightPort, SquareReductionSide.join01_23]

/-- The finite profile predicate is exactly equality at the endpoints of
the two seam edges. -/
theorem compatible_iff_pair_colors
    (side : SquareReductionSide) (word : SquareBoundaryWord) :
    side.Compatible word ↔
      ∀ step : Fin 2,
        word (side.leftPort step) = word (side.rightPort step) := by
  fin_cases side
  · constructor
    · rintro ⟨hzero, hone⟩ step
      fin_cases step
      · simpa [leftPort, rightPort, SquareReductionSide.join01_23,
          SquareReductionSide.join12_30] using hzero.symm
      · simpa [leftPort, rightPort, SquareReductionSide.join01_23,
          SquareReductionSide.join12_30] using hone
    · intro h
      constructor
      · simpa [leftPort, rightPort, SquareReductionSide.join01_23,
          SquareReductionSide.join12_30] using (h (0 : Fin 2)).symm
      · simpa [leftPort, rightPort, SquareReductionSide.join01_23,
          SquareReductionSide.join12_30] using h (1 : Fin 2)
  · constructor
    · rintro ⟨hzero, hone⟩ step
      fin_cases step
      · simpa [leftPort, rightPort, SquareReductionSide.join01_23,
          SquareReductionSide.join12_30] using hone.symm
      · simpa [leftPort, rightPort, SquareReductionSide.join01_23,
          SquareReductionSide.join12_30] using hzero
    · intro h
      have hzero := h (0 : Fin 2)
      have hone := h (1 : Fin 2)
      simpa [SquareReductionSide.Compatible, leftPort, rightPort,
        SquareReductionSide.join01_23,
        SquareReductionSide.join12_30] using And.intro hone hzero.symm

end SquareReductionSide

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

open SimpleGraph
open SimpleGraphDartRotation
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FourDefectBoundary
open GoertzelV24PlanarBondSpliceEuler
open GoertzelV24RetainedSpliceEdgeCount
open GoertzelV24RetainedSpliceEdgeDecomposition
open GoertzelV24RetainedSplicePrimalGraph
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TwoEdgeCutCapGeometry
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24AdjacentPairInsertion.AdjacentPairData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance retainedVertexSetFintype (first second : V) :
    Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

local instance retainedVertexSetDecidableEq (first second : V) :
    DecidableEq (retainedVertexSet first second) :=
  Subtype.instDecidableEq

/-- Canonical-namespace spelling of the central edge used by the adjacent-pair
insertion and reduction constructions. -/
abbrev centralEdgeValue (data : AdjacentPairData G) : Sym2 V :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.centralEdgeValue data

/-- Canonical-namespace spelling of a boundary edge value. -/
abbrev boundaryEdgeValue (data : AdjacentPairData G) (port : Fin 4) : Sym2 V :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdgeValue data port

/-- Canonical-namespace spelling of the deleted endpoint of a boundary
edge. -/
abbrev boundaryDeletedVertex (data : AdjacentPairData G) (port : Fin 4) : V :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryDeletedVertex
    data port

/-- Canonical-namespace spelling of a boundary edge. -/
abbrev boundaryEdge (data : AdjacentPairData G) (port : Fin 4) : G.edgeSet :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdge data port

/-- Canonical-namespace spelling of the induced-edge embedding into the
ambient graph. -/
abbrev retainedEdgeToAmbientEdge
    (data : AdjacentPairData G)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) : G.edgeSet :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.retainedEdgeToAmbientEdge
    data edge

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem boundaryEdgeValue_eq (data : AdjacentPairData G) (port : Fin 4) :
    data.boundaryEdgeValue port =
      s(data.boundaryDeletedVertex port, data.portVertex port) :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdgeValue_eq
    data port

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem portVertex_mem_boundaryEdgeValue
    (data : AdjacentPairData G) (port : Fin 4) :
    data.portVertex port ∈ (data.boundaryEdgeValue port : Sym2 V) :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.portVertex_mem_boundaryEdgeValue
    data port

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem boundaryEdgeValue_injective (data : AdjacentPairData G) :
    Function.Injective data.boundaryEdgeValue :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdgeValue_injective
    data

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem portVertex_ne (data : AdjacentPairData G) {first second : Fin 4}
    (hne : first ≠ second) :
    data.portVertex first ≠ data.portVertex second :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.portVertex_ne data hne

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem edge_eq_central_or_firstPort_of_mem
    (data : AdjacentPairData G) (edge : G.edgeSet)
    (hfirst : data.firstVertex ∈ (edge.1 : Sym2 V)) :
    edge.1 = s(data.firstVertex, data.secondVertex) ∨
      edge.1 = s(data.firstVertex, data.portVertex 0) ∨
      edge.1 = s(data.firstVertex, data.portVertex 1) :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.edge_eq_central_or_firstPort_of_mem
    data edge hfirst

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem edge_eq_central_or_secondPort_of_mem
    (data : AdjacentPairData G) (edge : G.edgeSet)
    (hsecond : data.secondVertex ∈ (edge.1 : Sym2 V)) :
    edge.1 = s(data.firstVertex, data.secondVertex) ∨
      edge.1 = s(data.secondVertex, data.portVertex 2) ∨
      edge.1 = s(data.secondVertex, data.portVertex 3) :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.edge_eq_central_or_secondPort_of_mem
    data edge hsecond

/-- The two vertices removed by adjacent-pair reduction. -/
def deletedVertices (data : AdjacentPairData G) : Finset V :=
  {data.firstVertex, data.secondVertex}

/-- All four edges exposed by deleting the adjacent pair. -/
def boundaryEdgeSet (data : AdjacentPairData G) : Finset G.edgeSet :=
  Finset.univ.image data.boundaryEdge

/-- The left ordered transversal for one of the two square reductions. -/
def leftCrossing (data : AdjacentPairData G)
    (side : SquareReductionSide) (step : Fin 2) : G.edgeSet :=
  data.boundaryEdge (side.leftPort step)

/-- The right ordered transversal for one of the two square reductions. -/
def rightCrossing (data : AdjacentPairData G)
    (side : SquareReductionSide) (step : Fin 2) : G.edgeSet :=
  data.boundaryEdge (side.rightPort step)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem boundaryEdge_injective (data : AdjacentPairData G) :
    Function.Injective data.boundaryEdge := by
  intro first second hedge
  apply data.boundaryEdgeValue_injective
  exact congrArg Subtype.val hedge

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem leftCrossing_injective (data : AdjacentPairData G)
    (side : SquareReductionSide) :
    Function.Injective (data.leftCrossing side) := by
  intro first second hedge
  apply side.leftPort_injective
  exact data.boundaryEdge_injective hedge

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem rightCrossing_injective (data : AdjacentPairData G)
    (side : SquareReductionSide) :
    Function.Injective (data.rightCrossing side) := by
  intro first second hedge
  apply side.rightPort_injective
  exact data.boundaryEdge_injective hedge

omit [Fintype V] [DecidableRel G.Adj] in
/-- The two ordered transversals enumerate all four boundary edges. -/
theorem pairedCut_union_boundaryEdgeSet
    (data : AdjacentPairData G) (side : SquareReductionSide) :
    orderedCut (data.leftCrossing side) ∪
        orderedCut (data.rightCrossing side) =
      data.boundaryEdgeSet := by
  apply Finset.Subset.antisymm
  · intro edge hedge
    rw [Finset.mem_union] at hedge
    rw [boundaryEdgeSet, Finset.mem_image]
    rcases hedge with hleft | hright
    · rcases Finset.mem_image.mp hleft with ⟨step, _, rfl⟩
      exact ⟨side.leftPort step, Finset.mem_univ _, rfl⟩
    · rcases Finset.mem_image.mp hright with ⟨step, _, rfl⟩
      exact ⟨side.rightPort step, Finset.mem_univ _, rfl⟩
  · intro edge hedge
    rw [boundaryEdgeSet, Finset.mem_image] at hedge
    rcases hedge with ⟨port, _, rfl⟩
    fin_cases side <;> fin_cases port <;>
      simp [orderedCut, leftCrossing, rightCrossing,
        SquareReductionSide.leftPort, SquareReductionSide.rightPort,
        SquareReductionSide.join01_23]

omit [Fintype V] [DecidableRel G.Adj] in
/-- No boundary edge occurs on both transversals. -/
theorem pairedCuts_disjoint
    (data : AdjacentPairData G) (side : SquareReductionSide) :
    Disjoint (orderedCut (data.leftCrossing side))
      (orderedCut (data.rightCrossing side)) := by
  rw [Finset.disjoint_left]
  intro edge hleft hright
  rcases Finset.mem_image.mp hleft with ⟨left, _, hleft⟩
  rcases Finset.mem_image.mp hright with ⟨right, _, hright⟩
  apply side.leftPort_ne_rightPort left right
  apply data.boundaryEdge_injective
  exact hleft.trans hright.symm

omit [Fintype V] [DecidableRel G.Adj] in
/-- Each exposed edge really crosses from the deleted pair to its retained
port vertex. -/
theorem boundaryEdge_crosses_deletedVertices
    (data : AdjacentPairData G) (port : Fin 4) :
    EdgeCrossesVertexSide G
      (fun vertex ↦ vertex ∈ data.deletedVertices)
      (data.boundaryEdge port) := by
  refine ⟨data.boundaryDeletedVertex port, data.portVertex port, ?_, ?_, ?_, ?_⟩
  · change data.boundaryDeletedVertex port ∈
      (data.boundaryEdgeValue port : Sym2 V)
    rw [data.boundaryEdgeValue_eq]
    simp
  · exact data.portVertex_mem_boundaryEdgeValue port
  · fin_cases port <;>
      simp [deletedVertices,
        GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryDeletedVertex]
  · simp only [deletedVertices, Finset.mem_insert, Finset.mem_singleton]
    rintro (hfirst | hsecond)
    · exact data.portNeFirst port hfirst
    · exact data.portNeSecond port hsecond

omit [Fintype V] [DecidableRel G.Adj] in
/-- Conversely, the only edges crossing the deleted adjacent pair are the
four explicitly named boundary edges. -/
theorem edgeCrosses_deletedVertices_iff_exists_boundaryEdge
    (data : AdjacentPairData G) (edge : G.edgeSet) :
    EdgeCrossesVertexSide G
        (fun vertex ↦ vertex ∈ data.deletedVertices) edge ↔
      ∃ port : Fin 4, edge = data.boundaryEdge port := by
  constructor
  · rintro ⟨inner, outer, hinner, houter, hinnerDeleted,
      houterRetained⟩
    simp only [deletedVertices, Finset.mem_insert,
      Finset.mem_singleton] at hinnerDeleted
    rcases hinnerDeleted with rfl | rfl
    · rcases data.edge_eq_central_or_firstPort_of_mem edge hinner with
        hcentral | hzero | hone
      · exfalso
        apply houterRetained
        simpa [deletedVertices, centralEdgeValue, hcentral] using houter
      · exact ⟨0, Subtype.ext (by simpa using hzero)⟩
      · exact ⟨1, Subtype.ext (by simpa using hone)⟩
    · rcases data.edge_eq_central_or_secondPort_of_mem edge hinner with
        hcentral | htwo | hthree
      · exfalso
        apply houterRetained
        simpa [deletedVertices, centralEdgeValue, hcentral] using houter
      · exact ⟨2, Subtype.ext (by simpa using htwo)⟩
      · exact ⟨3, Subtype.ext (by simpa using hthree)⟩
  · rintro ⟨port, rfl⟩
    exact data.boundaryEdge_crosses_deletedVertices port

/-- The explicitly named four-edge set is the endpoint-computed crossing
set of the graph-backed rotation system. -/
theorem boundaryEdgeSet_eq_vertexSetCrossingEdges
    (graphData : Data G) (data : AdjacentPairData G) :
    data.boundaryEdgeSet =
      vertexSetCrossingEdges graphData.toRotationSystem
        data.deletedVertices := by
  ext edge
  rw [mem_simpleGraph_vertexSetCrossingEdges_iff graphData
    data.deletedVertices edge]
  simp only [boundaryEdgeSet, Finset.mem_image, Finset.mem_univ, true_and]
  rw [data.edgeCrosses_deletedVertices_iff_exists_boundaryEdge]
  constructor
  · rintro ⟨port, hport⟩
    exact ⟨port, hport.symm⟩
  · rintro ⟨port, hport⟩
    exact ⟨port, hport.symm⟩

/-- Either square pairing presents the complete computed four-edge cut. -/
theorem pairedCut_boundary
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide) :
    orderedCut (data.leftCrossing side) ∪
        orderedCut (data.rightCrossing side) =
      vertexSetCrossingEdges graphData.toRotationSystem
        data.deletedVertices := by
  rw [data.pairedCut_union_boundaryEdgeSet,
    data.boundaryEdgeSet_eq_vertexSetCrossingEdges]

/-- A surviving dart used solely to root the shortened rotation system. -/
def retainedRoot (data : AdjacentPairData G) : G.Dart :=
  ⟨(data.portVertex 0, data.firstVertex), data.first_adj_port_zero.symm⟩

/-- Rerooting places the distinguished dart outside the deleted pair without
changing the embedded graph or any unpointed structural invariant. -/
def rootedGraphData (graphData : Data G) (data : AdjacentPairData G) :
    Data G :=
  graphDataWithOuter graphData data.retainedRoot

/-- The ambient rotation system with its root moved to a retained port. -/
abbrev rootedRotationSystem
    (graphData : Data G) (data : AdjacentPairData G) :=
  (data.rootedGraphData graphData).toRotationSystem

theorem outer_retained
    (graphData : Data G) (data : AdjacentPairData G) :
    deletedRegionKeep data.deletedVertices
      ((data.rootedRotationSystem graphData).vertOf
        (data.rootedRotationSystem graphData).outer) := by
  change data.portVertex 0 ∉ data.deletedVertices
  simp only [deletedVertices, Finset.mem_insert, Finset.mem_singleton]
  rintro (hfirst | hsecond)
  · exact data.portNeFirst 0 hfirst
  · exact data.portNeSecond 0 hsecond

/-- The computed cut boundary supplies the outward orientations of the left
transversal. -/
def leftCrosses
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide) :=
  leftCrossing_outward (data.rootedRotationSystem graphData)
    data.deletedVertices (data.leftCrossing side)
    (data.rightCrossing side)
    (data.pairedCut_boundary (data.rootedGraphData graphData) side)

/-- The computed cut boundary supplies the outward orientations of the right
transversal. -/
def rightCrosses
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide) :=
  rightCrossing_outward (data.rootedRotationSystem graphData)
    data.deletedVertices (data.leftCrossing side)
    (data.rightCrossing side)
    (data.pairedCut_boundary (data.rootedGraphData graphData) side)

/-- Every exposed retained dart occurs on one of the two paired
transversals. -/
def boundaryCover
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide) :=
  deletedRegionBoundaryCover (data.rootedRotationSystem graphData)
    data.deletedVertices (data.leftCrossing side)
    (data.rightCrossing side)
    (data.pairedCut_boundary (data.rootedGraphData graphData) side)

/-- The retained endpoint of an oriented boundary edge is its named port. -/
theorem orderedBoundaryDart_vertex_eq_port
    (graphData : Data G) (data : AdjacentPairData G)
    (crossing : Fin n → G.edgeSet)
    (hcrosses : ∀ step, ∃ dart : (data.rootedRotationSystem graphData).D,
      (data.rootedRotationSystem graphData).edgeOf dart = crossing step ∧
      deletedRegionKeep data.deletedVertices
        ((data.rootedRotationSystem graphData).vertOf dart) ∧
      ¬ deletedRegionKeep data.deletedVertices
        ((data.rootedRotationSystem graphData).vertOf
          ((data.rootedRotationSystem graphData).alpha dart)))
    (step : Fin n) (port : Fin 4)
    (hedge : crossing step = data.boundaryEdge port) :
    (data.rootedRotationSystem graphData).vertOf
        (orderedBoundaryDart (data.rootedRotationSystem graphData)
          (deletedRegionKeep data.deletedVertices) crossing hcrosses
          step).1.1.1 =
      data.portVertex port := by
  let dart := orderedBoundaryDart (data.rootedRotationSystem graphData)
    (deletedRegionKeep data.deletedVertices) crossing hcrosses step
  have hdartEndpoint :
      (data.rootedRotationSystem graphData).vertOf dart.1.1.1 ∈
        (data.rootedRotationSystem graphData).endpoints
          ((data.rootedRotationSystem graphData).edgeOf dart.1.1.1) := by
    apply (data.rootedRotationSystem graphData).mem_endpoints_iff.2
    exact ⟨dart.1.1.1,
      (data.rootedRotationSystem graphData).mem_dartsOn.2 rfl, rfl⟩
  have hdartEdge :
      (data.rootedRotationSystem graphData).edgeOf dart.1.1.1 =
        data.boundaryEdge port := by
    rw [orderedBoundaryDart_edgeOf, hedge]
  have hdartEndpoint' :
      (data.rootedRotationSystem graphData).vertOf dart.1.1.1 ∈
        (data.rootedRotationSystem graphData).endpoints
          (data.boundaryEdge port) := by
    rw [← hdartEdge]
    exact hdartEndpoint
  have hmem :
      (data.rootedRotationSystem graphData).vertOf dart.1.1.1 ∈
        (data.boundaryEdge port : Sym2 V) :=
    (mem_simpleGraphRotationSystem_endpoints_iff
      (data.rootedGraphData graphData) (data.boundaryEdge port)
      ((data.rootedRotationSystem graphData).vertOf dart.1.1.1)).1
        hdartEndpoint'
  have hcases :
      (data.rootedRotationSystem graphData).vertOf dart.1.1.1 =
          data.boundaryDeletedVertex port ∨
        (data.rootedRotationSystem graphData).vertOf dart.1.1.1 =
          data.portVertex port := by
    simpa [boundaryEdge, data.boundaryEdgeValue_eq] using hmem
  rcases hcases with hdeleted | hport
  · exfalso
    have hdeletedMem : data.boundaryDeletedVertex port ∈
        data.deletedVertices := by
      fin_cases port <;>
        simp [deletedVertices,
          GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryDeletedVertex]
    exact dart.1.1.2 (hdeleted.symm ▸ hdeletedMem)
  · exact hport

theorem leftBoundaryDart_vertex
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide) (step : Fin 2) :
    (data.rootedRotationSystem graphData).vertOf
        (orderedBoundaryDart (data.rootedRotationSystem graphData)
          (deletedRegionKeep data.deletedVertices)
          (data.leftCrossing side)
          (data.leftCrosses graphData side) step).1.1.1 =
      data.portVertex (side.leftPort step) := by
  apply data.orderedBoundaryDart_vertex_eq_port graphData
    (data.leftCrossing side) (data.leftCrosses graphData side)
    step (side.leftPort step)
  rfl

theorem rightBoundaryDart_vertex
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide) (step : Fin 2) :
    (data.rootedRotationSystem graphData).vertOf
        (orderedBoundaryDart (data.rootedRotationSystem graphData)
          (deletedRegionKeep data.deletedVertices)
          (data.rightCrossing side)
          (data.rightCrosses graphData side) step).1.1.1 =
      data.portVertex (side.rightPort step) := by
  apply data.orderedBoundaryDart_vertex_eq_port graphData
    (data.rightCrossing side) (data.rightCrosses graphData side)
    step (side.rightPort step)
  rfl

/-- Pairwise distinct ports discharge the no-loop condition for both new
seam edges. -/
theorem seamEndpoints
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide) (step : Fin 2) :
    (data.rootedRotationSystem graphData).vertOf
        (orderedBoundaryDart (data.rootedRotationSystem graphData)
          (deletedRegionKeep data.deletedVertices)
          (data.leftCrossing side)
          (data.leftCrosses graphData side) step).1.1.1 ≠
      (data.rootedRotationSystem graphData).vertOf
        (orderedBoundaryDart (data.rootedRotationSystem graphData)
          (deletedRegionKeep data.deletedVertices)
          (data.rightCrossing side)
          (data.rightCrosses graphData side) step).1.1.1 := by
  rw [data.leftBoundaryDart_vertex, data.rightBoundaryDart_vertex]
  exact data.portVertex_ne (side.leftPort_ne_rightPort step step)

/-- Delete the adjacent pair and join its four exposed half-edges according
to one of the two standard square reductions. This is an ordinary rotation
system on the surviving vertices; parallel edges are permitted, loops are
not. -/
def reductionRotationSystem
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide) :=
  orderedCutRetainedVertexRotationSystem
    (data.rootedRotationSystem graphData)
    (deletedRegionKeep data.deletedVertices)
    (data.leftCrossing side) (data.rightCrossing side)
    (data.leftCrosses graphData side) (data.rightCrosses graphData side)
    (data.leftCrossing_injective side)
    (data.rightCrossing_injective side)
    (data.boundaryCover graphData side) (data.pairedCuts_disjoint side)
    (data.outer_retained graphData) (data.seamEndpoints graphData side)

/-- A vertex of the induced adjacent-pair deletion, regarded as a retained
vertex of either square reduction. -/
def reductionVertexOfDeletedVertex
    (data : AdjacentPairData G)
    (vertex : retainedVertexSet data.firstVertex data.secondVertex) :
    RetainedVertex (deletedRegionKeep data.deletedVertices) :=
  ⟨vertex.1, by
    change vertex.1 ∉ data.deletedVertices
    simp only [deletedVertices, Finset.mem_insert, Finset.mem_singleton]
    rintro (hfirst | hsecond)
    · exact vertex.2.1 hfirst
    · exact vertex.2.2 hsecond⟩

omit [Fintype V] [DecidableRel G.Adj] in
@[simp]
theorem reductionVertexOfDeletedVertex_val
    (data : AdjacentPairData G)
    (vertex : retainedVertexSet data.firstVertex data.secondVertex) :
    (data.reductionVertexOfDeletedVertex vertex).1 = vertex.1 :=
  rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Embedding an edge of the induced deletion back into the ambient graph is
injective. -/
theorem retainedEdgeToAmbientEdge_injective
    (data : AdjacentPairData G) :
    Function.Injective data.retainedEdgeToAmbientEdge := by
  exact
    (GoertzelV24AdjacentPairInsertion.AdjacentPairData.retainedGraphEmbedding
      data).mapEdgeSet.injective

/-- The selected ambient representative of a deleted-graph edge has both
ends on the retained side. -/
def retainedEdgeInternalDart
    (graphData : Data G) (data : AdjacentPairData G)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) :
    InternalDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices) := by
  let RS := data.rootedRotationSystem graphData
  let ambient := data.retainedEdgeToAmbientEdge edge
  let dart := RS.dartRepresentative ambient
  have hdartEdge : RS.edgeOf dart = ambient :=
    RS.dartRepresentative_edgeOf ambient
  have endpointKeep : ∀ vertex : V,
      vertex ∈ (ambient.1 : Sym2 V) →
        deletedRegionKeep data.deletedVertices vertex := by
    intro vertex hvertex
    have hmapped : vertex ∈ edge.1.map Subtype.val := by
      simpa [ambient] using hvertex
    rcases Sym2.mem_map.mp hmapped with ⟨retained, _hretained, hvalue⟩
    subst vertex
    exact data.reductionVertexOfDeletedVertex retained |>.2
  refine ⟨⟨dart, endpointKeep _ ?_⟩, endpointKeep _ ?_⟩
  · apply (mem_simpleGraphRotationSystem_endpoints_iff
      (data.rootedGraphData graphData) ambient _).1
    apply RS.mem_endpoints_iff.2
    exact ⟨dart, RS.mem_dartsOn.2 hdartEdge, rfl⟩
  · apply (mem_simpleGraphRotationSystem_endpoints_iff
      (data.rootedGraphData graphData) ambient _).1
    apply RS.mem_endpoints_iff.2
    exact ⟨RS.alpha dart, RS.mem_dartsOn.2 (RS.edge_alpha dart |>.trans hdartEdge),
      rfl⟩

@[simp]
theorem retainedEdgeInternalDart_edgeOf
    (graphData : Data G) (data : AdjacentPairData G)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) :
    (data.rootedRotationSystem graphData).edgeOf
        (data.retainedEdgeInternalDart graphData edge).1.1 =
      data.retainedEdgeToAmbientEdge edge := by
  simp only [retainedEdgeInternalDart]
  exact (data.rootedRotationSystem graphData).dartRepresentative_edgeOf _

/-- The rewired-dart presentation underlying one adjacent-pair square
reduction. -/
abbrev reductionRewiredDartSystem
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide) :=
  orderedCutRetainedVertexRewiredDartSystem
    (data.rootedRotationSystem graphData)
    (deletedRegionKeep data.deletedVertices)
    (data.leftCrossing side) (data.rightCrossing side)
    (data.leftCrosses graphData side) (data.rightCrosses graphData side)
    (data.leftCrossing_injective side)
    (data.rightCrossing_injective side)
    (data.boundaryCover graphData side) (data.pairedCuts_disjoint side)
    (data.outer_retained graphData) (data.seamEndpoints graphData side)

/-- An old edge of the induced deletion, as an internal edge of a square
reduction. -/
def reductionEdgeOfDeletedEdge
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) :
    (data.reductionRewiredDartSystem graphData side).Edge :=
  retainedInternalSpliceEdge
    (data.rootedRotationSystem graphData)
    (deletedRegionKeep data.deletedVertices)
    (data.leftCrossing side) (data.rightCrossing side)
    (data.leftCrosses graphData side) (data.rightCrosses graphData side)
    (data.leftCrossing_injective side)
    (data.rightCrossing_injective side)
    (data.boundaryCover graphData side) (data.pairedCuts_disjoint side)
    (data.outer_retained graphData) (data.seamEndpoints graphData side)
    (data.retainedEdgeInternalDart graphData edge)

/-- The new seam edge at one of the two positions of a square reduction. -/
def reductionSeamEdge
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide) (step : Fin 2) :
    (data.reductionRewiredDartSystem graphData side).Edge :=
  orderedCutSeamSpliceEdge
    (data.rootedRotationSystem graphData)
    (deletedRegionKeep data.deletedVertices)
    (data.leftCrossing side) (data.rightCrossing side)
    (data.leftCrosses graphData side) (data.rightCrosses graphData side)
    (data.leftCrossing_injective side)
    (data.rightCrossing_injective side)
    (data.boundaryCover graphData side) (data.pairedCuts_disjoint side)
    (data.outer_retained graphData) (data.seamEndpoints graphData side) step

theorem reductionEdgeOfDeletedEdge_injective
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide) :
    Function.Injective (data.reductionEdgeOfDeletedEdge graphData side) := by
  intro first second hedge
  apply data.retainedEdgeToAmbientEdge_injective
  rw [← data.retainedEdgeInternalDart_edgeOf graphData first,
    ← data.retainedEdgeInternalDart_edgeOf graphData second]
  exact (retainedInternalSpliceEdge_eq_iff
    (data.rootedRotationSystem graphData)
    (deletedRegionKeep data.deletedVertices)
    (data.leftCrossing side) (data.rightCrossing side)
    (data.leftCrosses graphData side) (data.rightCrosses graphData side)
    (data.leftCrossing_injective side)
    (data.rightCrossing_injective side)
    (data.boundaryCover graphData side) (data.pairedCuts_disjoint side)
    (data.outer_retained graphData) (data.seamEndpoints graphData side)
    (data.retainedEdgeInternalDart graphData first)
    (data.retainedEdgeInternalDart graphData second)).1 hedge

theorem reductionEdgeOfDeletedEdge_ne_reductionSeamEdge
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) (step : Fin 2) :
    data.reductionEdgeOfDeletedEdge graphData side edge ≠
      data.reductionSeamEdge graphData side step :=
  retainedInternalSpliceEdge_ne_orderedCutSeamSpliceEdge
    (data.rootedRotationSystem graphData)
    (deletedRegionKeep data.deletedVertices)
    (data.leftCrossing side) (data.rightCrossing side)
    (data.leftCrosses graphData side) (data.rightCrosses graphData side)
    (data.leftCrossing_injective side)
    (data.rightCrossing_injective side)
    (data.boundaryCover graphData side) (data.pairedCuts_disjoint side)
    (data.outer_retained graphData) (data.seamEndpoints graphData side)
    (data.retainedEdgeInternalDart graphData edge) step

/-- Endpoint incidence of a deleted-graph edge is preserved by its internal
edge in either square reduction. -/
theorem reductionVertex_mem_endpoints_reductionEdgeOfDeletedEdge
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (vertex : retainedVertexSet data.firstVertex data.secondVertex)
    (hvertex : vertex ∈ (edge.1 : Sym2 _)) :
    data.reductionVertexOfDeletedVertex vertex ∈
      (data.reductionRotationSystem graphData side).endpoints
        (data.reductionEdgeOfDeletedEdge graphData side edge) := by
  unfold reductionRotationSystem reductionEdgeOfDeletedEdge
  rw [endpoints_retainedInternalSpliceEdge
    (data.rootedRotationSystem graphData)
    (deletedRegionKeep data.deletedVertices)
    (data.leftCrossing side) (data.rightCrossing side)
    (data.leftCrosses graphData side) (data.rightCrosses graphData side)
    (data.leftCrossing_injective side)
    (data.rightCrossing_injective side)
    (data.boundaryCover graphData side) (data.pairedCuts_disjoint side)
    (data.outer_retained graphData) (data.seamEndpoints graphData side)
    (data.retainedEdgeInternalDart graphData edge)]
  have hambientSym : vertex.1 ∈
      ((data.retainedEdgeToAmbientEdge edge).1 : Sym2 V) := by
    change vertex.1 ∈ edge.1.map Subtype.val
    exact Sym2.mem_map.mpr ⟨vertex, hvertex, rfl⟩
  have hambientEndpoints : vertex.1 ∈
      (data.rootedRotationSystem graphData).endpoints
        ((data.rootedRotationSystem graphData).edgeOf
          (data.retainedEdgeInternalDart graphData edge).1.1) := by
    rw [data.retainedEdgeInternalDart_edgeOf graphData edge]
    exact (mem_simpleGraphRotationSystem_endpoints_iff
      (data.rootedGraphData graphData)
      (data.retainedEdgeToAmbientEdge edge) vertex.1).2 hambientSym
  have himage : vertex.1 ∈
      (retainedInternalEndpointPair
        (data.rootedRotationSystem graphData)
        (deletedRegionKeep data.deletedVertices)
        (data.retainedEdgeInternalDart graphData edge)).image Subtype.val := by
    rw [image_val_retainedInternalEndpointPair]
    exact hambientEndpoints
  rcases Finset.mem_image.mp himage with ⟨retained, hretained, hvalue⟩
  have heq : retained = data.reductionVertexOfDeletedVertex vertex := by
    apply Subtype.ext
    exact hvalue
  simpa [heq] using hretained

/-- Restrict a coloring of a square reduction to the unchanged edges of the
induced adjacent-pair deletion. -/
def reductionDeletedColoring
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide)
    (C : (data.reductionRotationSystem graphData side).EdgeColoring Color) :
    (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color :=
  SimpleGraph.Coloring.mk
    (fun edge ↦ C (data.reductionEdgeOfDeletedEdge graphData side edge)) <| by
      intro first second hadjacent
      rcases (SimpleGraph.lineGraph_adj_iff_exists).1 hadjacent with
        ⟨hne, vertex, hfirst, hsecond⟩
      apply C.valid
      apply (data.reductionRotationSystem graphData side).edgeAdjacencyGraph_adj_iff.2
      exact ⟨(data.reductionEdgeOfDeletedEdge_injective graphData side).ne hne,
        data.reductionVertexOfDeletedVertex vertex,
        data.reductionVertex_mem_endpoints_reductionEdgeOfDeletedEdge
          graphData side first vertex hfirst,
        data.reductionVertex_mem_endpoints_reductionEdgeOfDeletedEdge
          graphData side second vertex hsecond⟩

@[simp]
theorem reductionDeletedColoring_apply
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide)
    (C : (data.reductionRotationSystem graphData side).EdgeColoring Color)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) :
    data.reductionDeletedColoring graphData side C edge =
      C (data.reductionEdgeOfDeletedEdge graphData side edge) :=
  rfl

/-- Nonzero colors remain nonzero when the seam edges are forgotten. -/
theorem reductionDeletedColoring_isTait
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide)
    (C : (data.reductionRotationSystem graphData side).EdgeColoring Color)
    (hC : (data.reductionRotationSystem graphData side).IsTaitEdgeColoring C) :
    IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
      (data.reductionDeletedColoring graphData side C) := by
  intro edge
  exact hC (data.reductionEdgeOfDeletedEdge graphData side edge)

/-- The left named port is an endpoint of its newly inserted seam edge. -/
theorem reductionLeftPort_mem_endpoints_reductionSeamEdge
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide) (step : Fin 2) :
    data.reductionVertexOfDeletedVertex
        (data.retainedPort (side.leftPort step)) ∈
      (data.reductionRotationSystem graphData side).endpoints
        (data.reductionSeamEdge graphData side step) := by
  unfold reductionRotationSystem reductionSeamEdge
  rw [endpoints_orderedCutSeamSpliceEdge
    (data.rootedRotationSystem graphData)
    (deletedRegionKeep data.deletedVertices)
    (data.leftCrossing side) (data.rightCrossing side)
    (data.leftCrosses graphData side) (data.rightCrosses graphData side)
    (data.leftCrossing_injective side)
    (data.rightCrossing_injective side)
    (data.boundaryCover graphData side) (data.pairedCuts_disjoint side)
    (data.outer_retained graphData) (data.seamEndpoints graphData side) step]
  apply Finset.mem_insert.mpr
  left
  apply Subtype.ext
  exact (data.leftBoundaryDart_vertex graphData side step).symm

/-- The right named port is the other endpoint of its newly inserted seam
edge. -/
theorem reductionRightPort_mem_endpoints_reductionSeamEdge
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide) (step : Fin 2) :
    data.reductionVertexOfDeletedVertex
        (data.retainedPort (side.rightPort step)) ∈
      (data.reductionRotationSystem graphData side).endpoints
        (data.reductionSeamEdge graphData side step) := by
  unfold reductionRotationSystem reductionSeamEdge
  rw [endpoints_orderedCutSeamSpliceEdge
    (data.rootedRotationSystem graphData)
    (deletedRegionKeep data.deletedVertices)
    (data.leftCrossing side) (data.rightCrossing side)
    (data.leftCrosses graphData side) (data.rightCrosses graphData side)
    (data.leftCrossing_injective side)
    (data.rightCrossing_injective side)
    (data.boundaryCover graphData side) (data.pairedCuts_disjoint side)
    (data.outer_retained graphData) (data.seamEndpoints graphData side) step]
  apply Finset.mem_insert.mpr
  right
  apply Finset.mem_singleton.mpr
  apply Subtype.ext
  exact (data.rightBoundaryDart_vertex graphData side step).symm

/-- Among the three nonzero Klein-four colors, the color distinct from two
distinct given colors is their sum. -/
private theorem add_eq_of_three_nonzero_pairwise_distinct :
    ∀ first second third : Color,
      first ≠ 0 → second ≠ 0 → third ≠ 0 →
      first ≠ second → third ≠ first → third ≠ second →
      first + second = third := by
  decide

/-- At any port incident with a new seam edge, the missing color of the
two-edge deletion is exactly the seam color. -/
theorem degreeTwoBoundaryColorWord_eq_reductionSeamColor_of_port
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (side : SquareReductionSide)
    (C : (data.reductionRotationSystem graphData side).EdgeColoring Color)
    (hC : (data.reductionRotationSystem graphData side).IsTaitEdgeColoring C)
    (port : Fin 4) (step : Fin 2)
    (hseamEndpoint :
      data.reductionVertexOfDeletedVertex (data.retainedPort port) ∈
        (data.reductionRotationSystem graphData side).endpoints
          (data.reductionSeamEdge graphData side step)) :
    data.degreeTwoBoundaryData.colorWord
        (data.reductionDeletedColoring graphData side C) port =
      C (data.reductionSeamEdge graphData side step) := by
  let deleted := DeletedAdjacentPairGraph G data.firstVertex data.secondVertex
  let deletedColoring := data.reductionDeletedColoring graphData side C
  have holdCard :=
    (data.degreeTwoBoundaryData_wellFormed hcubic).2.1 port
  have hcard :
      (incidentEdgeFinset deleted (data.retainedPort port)).card = 2 := by
    convert holdCard using 1
    apply congrArg Finset.card
    ext edge
    constructor
    · intro hedge
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hedge).2⟩
    · intro hedge
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hedge).2⟩
  rcases Finset.card_eq_two.mp hcard with
    ⟨first, second, hne, hincident⟩
  have hfirstMem : first ∈
      incidentEdgeFinset deleted (data.retainedPort port) := by
    rw [hincident]
    exact Finset.mem_insert_self first {second}
  have hsecondMem : second ∈
      incidentEdgeFinset deleted (data.retainedPort port) := by
    rw [hincident]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self second)
  have hfirstEndpoint : data.retainedPort port ∈ (first.1 : Sym2 _) := by
    exact (Finset.mem_filter.mp hfirstMem).2
  have hsecondEndpoint : data.retainedPort port ∈ (second.1 : Sym2 _) := by
    exact (Finset.mem_filter.mp hsecondMem).2
  have hdeletedTait : IsTaitEdgeColoring deleted deletedColoring :=
    data.reductionDeletedColoring_isTait graphData side C hC
  have hfirstSecond : deletedColoring first ≠ deletedColoring second := by
    apply deletedColoring.valid
    apply (SimpleGraph.lineGraph_adj_iff_exists).2
    exact ⟨hne, data.retainedPort port, hfirstEndpoint, hsecondEndpoint⟩
  have hseamFirst :
      C (data.reductionSeamEdge graphData side step) ≠
        deletedColoring first := by
    change C (data.reductionSeamEdge graphData side step) ≠
      C (data.reductionEdgeOfDeletedEdge graphData side first)
    apply C.valid
    apply (data.reductionRotationSystem graphData side).edgeAdjacencyGraph_adj_iff.2
    exact ⟨(data.reductionEdgeOfDeletedEdge_ne_reductionSeamEdge
        graphData side first step).symm,
      data.reductionVertexOfDeletedVertex (data.retainedPort port),
      hseamEndpoint,
      data.reductionVertex_mem_endpoints_reductionEdgeOfDeletedEdge
        graphData side first (data.retainedPort port) hfirstEndpoint⟩
  have hseamSecond :
      C (data.reductionSeamEdge graphData side step) ≠
        deletedColoring second := by
    change C (data.reductionSeamEdge graphData side step) ≠
      C (data.reductionEdgeOfDeletedEdge graphData side second)
    apply C.valid
    apply (data.reductionRotationSystem graphData side).edgeAdjacencyGraph_adj_iff.2
    exact ⟨(data.reductionEdgeOfDeletedEdge_ne_reductionSeamEdge
        graphData side second step).symm,
      data.reductionVertexOfDeletedVertex (data.retainedPort port),
      hseamEndpoint,
      data.reductionVertex_mem_endpoints_reductionEdgeOfDeletedEdge
        graphData side second (data.retainedPort port) hsecondEndpoint⟩
  have hsum : deletedColoring first + deletedColoring second =
      C (data.reductionSeamEdge graphData side step) :=
    add_eq_of_three_nonzero_pairwise_distinct
      (deletedColoring first) (deletedColoring second)
      (C (data.reductionSeamEdge graphData side step))
      (hdeletedTait first) (hdeletedTait second)
      (hC (data.reductionSeamEdge graphData side step))
      hfirstSecond hseamFirst hseamSecond
  change vertexKirchhoffSum deleted deletedColoring
      (data.retainedPort port) = _
  unfold vertexKirchhoffSum
  rw [hincident]
  have hnot : first ∉ ({second} : Finset _) := by
    intro hmem
    exact hne (Finset.mem_singleton.mp hmem)
  rw [Finset.sum_insert hnot, Finset.sum_singleton]
  exact hsum

theorem degreeTwoBoundaryColorWord_leftPort_eq_reductionSeamColor
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (side : SquareReductionSide)
    (C : (data.reductionRotationSystem graphData side).EdgeColoring Color)
    (hC : (data.reductionRotationSystem graphData side).IsTaitEdgeColoring C)
    (step : Fin 2) :
    data.degreeTwoBoundaryData.colorWord
        (data.reductionDeletedColoring graphData side C)
        (side.leftPort step) =
      C (data.reductionSeamEdge graphData side step) :=
  data.degreeTwoBoundaryColorWord_eq_reductionSeamColor_of_port
    graphData hcubic side C hC (side.leftPort step) step
    (data.reductionLeftPort_mem_endpoints_reductionSeamEdge
      graphData side step)

theorem degreeTwoBoundaryColorWord_rightPort_eq_reductionSeamColor
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (side : SquareReductionSide)
    (C : (data.reductionRotationSystem graphData side).EdgeColoring Color)
    (hC : (data.reductionRotationSystem graphData side).IsTaitEdgeColoring C)
    (step : Fin 2) :
    data.degreeTwoBoundaryData.colorWord
        (data.reductionDeletedColoring graphData side C)
        (side.rightPort step) =
      C (data.reductionSeamEdge graphData side step) :=
  data.degreeTwoBoundaryColorWord_eq_reductionSeamColor_of_port
    graphData hcubic side C hC (side.rightPort step) step
    (data.reductionRightPort_mem_endpoints_reductionSeamEdge
      graphData side step)

/-- A Tait coloring of a paired cap restricts to a deletion coloring whose
four-port word realizes exactly that cap pairing. -/
theorem reductionDeletedColorWord_compatible
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (side : SquareReductionSide)
    (C : (data.reductionRotationSystem graphData side).EdgeColoring Color)
    (hC : (data.reductionRotationSystem graphData side).IsTaitEdgeColoring C) :
    side.Compatible (data.degreeTwoBoundaryData.colorWord
      (data.reductionDeletedColoring graphData side C)) := by
  rw [side.compatible_iff_pair_colors]
  intro step
  exact (data.degreeTwoBoundaryColorWord_leftPort_eq_reductionSeamColor
    graphData hcubic side C hC step).trans
      (data.degreeTwoBoundaryColorWord_rightPort_eq_reductionSeamColor
        graphData hcubic side C hC step).symm

/-- Colorability of a square reduction produces an honest Tait coloring of
the induced adjacent-pair deletion together with the exact paired boundary
certificate. -/
theorem exists_deletedColoring_compatible_of_reductionTaitColorable
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (side : SquareReductionSide)
    (hcolorable : RotationSystemTaitColorable
      (data.reductionRotationSystem graphData side)) :
    ∃ deletedColoring :
        (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).EdgeColoring Color,
      IsTaitEdgeColoring
          (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
          deletedColoring ∧
        side.Compatible
          (data.degreeTwoBoundaryData.colorWord deletedColoring) := by
  rcases hcolorable with ⟨C, hC⟩
  exact ⟨data.reductionDeletedColoring graphData side C,
    data.reductionDeletedColoring_isTait graphData side C hC,
    data.reductionDeletedColorWord_compatible graphData hcubic side C hC⟩

end

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
