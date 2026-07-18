import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairPlanarReduction
import Mettapedia.GraphTheory.FourColor.GoertzelV24FourEdgeCutPlanarInterfaces

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FourEdgeCutNoncrossingInterfaces

open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24FourEdgeCutBoundaryOrder
open GoertzelV24FourEdgeCutPlanarInterfaces
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open GoertzelV24ThreeEdgeCutMinimality
open GoertzelV24TwoEdgeCutCapGeometry
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
variable {E : Type*} [Fintype E] [DecidableEq E]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- For either noncrossing pairing, its two left positions followed by its
two right positions in reverse order enumerate all four cyclic ports. -/
theorem boundaryPort_bijective (side : SquareReductionSide) :
    Function.Bijective side.boundaryPort := by
  fin_cases side <;> decide

/-- The equivalence from ordered seam positions to the common cyclic port
labels of one noncrossing pairing. -/
def boundaryPortEquiv (side : SquareReductionSide) :
    OrderedSeamPosition 2 ≃ Fin 4 :=
  Equiv.ofBijective side.boundaryPort (boundaryPort_bijective side)

@[simp]
theorem boundaryPortEquiv_apply
    (side : SquareReductionSide) (position : OrderedSeamPosition 2) :
    boundaryPortEquiv side position = side.boundaryPort position :=
  rfl

/-- In equivalence form, either standard noncrossing presentation transports
the opposite-interface cycle to the same positive cyclic port rotation. -/
theorem boundaryPortEquiv_permCongr_oppositeBoundaryCycle
    (side : SquareReductionSide) :
    (boundaryPortEquiv side).permCongr (oppositeBoundaryCycle 2) =
      finRotate 4 := by
  apply Equiv.ext
  intro port
  let position := (boundaryPortEquiv side).symm port
  have hposition : boundaryPortEquiv side position = port :=
    (boundaryPortEquiv side).apply_symm_apply port
  change boundaryPortEquiv side (oppositeBoundaryCycle 2 position) =
    finRotate 4 port
  rw [boundaryPortEquiv_apply,
    side.boundaryPort_oppositeBoundaryCycle]
  congr 1

/-- The actual crossing edge carrying one cyclic boundary-port label. -/
def boundaryCrossing
    (RS : RotationSystem V E) (deleted : Finset V)
    (boundaryOrder : Fin 4 ≃
      BoundaryDart RS (deletedRegionKeep deleted)) (port : Fin 4) : E :=
  RS.edgeOf (boundaryOrder port).1.1

theorem boundaryCrossing_injective
    (RS : RotationSystem V E) (deleted : Finset V)
    (boundaryOrder : Fin 4 ≃
      BoundaryDart RS (deletedRegionKeep deleted)) :
    Function.Injective (boundaryCrossing RS deleted boundaryOrder) := by
  intro first second hedges
  apply boundaryOrder.injective
  apply boundaryDart_eq_of_edgeOf_eq
  exact hedges

/-- The first ordered edge pair of a named noncrossing presentation. -/
def pairedLeftCrossing
    (RS : RotationSystem V E) (deleted : Finset V)
    (boundaryOrder : Fin 4 ≃
      BoundaryDart RS (deletedRegionKeep deleted))
    (side : SquareReductionSide) : Fin 2 → E :=
  fun step ↦ boundaryCrossing RS deleted boundaryOrder
    (side.leftPort step)

/-- The oppositely oriented second edge pair of a named noncrossing
presentation. -/
def pairedRightCrossing
    (RS : RotationSystem V E) (deleted : Finset V)
    (boundaryOrder : Fin 4 ≃
      BoundaryDart RS (deletedRegionKeep deleted))
    (side : SquareReductionSide) : Fin 2 → E :=
  fun step ↦ boundaryCrossing RS deleted boundaryOrder
    (side.rightPort step)

theorem pairedLeftCrossing_injective
    (RS : RotationSystem V E) (deleted : Finset V)
    (boundaryOrder : Fin 4 ≃
      BoundaryDart RS (deletedRegionKeep deleted))
    (side : SquareReductionSide) :
    Function.Injective
      (pairedLeftCrossing RS deleted boundaryOrder side) := by
  intro first second hedges
  apply side.leftPort_injective
  exact boundaryCrossing_injective RS deleted boundaryOrder hedges

theorem pairedRightCrossing_injective
    (RS : RotationSystem V E) (deleted : Finset V)
    (boundaryOrder : Fin 4 ≃
      BoundaryDart RS (deletedRegionKeep deleted))
    (side : SquareReductionSide) :
    Function.Injective
      (pairedRightCrossing RS deleted boundaryOrder side) := by
  intro first second hedges
  apply side.rightPort_injective
  exact boundaryCrossing_injective RS deleted boundaryOrder hedges

theorem pairedCuts_disjoint
    (RS : RotationSystem V E) (deleted : Finset V)
    (boundaryOrder : Fin 4 ≃
      BoundaryDart RS (deletedRegionKeep deleted))
    (side : SquareReductionSide) :
    Disjoint
      (orderedCut (pairedLeftCrossing RS deleted boundaryOrder side))
      (orderedCut (pairedRightCrossing RS deleted boundaryOrder side)) := by
  rw [Finset.disjoint_left]
  intro edge hleft hright
  rcases Finset.mem_image.mp hleft with
    ⟨left, _hleft, hleftEdge⟩
  rcases Finset.mem_image.mp hright with
    ⟨right, _hright, hrightEdge⟩
  apply side.leftPort_ne_rightPort left right
  apply boundaryCrossing_injective RS deleted boundaryOrder
  exact hleftEdge.trans hrightEdge.symm

/-- Either named noncrossing pairing presents exactly the same four actual
crossing edges. -/
theorem pairedCuts_boundary
    (RS : RotationSystem V E) (deleted : Finset V)
    (boundaryOrder : Fin 4 ≃
      BoundaryDart RS (deletedRegionKeep deleted))
    (side : SquareReductionSide) :
    orderedCut (pairedLeftCrossing RS deleted boundaryOrder side) ∪
        orderedCut (pairedRightCrossing RS deleted boundaryOrder side) =
      vertexSetCrossingEdges RS deleted := by
  ext edge
  constructor
  · intro hedge
    rw [Finset.mem_union] at hedge
    rcases hedge with hleft | hright
    · rcases Finset.mem_image.mp hleft with
        ⟨step, _hstep, hstep⟩
      rw [← hstep]
      exact boundaryDart_edge_mem_vertexSetCrossingEdges RS deleted
        (boundaryOrder (side.leftPort step))
    · rcases Finset.mem_image.mp hright with
        ⟨step, _hstep, hstep⟩
      rw [← hstep]
      exact boundaryDart_edge_mem_vertexSetCrossingEdges RS deleted
        (boundaryOrder (side.rightPort step))
  · intro hedge
    let boundary : BoundaryDart RS (deletedRegionKeep deleted) :=
      (boundaryDartEquivVertexSetCrossingEdge RS deleted).symm
        ⟨edge, hedge⟩
    let port : Fin 4 := boundaryOrder.symm boundary
    let position : OrderedSeamPosition 2 :=
      (boundaryPortEquiv side).symm port
    have hposition : side.boundaryPort position = port := by
      rw [← boundaryPortEquiv_apply]
      exact (boundaryPortEquiv side).apply_symm_apply port
    have hboundaryOrder : boundaryOrder port = boundary :=
      boundaryOrder.apply_symm_apply boundary
    have hboundaryEdge : RS.edgeOf boundary.1.1 = edge := by
      change ((boundaryDartEquivVertexSetCrossingEdge RS deleted)
        ((boundaryDartEquivVertexSetCrossingEdge RS deleted).symm
          ⟨edge, hedge⟩)).1 = edge
      rw [Equiv.apply_symm_apply]
    rcases position with step | step
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨step, Finset.mem_univ step, ?_⟩
      change side.leftPort step = port at hposition
      change RS.edgeOf (boundaryOrder (side.leftPort step)).1.1 = edge
      rw [hposition, hboundaryOrder, hboundaryEdge]
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨step, Finset.mem_univ step, ?_⟩
      change side.rightPort step = port at hposition
      change RS.edgeOf (boundaryOrder (side.rightPort step)).1.1 = edge
      rw [hposition, hboundaryOrder, hboundaryEdge]

/-- The common cyclic boundary coordinates read in one named noncrossing
presentation. -/
def pairedBoundaryPositionOrder
    (RS : RotationSystem V E) (deleted : Finset V)
    (boundaryOrder : Fin 4 ≃
      BoundaryDart RS (deletedRegionKeep deleted))
    (side : SquareReductionSide) :
    OrderedSeamPosition 2 ≃
      BoundaryDart RS (deletedRegionKeep deleted) :=
  (boundaryPortEquiv side).trans boundaryOrder

/-- Reconstructing the splice boundary enumeration from either named edge
pairing gives that pairing's presentation of the common cyclic order. -/
theorem orderedBoundaryPositionEquiv_eq_pairedBoundaryPositionOrder
    (RS : RotationSystem V E) (deleted : Finset V)
    (boundaryOrder : Fin 4 ≃
      BoundaryDart RS (deletedRegionKeep deleted))
    (side : SquareReductionSide) :
    orderedBoundaryPositionEquiv RS deleted
        (pairedLeftCrossing RS deleted boundaryOrder side)
        (pairedRightCrossing RS deleted boundaryOrder side)
        (pairedCuts_boundary RS deleted boundaryOrder side)
        (pairedLeftCrossing_injective RS deleted boundaryOrder side)
        (pairedRightCrossing_injective RS deleted boundaryOrder side)
        (pairedCuts_disjoint RS deleted boundaryOrder side) =
      pairedBoundaryPositionOrder RS deleted boundaryOrder side := by
  apply Equiv.ext
  intro position
  apply boundaryDart_eq_of_edgeOf_eq
  rcases position with step | step
  · rw [orderedBoundaryPositionEquiv_apply_left,
      orderedBoundaryDart_edgeOf]
    rfl
  · rw [orderedBoundaryPositionEquiv_apply_right,
      orderedBoundaryDart_edgeOf]
    rfl

/-- Both noncrossing presentations transport their opposite-interface cycle
to the same actual positive four-boundary successor. -/
theorem pairedBoundaryPositionOrder_permCongr_oppositeBoundaryCycle
    (RS : RotationSystem V E) (deleted : Finset V)
    (boundaryOrder : Fin 4 ≃
      BoundaryDart RS (deletedRegionKeep deleted))
    (side : SquareReductionSide) :
    (pairedBoundaryPositionOrder RS deleted boundaryOrder side).permCongr
        (oppositeBoundaryCycle 2) =
      boundaryOrder.permCongr (finRotate 4) := by
  apply Equiv.ext
  intro boundary
  have hport := DFunLike.congr_fun
    (boundaryPortEquiv_permCongr_oppositeBoundaryCycle side)
    (boundaryOrder.symm boundary)
  have htransport := congrArg boundaryOrder hport
  simpa [pairedBoundaryPositionOrder, Equiv.permCongr_apply] using htransport

/-- One proved cyclic boundary order simultaneously discharges the planar
order premise for either noncrossing pairing. -/
theorem pairedCutsFollowOppositeDeletedBoundaryOrder
    (RS : RotationSystem V E) (deleted : Finset V)
    (boundaryOrder : Fin 4 ≃
      BoundaryDart RS (deletedRegionKeep deleted))
    (horder : deletedRegionBoundarySuccessor RS deleted =
      boundaryOrder.permCongr (finRotate 4))
    (side : SquareReductionSide) :
    CutsFollowOppositeDeletedBoundaryOrder RS deleted
      (pairedLeftCrossing RS deleted boundaryOrder side)
      (pairedRightCrossing RS deleted boundaryOrder side)
      (pairedCuts_boundary RS deleted boundaryOrder side)
      (pairedLeftCrossing_injective RS deleted boundaryOrder side)
      (pairedRightCrossing_injective RS deleted boundaryOrder side)
      (pairedCuts_disjoint RS deleted boundaryOrder side) := by
  unfold CutsFollowOppositeDeletedBoundaryOrder
  rw [orderedBoundaryPositionEquiv_eq_pairedBoundaryPositionOrder,
    pairedBoundaryPositionOrder_permCongr_oppositeBoundaryCycle]
  exact horder

/-- A single cyclic labeling of the actual four-cut boundary, retaining both
the deleted- and retained-side first-return orders. -/
structure CyclicFourBoundaryData
    (RS : RotationSystem V E) (deleted : Finset V) where
  boundaryOrder : Fin 4 ≃ BoundaryDart RS (deletedRegionKeep deleted)
  deleted_order : deletedRegionBoundarySuccessor RS deleted =
    boundaryOrder.permCongr (finRotate 4)
  retained_order : retainedRegionBoundarySuccessor RS
      (deletedRegionKeep deleted) =
    (boundaryOrder.permCongr (finRotate 4))⁻¹

namespace CyclicFourBoundaryData

variable {RS : RotationSystem V E} {deleted : Finset V}
  (data : CyclicFourBoundaryData RS deleted)

/-- Changing only the distinguished outer dart preserves the complete cyclic
four-boundary data definitionally. -/
def withOuter (root : RS.D) :
    CyclicFourBoundaryData (RS.withOuter root) deleted where
  boundaryOrder := data.boundaryOrder
  deleted_order := data.deleted_order
  retained_order := data.retained_order

/-- The actual planar interface data for either noncrossing pairing, derived
from the same cyclic port labels. -/
def interface (side : SquareReductionSide) :
    FourCutPlanarInterfaceData RS deleted where
  leftCrossing := pairedLeftCrossing RS deleted data.boundaryOrder side
  rightCrossing := pairedRightCrossing RS deleted data.boundaryOrder side
  boundary := pairedCuts_boundary RS deleted data.boundaryOrder side
  left_injective :=
    pairedLeftCrossing_injective RS deleted data.boundaryOrder side
  right_injective :=
    pairedRightCrossing_injective RS deleted data.boundaryOrder side
  disjoint := pairedCuts_disjoint RS deleted data.boundaryOrder side
  order := pairedCutsFollowOppositeDeletedBoundaryOrder
    RS deleted data.boundaryOrder data.deleted_order side

@[simp]
theorem interface_leftCrossing
    (side : SquareReductionSide) (step : Fin 2) :
    (data.interface side).leftCrossing step =
      boundaryCrossing RS deleted data.boundaryOrder
        (side.leftPort step) :=
  rfl

@[simp]
theorem interface_rightCrossing
    (side : SquareReductionSide) (step : Fin 2) :
    (data.interface side).rightCrossing step =
      boundaryCrossing RS deleted data.boundaryOrder
        (side.rightPort step) :=
  rfl

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Root graph-backed data at the first retained boundary dart. -/
def rootedGraphData
    (graphData : Data G)
    (data : CyclicFourBoundaryData graphData.toRotationSystem deleted) :
    Data G :=
  graphDataWithOuter graphData (data.boundaryOrder 0).1.1

/-- The same cyclic boundary data on the rerooted graph-backed rotation
system. -/
def rootedBoundaryData
    (graphData : Data G)
    (data : CyclicFourBoundaryData graphData.toRotationSystem deleted) :
    CyclicFourBoundaryData
      (data.rootedGraphData graphData).toRotationSystem deleted := by
  change CyclicFourBoundaryData
    (graphData.toRotationSystem.withOuter
      (data.boundaryOrder 0).1.1) deleted
  exact data.withOuter (data.boundaryOrder 0).1.1

/-- Rerooting at a retained boundary dart supplies the outer-side premise
of every planar splice built from the cyclic four-boundary data. -/
theorem rooted_outer_retained
    (graphData : Data G)
    (data : CyclicFourBoundaryData graphData.toRotationSystem deleted) :
    deletedRegionKeep deleted
      ((data.rootedGraphData graphData).toRotationSystem.vertOf
        (data.rootedGraphData graphData).toRotationSystem.outer) := by
  exact (data.boundaryOrder 0).1.2

end CyclicFourBoundaryData

/-- Every exact cyclic four-edge cut has one common cyclic boundary labeling
that supplies both noncrossing planar interface presentations. -/
theorem exists_cyclicFourBoundaryData_of_exactCyclicFourCut
    (graphData : Data G)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4) :
    Nonempty (CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut)) := by
  rcases exists_boundaryOrder_of_exactCyclicFourCut graphData hsphere
      htwoSided hconnected hrotation hcyclic cut hcard with
    ⟨boundaryOrder, hdeletedOrder, hretainedOrder⟩
  exact ⟨⟨boundaryOrder, hdeletedOrder, hretainedOrder⟩⟩

end

end GoertzelV24FourEdgeCutNoncrossingInterfaces

end Mettapedia.GraphTheory.FourColor
