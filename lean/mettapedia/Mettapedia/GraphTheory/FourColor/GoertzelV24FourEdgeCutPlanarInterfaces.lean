import Mettapedia.GraphTheory.FourColor.GoertzelV24FourEdgeCutBoundaryOrder

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FourEdgeCutPlanarInterfaces

open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24FourEdgeCutBoundaryOrder
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open GoertzelV24ThreeEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
variable {E : Type*} [Fintype E] [DecidableEq E]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Read cyclic four-boundary coordinates as two interfaces.  The left
positions occur first and the right positions occur in reverse order around
the boundary. -/
def boundaryPositionOrder
    (RS : RotationSystem V E) (deleted : Finset V)
    (boundaryOrder : Fin 4 ≃
      BoundaryDart RS (deletedRegionKeep deleted)) :
    OrderedSeamPosition 2 ≃
      BoundaryDart RS (deletedRegionKeep deleted) :=
  (oppositeBoundaryPositionEquiv 2).trans boundaryOrder

/-- The first pair of edges in opposite-interface boundary coordinates. -/
def leftCrossing
    (RS : RotationSystem V E) (deleted : Finset V)
    (boundaryOrder : Fin 4 ≃
      BoundaryDart RS (deletedRegionKeep deleted)) : Fin 2 → E :=
  fun step ↦ RS.edgeOf
    ((boundaryPositionOrder RS deleted boundaryOrder (Sum.inl step)).1.1)

/-- The second pair of edges in opposite-interface boundary coordinates. -/
def rightCrossing
    (RS : RotationSystem V E) (deleted : Finset V)
    (boundaryOrder : Fin 4 ≃
      BoundaryDart RS (deletedRegionKeep deleted)) : Fin 2 → E :=
  fun step ↦ RS.edgeOf
    ((boundaryPositionOrder RS deleted boundaryOrder (Sum.inr step)).1.1)

theorem leftCrossing_injective
    (RS : RotationSystem V E) (deleted : Finset V)
    (boundaryOrder : Fin 4 ≃
      BoundaryDart RS (deletedRegionKeep deleted)) :
    Function.Injective (leftCrossing RS deleted boundaryOrder) := by
  intro first second hedges
  have hdarts :
      boundaryPositionOrder RS deleted boundaryOrder (Sum.inl first) =
        boundaryPositionOrder RS deleted boundaryOrder (Sum.inl second) := by
    apply boundaryDart_eq_of_edgeOf_eq
    exact hedges
  exact Sum.inl_injective
    ((boundaryPositionOrder RS deleted boundaryOrder).injective hdarts)

theorem rightCrossing_injective
    (RS : RotationSystem V E) (deleted : Finset V)
    (boundaryOrder : Fin 4 ≃
      BoundaryDart RS (deletedRegionKeep deleted)) :
    Function.Injective (rightCrossing RS deleted boundaryOrder) := by
  intro first second hedges
  have hdarts :
      boundaryPositionOrder RS deleted boundaryOrder (Sum.inr first) =
        boundaryPositionOrder RS deleted boundaryOrder (Sum.inr second) := by
    apply boundaryDart_eq_of_edgeOf_eq
    exact hedges
  exact Sum.inr_injective
    ((boundaryPositionOrder RS deleted boundaryOrder).injective hdarts)

theorem orderedCut_left_disjoint_right
    (RS : RotationSystem V E) (deleted : Finset V)
    (boundaryOrder : Fin 4 ≃
      BoundaryDart RS (deletedRegionKeep deleted)) :
    Disjoint (orderedCut (leftCrossing RS deleted boundaryOrder))
      (orderedCut (rightCrossing RS deleted boundaryOrder)) := by
  rw [Finset.disjoint_left]
  intro edge hleft hright
  rcases Finset.mem_image.mp hleft with
    ⟨left, _hleft, hleftEdge⟩
  rcases Finset.mem_image.mp hright with
    ⟨right, _hright, hrightEdge⟩
  have hdarts :
      boundaryPositionOrder RS deleted boundaryOrder (Sum.inl left) =
        boundaryPositionOrder RS deleted boundaryOrder (Sum.inr right) := by
    apply boundaryDart_eq_of_edgeOf_eq
    exact hleftEdge.trans hrightEdge.symm
  have hpositions : (Sum.inl left : OrderedSeamPosition 2) =
      Sum.inr right :=
    (boundaryPositionOrder RS deleted boundaryOrder).injective hdarts
  cases hpositions

/-- The two extracted pairs enumerate exactly the endpoint-computed boundary
edges. -/
theorem orderedCut_left_union_right
    (RS : RotationSystem V E) (deleted : Finset V)
    (boundaryOrder : Fin 4 ≃
      BoundaryDart RS (deletedRegionKeep deleted)) :
    orderedCut (leftCrossing RS deleted boundaryOrder) ∪
        orderedCut (rightCrossing RS deleted boundaryOrder) =
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
        (boundaryPositionOrder RS deleted boundaryOrder (Sum.inl step))
    · rcases Finset.mem_image.mp hright with
        ⟨step, _hstep, hstep⟩
      rw [← hstep]
      exact boundaryDart_edge_mem_vertexSetCrossingEdges RS deleted
        (boundaryPositionOrder RS deleted boundaryOrder (Sum.inr step))
  · intro hedge
    let boundary : BoundaryDart RS (deletedRegionKeep deleted) :=
      (boundaryDartEquivVertexSetCrossingEdge RS deleted).symm
        ⟨edge, hedge⟩
    let position : OrderedSeamPosition 2 :=
      (boundaryPositionOrder RS deleted boundaryOrder).symm boundary
    have hposition :
        boundaryPositionOrder RS deleted boundaryOrder position = boundary :=
      (boundaryPositionOrder RS deleted boundaryOrder).apply_symm_apply boundary
    have hboundaryEdge : RS.edgeOf boundary.1.1 = edge := by
      change ((boundaryDartEquivVertexSetCrossingEdge RS deleted)
        ((boundaryDartEquivVertexSetCrossingEdge RS deleted).symm
          ⟨edge, hedge⟩)).1 = edge
      rw [Equiv.apply_symm_apply]
    rcases position with step | step
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨step, Finset.mem_univ step, ?_⟩
      change RS.edgeOf
        (boundaryPositionOrder RS deleted boundaryOrder (Sum.inl step)).1.1 =
          edge
      rw [hposition, hboundaryEdge]
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨step, Finset.mem_univ step, ?_⟩
      change RS.edgeOf
        (boundaryPositionOrder RS deleted boundaryOrder (Sum.inr step)).1.1 =
          edge
      rw [hposition, hboundaryEdge]

/-- The library's boundary enumeration reconstructed from the two extracted
interfaces is the original cyclic boundary enumeration. -/
theorem orderedBoundaryPositionEquiv_eq_boundaryPositionOrder
    (RS : RotationSystem V E) (deleted : Finset V)
    (boundaryOrder : Fin 4 ≃
      BoundaryDart RS (deletedRegionKeep deleted)) :
    orderedBoundaryPositionEquiv RS deleted
        (leftCrossing RS deleted boundaryOrder)
        (rightCrossing RS deleted boundaryOrder)
        (orderedCut_left_union_right RS deleted boundaryOrder)
        (leftCrossing_injective RS deleted boundaryOrder)
        (rightCrossing_injective RS deleted boundaryOrder)
        (orderedCut_left_disjoint_right RS deleted boundaryOrder) =
      boundaryPositionOrder RS deleted boundaryOrder := by
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

/-- Conjugating the opposite-interface cycle back through its defining
coordinates recovers the original positive four-cycle. -/
theorem boundaryPositionOrder_permCongr_oppositeBoundaryCycle
    (RS : RotationSystem V E) (deleted : Finset V)
    (boundaryOrder : Fin 4 ≃
      BoundaryDart RS (deletedRegionKeep deleted)) :
    (boundaryPositionOrder RS deleted boundaryOrder).permCongr
        (oppositeBoundaryCycle 2) =
      boundaryOrder.permCongr (finRotate 4) := by
  apply Equiv.ext
  intro boundary
  simp [boundaryPositionOrder, oppositeBoundaryCycle,
    Equiv.permCongr_apply]

/-- A positive cyclic order on four actual boundary darts supplies the exact
opposite-order hypothesis required by the two-interface planar splice. -/
theorem cutsFollowOppositeDeletedBoundaryOrder_of_boundaryOrder
    (RS : RotationSystem V E) (deleted : Finset V)
    (boundaryOrder : Fin 4 ≃
      BoundaryDart RS (deletedRegionKeep deleted))
    (horder : deletedRegionBoundarySuccessor RS deleted =
      boundaryOrder.permCongr (finRotate 4)) :
    CutsFollowOppositeDeletedBoundaryOrder RS deleted
      (leftCrossing RS deleted boundaryOrder)
      (rightCrossing RS deleted boundaryOrder)
      (orderedCut_left_union_right RS deleted boundaryOrder)
      (leftCrossing_injective RS deleted boundaryOrder)
      (rightCrossing_injective RS deleted boundaryOrder)
      (orderedCut_left_disjoint_right RS deleted boundaryOrder) := by
  unfold CutsFollowOppositeDeletedBoundaryOrder
  rw [orderedBoundaryPositionEquiv_eq_boundaryPositionOrder,
    boundaryPositionOrder_permCongr_oppositeBoundaryCycle]
  exact horder

/-- A four-edge boundary presented as two oppositely ordered two-edge
interfaces, with every edge-level and rotation-level compatibility proof. -/
structure FourCutPlanarInterfaceData
    (RS : RotationSystem V E) (deleted : Finset V) where
  leftCrossing : Fin 2 → E
  rightCrossing : Fin 2 → E
  boundary : orderedCut leftCrossing ∪ orderedCut rightCrossing =
    vertexSetCrossingEdges RS deleted
  left_injective : Function.Injective leftCrossing
  right_injective : Function.Injective rightCrossing
  disjoint : Disjoint (orderedCut leftCrossing) (orderedCut rightCrossing)
  order : CutsFollowOppositeDeletedBoundaryOrder RS deleted
    leftCrossing rightCrossing boundary left_injective right_injective disjoint

/-- Package cyclic four-boundary coordinates as planar two-interface data. -/
def planarInterfaceDataOfBoundaryOrder
    (RS : RotationSystem V E) (deleted : Finset V)
    (boundaryOrder : Fin 4 ≃
      BoundaryDart RS (deletedRegionKeep deleted))
    (horder : deletedRegionBoundarySuccessor RS deleted =
      boundaryOrder.permCongr (finRotate 4)) :
    FourCutPlanarInterfaceData RS deleted where
  leftCrossing := leftCrossing RS deleted boundaryOrder
  rightCrossing := rightCrossing RS deleted boundaryOrder
  boundary := orderedCut_left_union_right RS deleted boundaryOrder
  left_injective := leftCrossing_injective RS deleted boundaryOrder
  right_injective := rightCrossing_injective RS deleted boundaryOrder
  disjoint := orderedCut_left_disjoint_right RS deleted boundaryOrder
  order := cutsFollowOppositeDeletedBoundaryOrder_of_boundaryOrder
    RS deleted boundaryOrder horder

/-- Every exact cyclic four-edge cut in the ambient spherical map admits an
actual pair of oppositely ordered planar two-edge interfaces. -/
theorem exists_planarInterfaceData_of_exactCyclicFourCut
    (graphData : Data G)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4) :
    Nonempty (FourCutPlanarInterfaceData graphData.toRotationSystem
      (cyclicCutVertexSide cut)) := by
  rcases exists_boundaryOrder_of_exactCyclicFourCut graphData hsphere
      htwoSided hconnected hrotation hcyclic cut hcard with
    ⟨boundaryOrder, hdeletedOrder, _hretainedOrder⟩
  exact ⟨planarInterfaceDataOfBoundaryOrder
    graphData.toRotationSystem (cyclicCutVertexSide cut)
    boundaryOrder hdeletedOrder⟩

end

end GoertzelV24FourEdgeCutPlanarInterfaces

end Mettapedia.GraphTheory.FourColor
