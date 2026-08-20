import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedRungPlacement

/-!
# L1: exact crossing receipts for selected local rail steps

A forward step between two surviving side slots of one literal Cell-3 hexagon
is either stationary because the two opposite-dart faces coincide, or it
crosses the third primal edge at their common cubic corner.  The older local
walk constructor retained only the resulting length-at-most-one dual walk.
This module keeps the literal third edge and the local degree-three receipt.

This is source-local coordinate data.  It does not rule out the stationary
branch, identify a bounded collision with a square-bond endpoint triangle,
construct a bypass, assemble long rails, attach end caps, or close the
source's bulk-corridor flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24HexSlabSideAdjacency
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation

/-- The dart on the displayed Cell-3 face at the first side slot of a local
forward step. -/
def selectedPlacementSideForwardDart
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (left : {position // position ∈ selectedPlacementSidePositions placement}) :
    web.annular.RS.D :=
  faceCycleDart web.annular.RS placement.root left.1

/-- The outside cubic corner traversed by a nonstationary local forward
step. -/
def selectedPlacementSideForwardCorner
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (left : {position // position ∈ selectedPlacementSidePositions placement}) : V :=
  web.annular.RS.vertOf
    (web.annular.RS.alpha (selectedPlacementSideForwardDart placement left))

/-- The literal third primal edge at the outside cubic corner.  This is the
edge crossed by the one-step facial-dual rail when its endpoint faces are
distinct. -/
def selectedPlacementSideForwardThirdEdge
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (left : {position // position ∈ selectedPlacementSidePositions placement}) :
    G.edgeSet :=
  web.annular.RS.edgeOf
    (web.annular.RS.rho
      (web.annular.RS.phi (selectedPlacementSideForwardDart placement left)))

/-- Proof-relevant classification of one source-selected forward side step.
The crossing constructor retains the exact primal edge instead of merely the
induced facial-dual adjacency. -/
inductive SelectedPlacementSideForwardStepReceipt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (left right :
      {position // position ∈ selectedPlacementSidePositions placement}) : Type
  | stationary
      (faces_eq : selectedPlacementSideFace placement left =
        selectedPlacementSideFace placement right)
  | crossing
      (faces_ne : selectedPlacementSideFace placement left ≠
        selectedPlacementSideFace placement right)
      (right_dart_eq : selectedPlacementSideForwardDart placement right =
        web.annular.RS.phi (selectedPlacementSideForwardDart placement left))
      (corner_card_eq_three :
        (web.annular.RS.dartsAt
          (selectedPlacementSideForwardCorner placement left)).card = 3)
      (thirdEdge_mem_shared :
        selectedPlacementSideForwardThirdEdge placement left ∈
          sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
            (Finset.univ : Finset (OrbitFace web.annular.RS))
            (selectedPlacementSideFace placement left).1
            (selectedPlacementSideFace placement right).1)

/-- **L1 exact local step receipt.**  Every forward step through the four
surviving side slots is either a literal stationary connector or crosses the
named third edge at the named cubic corner. -/
theorem selectedPlacementSideForwardStepReceipt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (left right :
      {position // position ∈ selectedPlacementSidePositions placement})
    (hsuccessor : right.1.val ≡ left.1.val + 1 [MOD 6]) :
    Nonempty (SelectedPlacementSideForwardStepReceipt placement left right) := by
  let leftDart := selectedPlacementSideForwardDart placement left
  let rightDart := selectedPlacementSideForwardDart placement right
  have hrightDart : rightDart = web.annular.RS.phi leftDart := by
    exact faceCycleDart_successor_of_modEq web.annular.RS placement.root
      placement.orbit_card left.1 right.1 hsuccessor
  by_cases hfaces : selectedPlacementSideFace placement left =
      selectedPlacementSideFace placement right
  · exact ⟨.stationary hfaces⟩
  · have hcornerCard : (web.annular.RS.dartsAt
        (selectedPlacementSideForwardCorner placement left)).card = 3 := by
      apply Instance.InteriorFace.dartsAt_card_eq_three web
      change (selectedPlacementSideFace placement left).1 ∈
        web.annular.cellulation.interiorFaces
      exact selectedPlacementSideFace_internal (corridor := corridor)
        placement left
    have hraw := thirdEdge_mem_sharedInteriorEdges_at_locally_cubic_corner
      web.annular.RS (Instance.InteriorFace.vertexRotationCyclic web)
      leftDart hcornerCard
      (by
        intro heq
        apply hfaces
        apply Subtype.ext
        change dartOrbitFace web.annular.RS
            (web.annular.RS.alpha leftDart) =
          dartOrbitFace web.annular.RS
            (web.annular.RS.alpha rightDart)
        rw [hrightDart]
        exact heq)
    refine ⟨.crossing hfaces ?_ hcornerCard ?_⟩
    · exact hrightDart
    · change web.annular.RS.edgeOf
          (web.annular.RS.rho (web.annular.RS.phi leftDart)) ∈
        sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS))
          (dartOrbitFace web.annular.RS (web.annular.RS.alpha leftDart))
          (dartOrbitFace web.annular.RS (web.annular.RS.alpha rightDart))
      rw [hrightDart]
      exact hraw

end Instance.SelectedLocalLayerFormation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
