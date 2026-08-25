import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailCollision

/-!
# Selected successor coordinates for literal Cell-3 rails

The selected Cell-3 construction already proves that consecutive incoming and
outgoing rungs are the same ambient edge with opposite darts.  This module
packages that geometric seam together with the two surviving side slots on
each side of it.  The package is the coordinate frame for the remaining
neighbouring-cell part of Fable flag L1.

No equality between a left side face and a right side face is asserted here.
That identification is the next finite local theorem.  In particular this
module neither imports the false global unique-shared-edge premise nor calls a
coordinate frame an assembled rail.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebBoundaryData.AnnularBoundaryData
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorColorTransfer
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabSideAdjacency
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24WindingClassification

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation

private theorem canonicalSelectedFlankingPositions
    (incoming outgoing : Fin 6) (hne : incoming ≠ outgoing)
    (hnonadjacent : hexRungType incoming outgoing ≠ HexRungType.adjacent) :
    cyclicSucc incoming ∈ hexSidePositions incoming outgoing ∧
    hexCyclicPred incoming ∈ hexSidePositions incoming outgoing ∧
    hexCyclicPred outgoing ∈ hexSidePositions incoming outgoing ∧
    cyclicSucc outgoing ∈ hexSidePositions incoming outgoing ∧
    (cyclicSucc incoming).val ≡ incoming.val + 1 [MOD 6] ∧
    incoming.val ≡ (hexCyclicPred incoming).val + 1 [MOD 6] ∧
    outgoing.val ≡ (hexCyclicPred outgoing).val + 1 [MOD 6] ∧
    (cyclicSucc outgoing).val ≡ outgoing.val + 1 [MOD 6] := by
  fin_cases incoming <;> fin_cases outgoing <;>
    norm_num [hexSidePositions, hexRungType, hexCyclicDistance,
      hexForwardDistance, hexCyclicPred, cyclicSucc, Nat.ModEq] at *

/-- The two selected side slots immediately after and before the incoming
rung.  Their order is chosen to agree with the two rail tracks arriving from
the preceding Cell-3 hexagon. -/
theorem exists_two_selectedPlacementSidePositions_flanking_incoming
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior) :
    ∃ after before :
        {position // position ∈ selectedPlacementSidePositions placement},
      after ≠ before ∧
      after.1.val ≡ placement.incomingPosition.val + 1 [MOD 6] ∧
      placement.incomingPosition.val ≡ before.1.val + 1 [MOD 6] := by
  have hnonadjacent :=
    SelectedInternalHexRungPlacement.rungType_ne_adjacent_of_cell3
      corridor rungs interior placement
  have hcanonical := canonicalSelectedFlankingPositions
    placement.incomingPosition6 placement.outgoingPosition6
      placement.positions6_ne hnonadjacent
  let after6 : {position // position ∈ hexSidePositions
      placement.incomingPosition6 placement.outgoingPosition6} :=
    ⟨cyclicSucc placement.incomingPosition6, hcanonical.1⟩
  let before6 : {position // position ∈ hexSidePositions
      placement.incomingPosition6 placement.outgoingPosition6} :=
    ⟨hexCyclicPred placement.incomingPosition6, hcanonical.2.1⟩
  let after := selectedPlacementSidePositionOfSix placement after6
  let before := selectedPlacementSidePositionOfSix placement before6
  refine ⟨after, before, ?_, ?_, ?_⟩
  · intro heq
    have hvals := congrArg (fun position => position.1.val) heq
    simp only [after, before, selectedPlacementSidePositionOfSix,
      selectedPlacementPositionOfSix_val] at hvals
    have hne6 : ∀ position : Fin 6,
        cyclicSucc position ≠ hexCyclicPred position := by
      intro position
      fin_cases position <;> decide
    apply hne6 placement.incomingPosition6
    exact Fin.ext hvals
  · simpa [after, after6, selectedPlacementSidePositionOfSix,
      SelectedInternalHexRungPlacement.incomingPosition6] using
      hcanonical.2.2.2.2.1
  · simpa [before, before6, selectedPlacementSidePositionOfSix,
      SelectedInternalHexRungPlacement.incomingPosition6] using
      hcanonical.2.2.2.2.2.1

/-- The literal coordinate frame spanning one selected successor seam.

The common rung is retained as an equality of oriented darts.  The four side
slots are only coordinates at this stage; later L1 work must prove their
cross-seam face relations or return the exact finite collision. -/
structure SelectedSourceLocalRailSuccessorFrame
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {leftInterior : CorridorInterior blockLength}
    (hnext : leftInterior.center.val + 2 < blockLength)
    (leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior)
    (rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)) where
  leftBefore :
    {position // position ∈ selectedPlacementSidePositions leftPlacement}
  leftAfter :
    {position // position ∈ selectedPlacementSidePositions leftPlacement}
  rightAfter :
    {position // position ∈ selectedPlacementSidePositions rightPlacement}
  rightBefore :
    {position // position ∈ selectedPlacementSidePositions rightPlacement}
  leftBefore_mod : leftPlacement.outgoingPosition.val ≡
    leftBefore.1.val + 1 [MOD 6]
  leftAfter_mod : leftAfter.1.val ≡
    leftPlacement.outgoingPosition.val + 1 [MOD 6]
  rightAfter_mod : rightAfter.1.val ≡
    rightPlacement.incomingPosition.val + 1 [MOD 6]
  rightBefore_mod : rightPlacement.incomingPosition.val ≡
    rightBefore.1.val + 1 [MOD 6]
  seam_oriented :
    faceCycleDart web.annular.RS rightPlacement.root
        rightPlacement.incomingPosition =
      web.annular.RS.alpha
        (faceCycleDart web.annular.RS leftPlacement.root
          leftPlacement.outgoingPosition)

/-- Every pair of consecutive selected Cell-3 placements constructs the exact
successor coordinate frame.  This is an unconditional finite six-cycle fact;
it deliberately stops before the neighbouring-face classification. -/
theorem exists_selectedSourceLocalRailSuccessorFrame
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {leftInterior : CorridorInterior blockLength}
    (hnext : leftInterior.center.val + 2 < blockLength)
    (leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior)
    (rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)) :
    Nonempty (SelectedSourceLocalRailSuccessorFrame hnext leftPlacement
      rightPlacement) := by
  rcases exists_two_selectedPlacementSidePositions_flanking_outgoing
      (corridor := corridor) leftPlacement with
    ⟨leftBefore, leftAfter, _hleftNe, hleftBefore, hleftAfter⟩
  rcases exists_two_selectedPlacementSidePositions_flanking_incoming
      (corridor := corridor) rightPlacement with
    ⟨rightAfter, rightBefore, _hrightNe, hrightAfter, hrightBefore⟩
  exact ⟨{
    leftBefore := leftBefore
    leftAfter := leftAfter
    rightAfter := rightAfter
    rightBefore := rightBefore
    leftBefore_mod := hleftBefore
    leftAfter_mod := hleftAfter
    rightAfter_mod := hrightAfter
    rightBefore_mod := hrightBefore
    seam_oriented := selectedNextIncomingDart_eq_alpha_outgoingDart
      (corridor := corridor) hnext leftPlacement rightPlacement
  }⟩

/-- The first selected rail track crosses a successor seam without changing
its exterior face.  The proof is the literal three-dart rotation calculation
at one endpoint of the common rung. -/
theorem SelectedSourceLocalRailSuccessorFrame.leftBeforeFace_eq_rightAfterFace
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}
    (frame : SelectedSourceLocalRailSuccessorFrame hnext leftPlacement
      rightPlacement) :
    selectedPlacementSideFace leftPlacement frame.leftBefore =
      selectedPlacementSideFace rightPlacement frame.rightAfter := by
  let leftBeforeDart := faceCycleDart web.annular.RS leftPlacement.root
    frame.leftBefore.1
  let leftOutgoingDart := faceCycleDart web.annular.RS leftPlacement.root
    leftPlacement.outgoingPosition
  let rightIncomingDart := faceCycleDart web.annular.RS rightPlacement.root
    rightPlacement.incomingPosition
  let rightAfterDart := faceCycleDart web.annular.RS rightPlacement.root
    frame.rightAfter.1
  have hleftStep : leftOutgoingDart = web.annular.RS.phi leftBeforeDart := by
    exact faceCycleDart_successor_of_modEq web.annular.RS leftPlacement.root
      leftPlacement.orbit_card frame.leftBefore.1
        leftPlacement.outgoingPosition frame.leftBefore_mod
  have hrightStep : rightAfterDart = web.annular.RS.phi rightIncomingDart := by
    exact faceCycleDart_successor_of_modEq web.annular.RS rightPlacement.root
      rightPlacement.orbit_card rightPlacement.incomingPosition
        frame.rightAfter.1 frame.rightAfter_mod
  have hseam : rightIncomingDart =
      web.annular.RS.alpha leftOutgoingDart := by
    simpa [rightIncomingDart, leftOutgoingDart] using frame.seam_oriented
  have hcard : (web.annular.RS.dartsAt
      (web.annular.RS.vertOf (web.annular.RS.alpha leftBeforeDart))).card = 3 := by
    apply Instance.InteriorFace.dartsAt_card_eq_three web
    change (selectedPlacementSideFace leftPlacement frame.leftBefore).1 ∈
      web.annular.cellulation.interiorFaces
    exact selectedPlacementSideFace_internal (corridor := corridor)
      leftPlacement frame.leftBefore
  have hcube := rho_cube_apply_of_dartsAt_card_eq_three web.annular.RS
    (Instance.InteriorFace.vertexRotationCyclic web)
      (web.annular.RS.alpha leftBeforeDart) hcard
  have hstep : web.annular.RS.phi
      (web.annular.RS.alpha rightAfterDart) =
      web.annular.RS.alpha leftBeforeDart := by
    calc
      web.annular.RS.phi (web.annular.RS.alpha rightAfterDart) =
          web.annular.RS.rho rightAfterDart := by
            simp only [RotationSystem.phi_apply,
              web.annular.RS.alpha_involutive]
      _ = web.annular.RS.rho (web.annular.RS.phi rightIncomingDart) := by
            rw [hrightStep]
      _ = web.annular.RS.rho (web.annular.RS.rho leftOutgoingDart) := by
            rw [RotationSystem.phi_apply, hseam]
            simp only [web.annular.RS.alpha_involutive]
      _ = web.annular.RS.rho
          (web.annular.RS.rho (web.annular.RS.phi leftBeforeDart)) := by
            rw [hleftStep]
      _ = web.annular.RS.alpha leftBeforeDart := by
            simpa only [RotationSystem.phi_apply] using hcube
  apply Subtype.ext
  change dartOrbitFace web.annular.RS (web.annular.RS.alpha leftBeforeDart) =
    dartOrbitFace web.annular.RS (web.annular.RS.alpha rightAfterDart)
  calc
    dartOrbitFace web.annular.RS (web.annular.RS.alpha leftBeforeDart) =
        dartOrbitFace web.annular.RS
          (web.annular.RS.phi (web.annular.RS.alpha rightAfterDart)) := by
            rw [hstep]
    _ = dartOrbitFace web.annular.RS (web.annular.RS.alpha rightAfterDart) :=
      dartOrbitFace_phi_eq web.annular.RS _

/-- The second selected rail track has the analogous exact face continuation
across the other endpoint of the common rung. -/
theorem SelectedSourceLocalRailSuccessorFrame.leftAfterFace_eq_rightBeforeFace
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}
    (frame : SelectedSourceLocalRailSuccessorFrame hnext leftPlacement
      rightPlacement) :
    selectedPlacementSideFace leftPlacement frame.leftAfter =
      selectedPlacementSideFace rightPlacement frame.rightBefore := by
  let leftOutgoingDart := faceCycleDart web.annular.RS leftPlacement.root
    leftPlacement.outgoingPosition
  let leftAfterDart := faceCycleDart web.annular.RS leftPlacement.root
    frame.leftAfter.1
  let rightBeforeDart := faceCycleDart web.annular.RS rightPlacement.root
    frame.rightBefore.1
  let rightIncomingDart := faceCycleDart web.annular.RS rightPlacement.root
    rightPlacement.incomingPosition
  have hleftStep : leftAfterDart = web.annular.RS.phi leftOutgoingDart := by
    exact faceCycleDart_successor_of_modEq web.annular.RS leftPlacement.root
      leftPlacement.orbit_card leftPlacement.outgoingPosition frame.leftAfter.1
        frame.leftAfter_mod
  have hrightStep : rightIncomingDart = web.annular.RS.phi rightBeforeDart := by
    exact faceCycleDart_successor_of_modEq web.annular.RS rightPlacement.root
      rightPlacement.orbit_card frame.rightBefore.1
        rightPlacement.incomingPosition frame.rightBefore_mod
  have hseam : rightIncomingDart =
      web.annular.RS.alpha leftOutgoingDart := by
    simpa [rightIncomingDart, leftOutgoingDart] using frame.seam_oriented
  have hcard : (web.annular.RS.dartsAt
      (web.annular.RS.vertOf (web.annular.RS.alpha rightBeforeDart))).card = 3 := by
    apply Instance.InteriorFace.dartsAt_card_eq_three web
    change (selectedPlacementSideFace rightPlacement frame.rightBefore).1 ∈
      web.annular.cellulation.interiorFaces
    exact selectedPlacementSideFace_internal (corridor := corridor)
      rightPlacement frame.rightBefore
  have hcube := rho_cube_apply_of_dartsAt_card_eq_three web.annular.RS
    (Instance.InteriorFace.vertexRotationCyclic web)
      (web.annular.RS.alpha rightBeforeDart) hcard
  have hstep : web.annular.RS.phi
      (web.annular.RS.alpha leftAfterDart) =
      web.annular.RS.alpha rightBeforeDart := by
    calc
      web.annular.RS.phi (web.annular.RS.alpha leftAfterDart) =
          web.annular.RS.rho leftAfterDart := by
            simp only [RotationSystem.phi_apply,
              web.annular.RS.alpha_involutive]
      _ = web.annular.RS.rho (web.annular.RS.phi leftOutgoingDart) := by
            rw [hleftStep]
      _ = web.annular.RS.rho (web.annular.RS.rho rightIncomingDart) := by
            rw [RotationSystem.phi_apply, ← hseam]
      _ = web.annular.RS.rho
          (web.annular.RS.rho (web.annular.RS.phi rightBeforeDart)) := by
            rw [hrightStep]
      _ = web.annular.RS.alpha rightBeforeDart := by
            simpa only [RotationSystem.phi_apply] using hcube
  apply Subtype.ext
  change dartOrbitFace web.annular.RS (web.annular.RS.alpha leftAfterDart) =
    dartOrbitFace web.annular.RS (web.annular.RS.alpha rightBeforeDart)
  calc
    dartOrbitFace web.annular.RS (web.annular.RS.alpha leftAfterDart) =
        dartOrbitFace web.annular.RS
          (web.annular.RS.phi (web.annular.RS.alpha leftAfterDart)) :=
      (dartOrbitFace_phi_eq web.annular.RS _).symm
    _ = dartOrbitFace web.annular.RS
        (web.annular.RS.alpha rightBeforeDart) := by rw [hstep]

/-- A selected successor frame together with the next Cell-3 hexagon's two
separated canonical rail paths.  The dependent fields prevent a shape or path
certificate from being attached to unrelated seam coordinates. -/
structure SeparatedSelectedSourceLocalRailSuccessor
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {leftInterior : CorridorInterior blockLength}
    (hnext : leftInterior.center.val + 2 < blockLength)
    (leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior)
    (rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)) where
  frame : SelectedSourceLocalRailSuccessorFrame hnext leftPlacement rightPlacement
  rightOutgoingBefore :
    {position // position ∈ selectedPlacementSidePositions rightPlacement}
  rightOutgoingAfter :
    {position // position ∈ selectedPlacementSidePositions rightPlacement}
  rightOutgoingBefore_mod : rightPlacement.outgoingPosition.val ≡
    rightOutgoingBefore.1.val + 1 [MOD 6]
  rightOutgoingAfter_mod : rightOutgoingAfter.1.val ≡
    rightPlacement.outgoingPosition.val + 1 [MOD 6]
  rightRails : SeparatedSelectedSourceLocalRailPaths rightPlacement
    frame.rightAfter frame.rightBefore rightOutgoingBefore rightOutgoingAfter

/-- **L1 selected neighboring-cell alternative.** Two consecutive literal
Cell-3 placements construct the oriented successor frame and the next cell's
separated rail pair, unless the next cell returns the exact finite selected
collision certificate.

This closes the coordinate/face-identification part of the neighboring seam.
It does not yet prove that appending an arbitrary number of successful cells
preserves path simplicity or attaches the two annular end caps. -/
theorem exists_separatedSelectedSourceLocalRailSuccessor_or_collision
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {leftInterior : CorridorInterior blockLength}
    (hnext : leftInterior.center.val + 2 < blockLength)
    (hnextNext : leftInterior.center.val + 3 < blockLength)
    (leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior)
    (rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)) :
    Nonempty (SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement) ∨
      SelectedLocalLayerCollision
        (interior := nextCorridorInterior leftInterior hnext)
        (by simpa [nextCorridorInterior] using hnextNext) rightPlacement := by
  let hrightNext :
      (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength := by
    simpa [nextCorridorInterior] using hnextNext
  rcases exists_selectedSourceLocalRailSuccessorFrame hnext leftPlacement
      rightPlacement with ⟨frame⟩
  rcases exists_two_selectedPlacementSidePositions_flanking_outgoing
      (corridor := corridor) rightPlacement with
    ⟨rightOutgoingBefore, rightOutgoingAfter, _hrightOutgoingNe,
      hrightOutgoingBefore, hrightOutgoingAfter⟩
  rcases exists_separatedSelectedSourceLocalRailPaths_or_collision_of_cell3
      hrightNext rightPlacement frame.rightAfter frame.rightBefore
        rightOutgoingBefore rightOutgoingAfter frame.rightAfter_mod
        frame.rightBefore_mod hrightOutgoingBefore hrightOutgoingAfter with
    hrails | hcollision
  · left
    exact ⟨{
      frame := frame
      rightOutgoingBefore := rightOutgoingBefore
      rightOutgoingAfter := rightOutgoingAfter
      rightOutgoingBefore_mod := hrightOutgoingBefore
      rightOutgoingAfter_mod := hrightOutgoingAfter
      rightRails := Classical.choice hrails
    }⟩
  · exact Or.inr hcollision

end Instance.SelectedLocalLayerFormation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
