import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseHistoricalLocality
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalRailStep
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexSlabSideAdjacency

/-!
# Coordinate compatibility at one literal Cell rebase

The source chooses the two slots flanking an outgoing rung independently in
each Cell witness.  On the six-cycle these slots are nevertheless unique.
This file records that bounded coordinate fact before the remaining facial
boundary argument inspects the three possible local rail shapes.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabSideAdjacency
open GoertzelV24OrientedHexSlab
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationFaceRegionalDartCarrier

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace Instance

namespace LocalLayerFormation

/-- Advancing the serial Cell index advances its underlying corridor interior
by exactly one step. -/
theorem sourceLocalLayerInteriorAt_nextOffset_eq_nextCorridorInterior
    {blockLength : Nat}
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    sourceLocalLayerInteriorAt (sourceLocalLayerNextOffset offset hnext) =
      nextCorridorInterior (sourceLocalLayerInteriorAt offset)
        (sourceLocalLayerInteriorAt_hasNext offset) := by
  rfl

/-- A source witness's before slot is the unique side position immediately
preceding its outgoing rung. -/
theorem SourceLocalLayerPairWitness.before_eq_of_outgoing_mod
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {interior : CorridorInterior blockLength}
    {hnext : interior.center.val + 2 < blockLength}
    (witness : SourceLocalLayerPairWitness web corridor hunique interior hnext)
    (position : {position // position ∈
      placementSidePositions witness.placement})
    (hposition : witness.placement.outgoingPosition.val ≡
      position.1.val + 1 [MOD 6]) :
    witness.before = position := by
  have hbeforeMod := witness.outgoing_after_before
  apply Subtype.ext
  apply Fin.ext
  simp only [Nat.ModEq] at hbeforeMod hposition
  have hbefore : witness.before.1.val < 6 := by
    simpa only [witness.placement.orbit_card] using witness.before.1.isLt
  have hpositionBound : position.1.val < 6 := by
    simpa only [witness.placement.orbit_card] using position.1.isLt
  omega

/-- A source witness's after slot is the unique side position immediately
following its outgoing rung. -/
theorem SourceLocalLayerPairWitness.after_eq_of_outgoing_mod
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {interior : CorridorInterior blockLength}
    {hnext : interior.center.val + 2 < blockLength}
    (witness : SourceLocalLayerPairWitness web corridor hunique interior hnext)
    (position : {position // position ∈
      placementSidePositions witness.placement})
    (hposition : position.1.val ≡
      witness.placement.outgoingPosition.val + 1 [MOD 6]) :
    witness.after = position := by
  have hafterMod := witness.after_after_outgoing
  apply Subtype.ext
  apply Fin.ext
  simp only [Nat.ModEq] at hafterMod hposition
  have hafter : witness.after.1.val < 6 := by
    simpa only [witness.placement.orbit_card] using witness.after.1.isLt
  have hpositionBound : position.1.val < 6 := by
    simpa only [witness.placement.orbit_card] using position.1.isLt
  omega

/-- When the right placement of a successor is itself the next source
witness, the successor's outgoing-before slot is that witness's canonical
before slot.  This removes the otherwise opaque independent finite choices. -/
theorem SourceLocalRailSuccessor.rightOutgoingBefore_eq_witnessBefore
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique leftInterior}
    {leftBefore leftAfter :
      {position // position ∈ placementSidePositions leftPlacement}}
    {hleftBefore : leftPlacement.outgoingPosition.val ≡
      leftBefore.1.val + 1 [MOD 6]}
    {hleftAfter : leftAfter.1.val ≡
      leftPlacement.outgoingPosition.val + 1 [MOD 6]}
    {hrightNext :
      (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    {rightWitness : SourceLocalLayerPairWitness web corridor hunique
      (nextCorridorInterior leftInterior hnext) hrightNext}
    (successor : SourceLocalRailSuccessor hnext leftPlacement leftBefore
      leftAfter hleftBefore hleftAfter rightWitness.placement) :
    successor.rightOutgoingBefore = rightWitness.before := by
  symm
  exact rightWitness.before_eq_of_outgoing_mod
    successor.rightOutgoingBefore successor.outgoingBefore_mod

/-- The corresponding outgoing-after coordinate is also canonical. -/
theorem SourceLocalRailSuccessor.rightOutgoingAfter_eq_witnessAfter
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique leftInterior}
    {leftBefore leftAfter :
      {position // position ∈ placementSidePositions leftPlacement}}
    {hleftBefore : leftPlacement.outgoingPosition.val ≡
      leftBefore.1.val + 1 [MOD 6]}
    {hleftAfter : leftAfter.1.val ≡
      leftPlacement.outgoingPosition.val + 1 [MOD 6]}
    {hrightNext :
      (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    {rightWitness : SourceLocalLayerPairWitness web corridor hunique
      (nextCorridorInterior leftInterior hnext) hrightNext}
    (successor : SourceLocalRailSuccessor hnext leftPlacement leftBefore
      leftAfter hleftBefore hleftAfter rightWitness.placement) :
    successor.rightOutgoingAfter = rightWitness.after := by
  symm
  exact rightWitness.after_eq_of_outgoing_mod
    successor.rightOutgoingAfter successor.outgoingAfter_mod

/-- On the centre face of the successor Cell, its outgoing-before occurrence
is either already in the closed incoming-flank carrier or has an immediate
face predecessor there.  This is the finite content of the three rail shapes
on the first side. -/
theorem SourceLocalRailSuccessor.rightOutgoingBefore_mem_or_predecessor_mem
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique leftInterior}
    {leftBefore leftAfter :
      {position // position ∈ placementSidePositions leftPlacement}}
    {hleftBefore : leftPlacement.outgoingPosition.val ≡
      leftBefore.1.val + 1 [MOD 6]}
    {hleftAfter : leftAfter.1.val ≡
      leftPlacement.outgoingPosition.val + 1 [MOD 6]}
    {rightPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique (nextCorridorInterior leftInterior hnext)}
    (successor : SourceLocalRailSuccessor hnext leftPlacement leftBefore
      leftAfter hleftBefore hleftAfter rightPlacement) :
    let incomingBeforeDart := faceCycleDart web.annular.RS
      rightPlacement.root successor.rightBefore.1
    let incomingAfterDart := faceCycleDart web.annular.RS
      rightPlacement.root successor.rightAfter.1
    let outgoingDart := faceCycleDart web.annular.RS rightPlacement.root
      successor.rightOutgoingBefore.1
    let incomingEdges : Finset G.edgeSet :=
      {web.annular.RS.edgeOf incomingBeforeDart,
        web.annular.RS.edgeOf incomingAfterDart}
    outgoingDart ∈ closedDartCarrier web.annular.RS incomingEdges ∨
      web.annular.RS.phi.symm outgoingDart ∈
        closedDartCarrier web.annular.RS incomingEdges := by
  dsimp only
  let incomingBeforeDart := faceCycleDart web.annular.RS
    rightPlacement.root successor.rightBefore.1
  let incomingAfterDart := faceCycleDart web.annular.RS
    rightPlacement.root successor.rightAfter.1
  let outgoingDart := faceCycleDart web.annular.RS rightPlacement.root
    successor.rightOutgoingBefore.1
  let incomingEdges : Finset G.edgeSet :=
    {web.annular.RS.edgeOf incomingBeforeDart,
      web.annular.RS.edgeOf incomingAfterDart}
  cases successor.shape with
  | forwardTwo first_eq middle _houtgoingMiddle _hmiddleIncoming =>
      left
      apply mem_closedDartCarrier_of_edge_mem
      simp [first_eq]
  | forwardThree first_step _second_step =>
      left
      have hstep : outgoingDart = web.annular.RS.phi incomingBeforeDart :=
        faceCycleDart_successor_of_modEq web.annular.RS rightPlacement.root
          rightPlacement.orbit_card successor.rightBefore.1
            successor.rightOutgoingBefore.1 first_step
      apply mem_closedDartCarrier_of_face_neighbor_of_edge_mem
        web.annular.RS incomingEdges incomingBeforeDart outgoingDart
      · simp [incomingEdges]
      · exact Or.inl hstep
  | forwardFour middle incoming_to_middle middle_to_outgoing _second_eq =>
      right
      let middleDart := faceCycleDart web.annular.RS rightPlacement.root middle.1
      have hfirst : middleDart = web.annular.RS.phi incomingBeforeDart :=
        faceCycleDart_successor_of_modEq web.annular.RS rightPlacement.root
          rightPlacement.orbit_card successor.rightBefore.1 middle.1
            incoming_to_middle
      have hsecond : outgoingDart = web.annular.RS.phi middleDart :=
        faceCycleDart_successor_of_modEq web.annular.RS rightPlacement.root
          rightPlacement.orbit_card middle.1
            successor.rightOutgoingBefore.1 middle_to_outgoing
      have hmiddle : middleDart ∈
          closedDartCarrier web.annular.RS incomingEdges := by
        apply mem_closedDartCarrier_of_face_neighbor_of_edge_mem
          web.annular.RS incomingEdges incomingBeforeDart middleDart
        · simp [incomingEdges]
        · exact Or.inl hfirst
      have hpredecessor : web.annular.RS.phi.symm outgoingDart =
          middleDart := by
        apply web.annular.RS.phi.injective
        simp [hsecond]
      rw [hpredecessor]
      exact hmiddle

/-- The symmetric second side: the outgoing-after occurrence is either in
the incoming carrier or has its immediate face successor there. -/
theorem SourceLocalRailSuccessor.rightOutgoingAfter_mem_or_successor_mem
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique leftInterior}
    {leftBefore leftAfter :
      {position // position ∈ placementSidePositions leftPlacement}}
    {hleftBefore : leftPlacement.outgoingPosition.val ≡
      leftBefore.1.val + 1 [MOD 6]}
    {hleftAfter : leftAfter.1.val ≡
      leftPlacement.outgoingPosition.val + 1 [MOD 6]}
    {rightPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique (nextCorridorInterior leftInterior hnext)}
    (successor : SourceLocalRailSuccessor hnext leftPlacement leftBefore
      leftAfter hleftBefore hleftAfter rightPlacement) :
    let incomingBeforeDart := faceCycleDart web.annular.RS
      rightPlacement.root successor.rightBefore.1
    let incomingAfterDart := faceCycleDart web.annular.RS
      rightPlacement.root successor.rightAfter.1
    let outgoingDart := faceCycleDart web.annular.RS rightPlacement.root
      successor.rightOutgoingAfter.1
    let incomingEdges : Finset G.edgeSet :=
      {web.annular.RS.edgeOf incomingBeforeDart,
        web.annular.RS.edgeOf incomingAfterDart}
    outgoingDart ∈ closedDartCarrier web.annular.RS incomingEdges ∨
      web.annular.RS.phi outgoingDart ∈
        closedDartCarrier web.annular.RS incomingEdges := by
  dsimp only
  let incomingBeforeDart := faceCycleDart web.annular.RS
    rightPlacement.root successor.rightBefore.1
  let incomingAfterDart := faceCycleDart web.annular.RS
    rightPlacement.root successor.rightAfter.1
  let outgoingDart := faceCycleDart web.annular.RS rightPlacement.root
    successor.rightOutgoingAfter.1
  let incomingEdges : Finset G.edgeSet :=
    {web.annular.RS.edgeOf incomingBeforeDart,
      web.annular.RS.edgeOf incomingAfterDart}
  cases successor.shape with
  | forwardTwo _first_eq middle outgoing_to_middle middle_to_incoming =>
      right
      let middleDart := faceCycleDart web.annular.RS rightPlacement.root middle.1
      have hfirst : middleDart = web.annular.RS.phi outgoingDart :=
        faceCycleDart_successor_of_modEq web.annular.RS rightPlacement.root
          rightPlacement.orbit_card successor.rightOutgoingAfter.1 middle.1
            outgoing_to_middle
      have hsecond : incomingAfterDart = web.annular.RS.phi middleDart :=
        faceCycleDart_successor_of_modEq web.annular.RS rightPlacement.root
          rightPlacement.orbit_card middle.1 successor.rightAfter.1
            middle_to_incoming
      have hmiddle : middleDart ∈
          closedDartCarrier web.annular.RS incomingEdges := by
        have hmiddleEq : middleDart = web.annular.RS.phi.symm incomingAfterDart := by
          apply web.annular.RS.phi.injective
          simp [hsecond]
        apply mem_closedDartCarrier_of_face_neighbor_of_edge_mem
          web.annular.RS incomingEdges incomingAfterDart middleDart
        · simp [incomingEdges]
        · exact Or.inr hmiddleEq
      rw [← hfirst]
      exact hmiddle
  | forwardThree _first_step second_step =>
      left
      have hstep : incomingAfterDart = web.annular.RS.phi outgoingDart :=
        faceCycleDart_successor_of_modEq web.annular.RS rightPlacement.root
          rightPlacement.orbit_card successor.rightOutgoingAfter.1
            successor.rightAfter.1 second_step
      have houtgoingEq : outgoingDart =
          web.annular.RS.phi.symm incomingAfterDart := by
        apply web.annular.RS.phi.injective
        simp [hstep]
      apply mem_closedDartCarrier_of_face_neighbor_of_edge_mem
        web.annular.RS incomingEdges incomingAfterDart outgoingDart
      · simp [incomingEdges]
      · exact Or.inr houtgoingEq
  | forwardFour _middle _hincomingMiddle _hmiddleOutgoing second_eq =>
      left
      apply mem_closedDartCarrier_of_edge_mem
      simp [second_eq]

/-- The independently selected source witnesses at two consecutive serial
Cells have a literal successor package whose outgoing flank coordinates are
exactly the next witness's named coordinates. -/
theorem exists_sourceLocalLayerSerialCellRebase_successor_coordinates
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    let leftWitness := localLayerPairWitnessOfCorridor corridor hunique
      (sourceLocalLayerInteriorAt offset)
      (sourceLocalLayerInteriorAt_hasNext offset)
    let target := sourceLocalLayerNextOffset offset hnext
    let rightWitness := localLayerPairWitnessOfCorridor corridor hunique
      (sourceLocalLayerInteriorAt target)
      (sourceLocalLayerInteriorAt_hasNext target)
    ∃ successor : SourceLocalRailSuccessor
        (sourceLocalLayerInteriorAt_hasNext offset)
        leftWitness.placement leftWitness.before leftWitness.after
        leftWitness.outgoing_after_before leftWitness.after_after_outgoing
        rightWitness.placement,
      successor.rightOutgoingBefore = rightWitness.before ∧
        successor.rightOutgoingAfter = rightWitness.after ∧
        web.annular.RS.edgeOf
            (faceCycleDart web.annular.RS rightWitness.placement.root
              successor.rightBefore.1) =
          sourceLocalLayerRightCrossingAt corridor hunique offset (0 : Fin 2) ∧
        web.annular.RS.edgeOf
            (faceCycleDart web.annular.RS rightWitness.placement.root
              successor.rightAfter.1) =
          sourceLocalLayerRightCrossingAt corridor hunique offset (1 : Fin 2) ∧
        web.annular.RS.edgeOf
            (faceCycleDart web.annular.RS rightWitness.placement.root
              successor.rightOutgoingBefore.1) =
          sourceLocalLayerLeftCrossingAt corridor hunique target (0 : Fin 2) ∧
        web.annular.RS.edgeOf
            (faceCycleDart web.annular.RS rightWitness.placement.root
              successor.rightOutgoingAfter.1) =
          sourceLocalLayerLeftCrossingAt corridor hunique target (1 : Fin 2) := by
  dsimp only
  let leftWitness := localLayerPairWitnessOfCorridor corridor hunique
    (sourceLocalLayerInteriorAt offset)
    (sourceLocalLayerInteriorAt_hasNext offset)
  let target := sourceLocalLayerNextOffset offset hnext
  let rightWitness := localLayerPairWitnessOfCorridor corridor hunique
    (sourceLocalLayerInteriorAt target)
    (sourceLocalLayerInteriorAt_hasNext target)
  rcases exists_nextSourceLocalRailWalkPair
      (sourceLocalLayerInteriorAt_hasNext offset) leftWitness.placement
      leftWitness.before leftWitness.after
      leftWitness.outgoing_after_before leftWitness.after_after_outgoing
      rightWitness.placement with ⟨successor⟩
  have houtgoingBefore := successor.rightOutgoingBefore_eq_witnessBefore
  have houtgoingAfter := successor.rightOutgoingAfter_eq_witnessAfter
  refine ⟨successor, houtgoingBefore, houtgoingAfter, ?_, ?_, ?_, ?_⟩
  · calc
      web.annular.RS.edgeOf
          (faceCycleDart web.annular.RS rightWitness.placement.root
            successor.rightBefore.1) =
          web.annular.RS.edgeOf
            (web.annular.RS.rho (web.annular.RS.phi
              (faceCycleDart web.annular.RS leftWitness.placement.root
                leftWitness.before.1))) := successor.beforeEdge_eq
      _ = sourceLocalLayerRightCrossingAt corridor hunique offset
          (0 : Fin 2) := by
        symm
        simpa [sourceLocalLayerRightCrossingAt, sourceLocalLayerPairAt,
          sourceLocalLayerPair, localLayerPairOfCorridor, leftWitness,
          LocalLayerPair.secondLayer,
          GoertzelV24AnnularCrosscut.SimpleDualCrosscut.crossingEdge] using
            leftWitness.secondWalk_crossingEdge_zero_eq_beforeThirdEdge
  · calc
      web.annular.RS.edgeOf
          (faceCycleDart web.annular.RS rightWitness.placement.root
            successor.rightAfter.1) =
          web.annular.RS.edgeOf
            (web.annular.RS.rho (web.annular.RS.phi
              (faceCycleDart web.annular.RS leftWitness.placement.root
                leftWitness.placement.outgoingPosition))) :=
        successor.afterEdge_eq
      _ = sourceLocalLayerRightCrossingAt corridor hunique offset
          (1 : Fin 2) := by
        symm
        simpa [sourceLocalLayerRightCrossingAt, sourceLocalLayerPairAt,
          sourceLocalLayerPair, localLayerPairOfCorridor, leftWitness,
          LocalLayerPair.secondLayer,
          GoertzelV24AnnularCrosscut.SimpleDualCrosscut.crossingEdge] using
            leftWitness.secondWalk_crossingEdge_one_eq_afterThirdEdge
  · rw [houtgoingBefore]
    simpa [sourceLocalLayerLeftCrossingAt, sourceLocalLayerPairAt,
      sourceLocalLayerPair, localLayerPairOfCorridor, rightWitness, target,
      LocalLayerPair.firstLayer,
      GoertzelV24AnnularCrosscut.SimpleDualCrosscut.crossingEdge] using
        rightWitness.firstWalk_crossingEdge_zero_eq_beforeEdge.symm
  · rw [houtgoingAfter]
    simpa [sourceLocalLayerLeftCrossingAt, sourceLocalLayerPairAt,
      sourceLocalLayerPair, localLayerPairOfCorridor, rightWitness, target,
      LocalLayerPair.firstLayer,
      GoertzelV24AnnularCrosscut.SimpleDualCrosscut.crossingEdge] using
        rightWitness.firstWalk_crossingEdge_one_eq_afterEdge.symm

/-- The two successor outgoing occurrences on the centre face are localized
in the old rolling carrier of the preceding Cell.  This is the serial form of
the finite three-shape calculation above: no witness choice remains hidden,
and the carrier is the indexed one used by the exact rebase interface. -/
theorem exists_sourceLocalLayerSerialCellRebase_successor_coordinate_locality
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    let leftWitness := localLayerPairWitnessOfCorridor corridor hunique
      (sourceLocalLayerInteriorAt offset)
      (sourceLocalLayerInteriorAt_hasNext offset)
    let target := sourceLocalLayerNextOffset offset hnext
    let rightWitness := localLayerPairWitnessOfCorridor corridor hunique
      (sourceLocalLayerInteriorAt target)
      (sourceLocalLayerInteriorAt_hasNext target)
    ∃ successor : SourceLocalRailSuccessor
        (sourceLocalLayerInteriorAt_hasNext offset)
        leftWitness.placement leftWitness.before leftWitness.after
        leftWitness.outgoing_after_before leftWitness.after_after_outgoing
        rightWitness.placement,
      let outgoingBeforeDart := faceCycleDart web.annular.RS
        rightWitness.placement.root successor.rightOutgoingBefore.1
      let outgoingAfterDart := faceCycleDart web.annular.RS
        rightWitness.placement.root successor.rightOutgoingAfter.1
      (outgoingBeforeDart ∈
          sourceLocalLayerSerialFaceOutgoingDartCarrierAt corridor hunique
            offset ∨
        web.annular.RS.phi.symm outgoingBeforeDart ∈
          sourceLocalLayerSerialFaceOutgoingDartCarrierAt corridor hunique
            offset) ∧
      (outgoingAfterDart ∈
          sourceLocalLayerSerialFaceOutgoingDartCarrierAt corridor hunique
            offset ∨
        web.annular.RS.phi outgoingAfterDart ∈
          sourceLocalLayerSerialFaceOutgoingDartCarrierAt corridor hunique
            offset) := by
  dsimp only
  let leftWitness := localLayerPairWitnessOfCorridor corridor hunique
    (sourceLocalLayerInteriorAt offset)
    (sourceLocalLayerInteriorAt_hasNext offset)
  let target := sourceLocalLayerNextOffset offset hnext
  let rightWitness := localLayerPairWitnessOfCorridor corridor hunique
    (sourceLocalLayerInteriorAt target)
    (sourceLocalLayerInteriorAt_hasNext target)
  rcases exists_sourceLocalLayerSerialCellRebase_successor_coordinates
      corridor hunique offset hnext with
    ⟨successor, _houtgoingBefore, _houtgoingAfter, hincomingBefore,
      hincomingAfter, _houtgoingBeforeEdge, _houtgoingAfterEdge⟩
  refine ⟨successor, ?_, ?_⟩
  · have hlocal := successor.rightOutgoingBefore_mem_or_predecessor_mem
    have hincomingEdges :
        {web.annular.RS.edgeOf
            (faceCycleDart web.annular.RS rightWitness.placement.root
              successor.rightBefore.1),
          web.annular.RS.edgeOf
            (faceCycleDart web.annular.RS rightWitness.placement.root
              successor.rightAfter.1)} =
        indexedCrossingEdgeSet
          (sourceLocalLayerRightCrossingAt corridor hunique offset) := by
      rw [hincomingBefore, hincomingAfter]
      ext edge
      simp only [Finset.mem_insert, Finset.mem_singleton,
        mem_indexedCrossingEdgeSet_iff]
      constructor
      · rintro (hedge | hedge)
        · exact ⟨0, hedge.symm⟩
        · exact ⟨1, hedge.symm⟩
      · rintro ⟨index, hedge⟩
        fin_cases index
        · exact Or.inl hedge.symm
        · exact Or.inr hedge.symm
    dsimp only at hlocal
    rw [hincomingEdges] at hlocal
    simpa [sourceLocalLayerSerialFaceOutgoingDartCarrierAt] using hlocal
  · have hlocal := successor.rightOutgoingAfter_mem_or_successor_mem
    have hincomingEdges :
        {web.annular.RS.edgeOf
            (faceCycleDart web.annular.RS rightWitness.placement.root
              successor.rightBefore.1),
          web.annular.RS.edgeOf
            (faceCycleDart web.annular.RS rightWitness.placement.root
              successor.rightAfter.1)} =
        indexedCrossingEdgeSet
          (sourceLocalLayerRightCrossingAt corridor hunique offset) := by
      rw [hincomingBefore, hincomingAfter]
      ext edge
      simp only [Finset.mem_insert, Finset.mem_singleton,
        mem_indexedCrossingEdgeSet_iff]
      constructor
      · rintro (hedge | hedge)
        · exact ⟨0, hedge.symm⟩
        · exact ⟨1, hedge.symm⟩
      · rintro ⟨index, hedge⟩
        fin_cases index
        · exact Or.inl hedge.symm
        · exact Or.inr hedge.symm
    dsimp only at hlocal
    rw [hincomingEdges] at hlocal
    simpa [sourceLocalLayerSerialFaceOutgoingDartCarrierAt] using hlocal

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
