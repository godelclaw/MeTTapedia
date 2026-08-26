import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalInterfaceOrientation
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedFaceBoundary

/-!
# The consumed rung is facially exposed to the old Cell carrier

The shared rung retained during one literal Cell update may itself be absent
from the rolling facial carrier.  It is nevertheless a genuine boundary
vertex of the carrier's strict exterior: on the current hexagon its two face
neighbours are the incoming Cell crossings, while on the next hexagon they
are the outgoing Cell crossings.

This is the first source-geometric case of the expanded-interface locality
obligation.  It uses the actual consecutive Cell placements, not a global
planarity or saturation assumption.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabSideAdjacency
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationFaceRegionalDartCarrier
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cellRebaseSharedRungBoundaryEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- Every dart over the consumed shared rung has both immediate face
neighbours in the old rolling facial carrier.  The two orientations are
handled by the current and next literal hexagons respectively. -/
theorem sourceLocalLayerSerialCellRebase_sharedRung_faceNeighbors_mem_oldCarrier
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (dart : web.annular.RS.D)
    (hrung : web.annular.RS.edgeOf dart =
      sourceLocalLayerSharedRungAt corridor hunique offset) :
    web.annular.RS.phi dart ∈
        sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset ∧
      web.annular.RS.phi.symm dart ∈
        sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset := by
  let interior := sourceLocalLayerInteriorAt offset
  let hnextInterior := sourceLocalLayerInteriorAt_hasNext offset
  let witness := localLayerPairWitnessOfCorridor corridor hunique interior
    hnextInterior
  let outgoingDart := faceCycleDart web.annular.RS witness.placement.root
    witness.placement.outgoingPosition
  have houtgoingEdge : web.annular.RS.edgeOf outgoingDart =
      sourceLocalLayerSharedRungAt corridor hunique offset := by
    change faceCycleEdge web.annular.RS witness.placement.root
        witness.placement.outgoingPosition =
      sourceLocalLayerSharedRungAt corridor hunique offset
    simpa [sourceLocalLayerSharedRungAt, interior] using
      witness.placement.outgoing_edge
  have hedge : web.annular.RS.edgeOf dart =
      web.annular.RS.edgeOf outgoingDart := hrung.trans houtgoingEdge.symm
  rcases web.annular.RS.edge_fiber_two_cases
      (e := web.annular.RS.edgeOf dart) (d := dart) (y := outgoingDart)
      rfl hedge.symm with hsame | hopposite
  · subst dart
    let beforeDart := faceCycleDart web.annular.RS witness.placement.root
      witness.before.1
    let afterDart := faceCycleDart web.annular.RS witness.placement.root
      witness.after.1
    have hbefore : outgoingDart = web.annular.RS.phi beforeDart := by
      exact faceCycleDart_successor_of_modEq web.annular.RS
        witness.placement.root witness.placement.orbit_card witness.before.1
          witness.placement.outgoingPosition witness.outgoing_after_before
    have hafter : afterDart = web.annular.RS.phi outgoingDart := by
      exact faceCycleDart_successor_of_modEq web.annular.RS
        witness.placement.root witness.placement.orbit_card
          witness.placement.outgoingPosition witness.after.1
            witness.after_after_outgoing
    have hbeforeEdge : web.annular.RS.edgeOf beforeDart =
        sourceLocalLayerLeftCrossingAt corridor hunique offset (0 : Fin 2) := by
      simpa [sourceLocalLayerLeftCrossingAt, sourceLocalLayerPairAt,
        sourceLocalLayerPair, localLayerPairOfCorridor, interior, witness,
        beforeDart, LocalLayerPair.firstLayer,
        GoertzelV24AnnularCrosscut.SimpleDualCrosscut.crossingEdge] using
          witness.firstWalk_crossingEdge_zero_eq_beforeEdge.symm
    have hafterEdge : web.annular.RS.edgeOf afterDart =
        sourceLocalLayerLeftCrossingAt corridor hunique offset (1 : Fin 2) := by
      simpa [sourceLocalLayerLeftCrossingAt, sourceLocalLayerPairAt,
        sourceLocalLayerPair, localLayerPairOfCorridor, interior, witness,
        afterDart, LocalLayerPair.firstLayer,
        GoertzelV24AnnularCrosscut.SimpleDualCrosscut.crossingEdge] using
          witness.firstWalk_crossingEdge_one_eq_afterEdge.symm
    constructor
    · rw [← hafter]
      apply Finset.mem_union_left
      rw [mem_dartsOnEdges_iff, hafterEdge]
      exact sourceLocalLayerCellRegionAt_leftCrossing corridor hunique offset 1
    · have hsymm : web.annular.RS.phi.symm outgoingDart = beforeDart := by
        apply web.annular.RS.phi.injective
        simp [hbefore]
      rw [hsymm]
      apply Finset.mem_union_left
      rw [mem_dartsOnEdges_iff, hbeforeEdge]
      exact sourceLocalLayerCellRegionAt_leftCrossing corridor hunique offset 0
  · have hdart : dart = web.annular.RS.alpha outgoingDart := by
      simpa using (congrArg web.annular.RS.alpha hopposite).symm
    subst dart
    let rightInterior := nextCorridorInterior interior hnextInterior
    let rightPlacement := localInternalHexRungPlacement corridor hunique
      rightInterior
    let incomingDart := faceCycleDart web.annular.RS rightPlacement.root
      rightPlacement.incomingPosition
    have hincoming : incomingDart = web.annular.RS.alpha outgoingDart := by
      simpa [rightInterior, incomingDart, outgoingDart] using
        nextLocalPlacement_incomingDart_eq_alpha_outgoingDart interior
          hnextInterior witness.placement rightPlacement
    rcases exists_canonicalNextLocalPlacementRailEdges corridor hunique interior
        hnextInterior with
      ⟨rightBefore, rightAfter, _hne, hbeforeMod, hafterMod,
        hbeforeEdge, _hbeforeFace, hafterEdge, _hafterFace⟩
    let beforeDart := faceCycleDart web.annular.RS rightPlacement.root
      rightBefore.1
    let afterDart := faceCycleDart web.annular.RS rightPlacement.root
      rightAfter.1
    have hbefore : beforeDart = web.annular.RS.phi incomingDart := by
      exact faceCycleDart_successor_of_modEq web.annular.RS
        rightPlacement.root rightPlacement.orbit_card
          rightPlacement.incomingPosition rightBefore.1 hbeforeMod
    have hafter : incomingDart = web.annular.RS.phi afterDart := by
      exact faceCycleDart_successor_of_modEq web.annular.RS
        rightPlacement.root rightPlacement.orbit_card rightAfter.1
          rightPlacement.incomingPosition hafterMod
    have hbeforeCrossing : web.annular.RS.edgeOf beforeDart =
        sourceLocalLayerRightCrossingAt corridor hunique offset (0 : Fin 2) := by
      calc
        web.annular.RS.edgeOf beforeDart =
            web.annular.RS.edgeOf
              (web.annular.RS.rho (web.annular.RS.phi
                (faceCycleDart web.annular.RS witness.placement.root
                  witness.before.1))) := hbeforeEdge
        _ = sourceLocalLayerRightCrossingAt corridor hunique offset
            (0 : Fin 2) := by
          symm
          simpa [sourceLocalLayerRightCrossingAt, sourceLocalLayerPairAt,
            sourceLocalLayerPair, localLayerPairOfCorridor, interior, witness,
            LocalLayerPair.secondLayer,
            GoertzelV24AnnularCrosscut.SimpleDualCrosscut.crossingEdge] using
              witness.secondWalk_crossingEdge_zero_eq_beforeThirdEdge
    have hafterCrossing : web.annular.RS.edgeOf afterDart =
        sourceLocalLayerRightCrossingAt corridor hunique offset (1 : Fin 2) := by
      calc
        web.annular.RS.edgeOf afterDart =
            web.annular.RS.edgeOf
              (web.annular.RS.rho (web.annular.RS.phi
                (faceCycleDart web.annular.RS witness.placement.root
                  witness.placement.outgoingPosition))) := hafterEdge
        _ = sourceLocalLayerRightCrossingAt corridor hunique offset
            (1 : Fin 2) := by
          symm
          simpa [sourceLocalLayerRightCrossingAt, sourceLocalLayerPairAt,
            sourceLocalLayerPair, localLayerPairOfCorridor, interior, witness,
            LocalLayerPair.secondLayer,
            GoertzelV24AnnularCrosscut.SimpleDualCrosscut.crossingEdge] using
              witness.secondWalk_crossingEdge_one_eq_afterThirdEdge
    constructor
    · rw [← hincoming, ← hbefore]
      apply Finset.mem_union_right
      apply mem_closedDartCarrier_of_edge_mem
      rw [hbeforeCrossing]
      exact (mem_indexedCrossingEdgeSet_iff _ _).2 ⟨0, rfl⟩
    · rw [← hincoming]
      have hsymm : web.annular.RS.phi.symm incomingDart = afterDart := by
        apply web.annular.RS.phi.injective
        simp [hafter]
      rw [hsymm]
      apply Finset.mem_union_right
      apply mem_closedDartCarrier_of_edge_mem
      rw [hafterCrossing]
      exact (mem_indexedCrossingEdgeSet_iff _ _).2 ⟨1, rfl⟩

/-- The forward face neighbour of a consumed-rung occurrence lies over a
literal Cell crossing: the second incoming crossing on the current face, or
the first outgoing crossing on the successor face according to orientation. -/
theorem sourceLocalLayerSerialCellRebase_sharedRung_phi_edge_eq_crossing
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (dart : web.annular.RS.D)
    (hrung : web.annular.RS.edgeOf dart =
      sourceLocalLayerSharedRungAt corridor hunique offset) :
    web.annular.RS.edgeOf (web.annular.RS.phi dart) =
        sourceLocalLayerLeftCrossingAt corridor hunique offset (1 : Fin 2) ∨
      web.annular.RS.edgeOf (web.annular.RS.phi dart) =
        sourceLocalLayerRightCrossingAt corridor hunique offset (0 : Fin 2) := by
  let interior := sourceLocalLayerInteriorAt offset
  let hnextInterior := sourceLocalLayerInteriorAt_hasNext offset
  let witness := localLayerPairWitnessOfCorridor corridor hunique interior
    hnextInterior
  let outgoingDart := faceCycleDart web.annular.RS witness.placement.root
    witness.placement.outgoingPosition
  have houtgoingEdge : web.annular.RS.edgeOf outgoingDart =
      sourceLocalLayerSharedRungAt corridor hunique offset := by
    change faceCycleEdge web.annular.RS witness.placement.root
        witness.placement.outgoingPosition =
      sourceLocalLayerSharedRungAt corridor hunique offset
    simpa [sourceLocalLayerSharedRungAt, interior] using
      witness.placement.outgoing_edge
  have hedge : web.annular.RS.edgeOf dart =
      web.annular.RS.edgeOf outgoingDart := hrung.trans houtgoingEdge.symm
  rcases web.annular.RS.edge_fiber_two_cases
      (e := web.annular.RS.edgeOf dart) (d := dart) (y := outgoingDart)
      rfl hedge.symm with hsame | hopposite
  · subst dart
    left
    let afterDart := faceCycleDart web.annular.RS witness.placement.root
      witness.after.1
    have hafter : afterDart = web.annular.RS.phi outgoingDart := by
      exact faceCycleDart_successor_of_modEq web.annular.RS
        witness.placement.root witness.placement.orbit_card
          witness.placement.outgoingPosition witness.after.1
            witness.after_after_outgoing
    have hafterEdge : web.annular.RS.edgeOf afterDart =
        sourceLocalLayerLeftCrossingAt corridor hunique offset (1 : Fin 2) := by
      simpa [sourceLocalLayerLeftCrossingAt, sourceLocalLayerPairAt,
        sourceLocalLayerPair, localLayerPairOfCorridor, interior, witness,
        afterDart, LocalLayerPair.firstLayer,
        GoertzelV24AnnularCrosscut.SimpleDualCrosscut.crossingEdge] using
          witness.firstWalk_crossingEdge_one_eq_afterEdge.symm
    rw [← hafter]
    exact hafterEdge
  · have hdart : dart = web.annular.RS.alpha outgoingDart := by
      simpa using (congrArg web.annular.RS.alpha hopposite).symm
    subst dart
    right
    let rightInterior := nextCorridorInterior interior hnextInterior
    let rightPlacement := localInternalHexRungPlacement corridor hunique
      rightInterior
    let incomingDart := faceCycleDart web.annular.RS rightPlacement.root
      rightPlacement.incomingPosition
    have hincoming : incomingDart = web.annular.RS.alpha outgoingDart := by
      simpa [rightInterior, incomingDart, outgoingDart] using
        nextLocalPlacement_incomingDart_eq_alpha_outgoingDart interior
          hnextInterior witness.placement rightPlacement
    rcases exists_canonicalNextLocalPlacementRailEdges corridor hunique interior
        hnextInterior with
      ⟨rightBefore, _rightAfter, _hne, hbeforeMod, _hafterMod,
        hbeforeEdge, _hbeforeFace, _hafterEdge, _hafterFace⟩
    let beforeDart := faceCycleDart web.annular.RS rightPlacement.root
      rightBefore.1
    have hbefore : beforeDart = web.annular.RS.phi incomingDart := by
      exact faceCycleDart_successor_of_modEq web.annular.RS
        rightPlacement.root rightPlacement.orbit_card
          rightPlacement.incomingPosition rightBefore.1 hbeforeMod
    have hbeforeCrossing : web.annular.RS.edgeOf beforeDart =
        sourceLocalLayerRightCrossingAt corridor hunique offset (0 : Fin 2) := by
      calc
        web.annular.RS.edgeOf beforeDart =
            web.annular.RS.edgeOf
              (web.annular.RS.rho (web.annular.RS.phi
                (faceCycleDart web.annular.RS witness.placement.root
                  witness.before.1))) := hbeforeEdge
        _ = sourceLocalLayerRightCrossingAt corridor hunique offset
            (0 : Fin 2) := by
          symm
          simpa [sourceLocalLayerRightCrossingAt, sourceLocalLayerPairAt,
            sourceLocalLayerPair, localLayerPairOfCorridor, interior, witness,
            LocalLayerPair.secondLayer,
            GoertzelV24AnnularCrosscut.SimpleDualCrosscut.crossingEdge] using
              witness.secondWalk_crossingEdge_zero_eq_beforeThirdEdge
    rw [← hincoming, ← hbefore]
    exact hbeforeCrossing

/-- The forward face neighbour of a consumed-rung occurrence is present in
the literal pre-rebase region. -/
theorem sourceLocalLayerSerialCellRebase_sharedRung_phi_edge_mem_preRebase
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (dart : web.annular.RS.D)
    (hrung : web.annular.RS.edgeOf dart =
      sourceLocalLayerSharedRungAt corridor hunique offset) :
    web.annular.RS.edgeOf (web.annular.RS.phi dart) ∈
      sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset := by
  rcases sourceLocalLayerSerialCellRebase_sharedRung_phi_edge_eq_crossing
      corridor hunique offset dart hrung with hleft | hright
  · rw [hleft, sourceLocalLayerSerialPreRebaseOutputRegionAt]
    apply Finset.mem_union_left
    rw [sourceLocalLayerSerialOutputRegionAt,
      sourceLocalLayerSerialPrefixRegion_succ corridor hunique offset.isLt]
    exact Finset.mem_union_right _
      (sourceLocalLayerCellRegionAt_leftCrossing corridor hunique offset 1)
  · rw [hright, sourceLocalLayerSerialPreRebaseOutputRegionAt]
    exact Finset.mem_union_left _
      (sourceLocalLayerSerialOutputRegionAt_rightCrossing corridor hunique
        offset 0)

/-- A genuinely new pre-rebase occurrence over the consumed rung has a
literal facial neighbour in the old rolling carrier.  This is the complete
boundary-locality discharge for the consumed-rung role. -/
theorem sourceLocalLayerSerialCellRebase_sharedRung_exists_oldNeighbor
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (dart : web.annular.RS.D)
    (hrung : web.annular.RS.edgeOf dart =
      sourceLocalLayerSharedRungAt corridor hunique offset)
    (hpresent : web.annular.RS.edgeOf dart ∈
      sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    (hnew : dart ∉
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset) :
    ∃ oldDart : {dart // dart ∈
        sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset},
      (faceRegionalDartGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        ).Adj oldDart.1 dart := by
  have hneighbors :=
    sourceLocalLayerSerialCellRebase_sharedRung_faceNeighbors_mem_oldCarrier
      corridor hunique offset dart hrung
  let oldDart : {dart // dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset} :=
    ⟨web.annular.RS.phi dart, hneighbors.1⟩
  refine ⟨oldDart, ?_⟩
  rw [faceRegionalDartGraph_adj]
  refine ⟨?_, Or.inr rfl, ?_, hpresent⟩
  · intro heq
    exact hnew (heq ▸ oldDart.2)
  · exact sourceLocalLayerSerialCellRebase_sharedRung_phi_edge_mem_preRebase
      corridor hunique offset dart hrung

/-- Every collar coordinate rooted at a consumed-rung occurrence satisfies
the boundary-locality obligation.  The centre uses the explicit neighbour;
the two neighbour coordinates are already in the old carrier and therefore
cannot satisfy the genuinely-new premise. -/
theorem sourceLocalLayerSerialCellRebase_sharedRung_collar_exists_oldNeighbor
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (occurrence : SourceLocalLayerBoundaryRebaseFaceOccurrenceAt corridor
      hunique offset hnext)
    (hrung : web.annular.RS.edgeOf occurrence.1 =
      sourceLocalLayerSharedRungAt corridor hunique offset)
    (direction : SourceLocalLayerSerialCellRebaseFaceCollarDirection)
    (hpresent : web.annular.RS.edgeOf
        (sourceLocalLayerSerialCellRebaseFaceCollarDartAt web.annular.RS
          occurrence.1 direction) ∈
      sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    (hnew : sourceLocalLayerSerialCellRebaseFaceCollarDartAt web.annular.RS
        occurrence.1 direction ∉
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset) :
    ∃ oldDart : {dart // dart ∈
        sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset},
      (faceRegionalDartGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        ).Adj oldDart.1
          (sourceLocalLayerSerialCellRebaseFaceCollarDartAt web.annular.RS
            occurrence.1 direction) := by
  have hneighbors :=
    sourceLocalLayerSerialCellRebase_sharedRung_faceNeighbors_mem_oldCarrier
      corridor hunique offset occurrence.1 hrung
  cases direction with
  | center =>
      exact sourceLocalLayerSerialCellRebase_sharedRung_exists_oldNeighbor
        corridor hunique offset occurrence.1 hrung hpresent hnew
  | forward =>
      exact (hnew hneighbors.1).elim
  | backward =>
      exact (hnew hneighbors.2).elim

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
