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

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
