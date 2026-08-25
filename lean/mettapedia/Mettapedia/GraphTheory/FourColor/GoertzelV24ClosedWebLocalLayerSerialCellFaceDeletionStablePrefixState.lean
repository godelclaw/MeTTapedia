import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceTransitionCarrier
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactor

/-!
# A deletion-stable facial cumulative-prefix state

The component partition of a cumulative regional face graph is not stable
under deletion of the moving seam.  The bounded literal Cell carrier already
contains every dart occurrence through which the next local update can meet
the accumulated prefix, so the generic interface-exterior factor gives the
right finite state: literal adjacency on the carrier together with attachment
through components strictly outside it.

This file extracts that state on the at-most-twenty-four-dart facial carrier
and proves that it reconstructs prefix reachability after every carrier mask.
The result is the facial analogue of the deletion-stable tracked-prefix state.
It deliberately carries no component weights; the capped distinct-edge
measure requires an additional weighted refinement of this exact component
factor.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStablePrefixState

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24DeletionSensitivePortResidualFactorContraction
open GoertzelV24FaceOrbitIncidence
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance faceDeletionStablePrefixStateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The finite deletion-stable facial state of one cumulative prefix. -/
abbrev SourceLocalLayerSerialFaceDeletionStablePrefixState :=
  BoundedInterfaceExteriorFamilyCode 24 Unit

/-- Extract the exact mask-independent facial state on the literal rolling
Cell carrier. -/
noncomputable def sourceLocalLayerSerialFaceDeletionStablePrefixStateAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6) :
    SourceLocalLayerSerialFaceDeletionStablePrefixState :=
  let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    offset
  boundedInterfaceExteriorFamilyCode carrier 24
    (sourceLocalLayerSerialFaceTransitionCarrierAt_card_le_twentyFour corridor
      hunique offset hcell)
    (fun _ => faceRegionalDartGraph web.annular.RS
      (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset))

/-- The bounded state records the literal size of the rolling facial carrier. -/
@[simp]
theorem sourceLocalLayerSerialFaceDeletionStablePrefixStateAt_vertexCount
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6) :
    (sourceLocalLayerSerialFaceDeletionStablePrefixStateAt corridor hunique
      offset hcell).vertexCount.val =
      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
        ).card :=
  rfl

/-- The source-extracted state reconstructs cumulative facial reachability
after every deletion mask on the rolling Cell carrier. -/
theorem sourceLocalLayerSerialFaceDeletionStablePrefixStateAt_reachable_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (removed : Fin
      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
        ).card → Bool)
    (left right : SurvivingInterfaceSlot
      (fun slot : Fin
          (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
            ).card =>
        ((carrierCoordinate
          (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            offset)).symm slot).1)
      removed) :
    let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
      hunique offset
    let graph := faceRegionalDartGraph web.annular.RS
      (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
    let dartAt := fun slot : Fin carrier.card =>
      ((carrierCoordinate carrier).symm slot).1
    (restrictedByMask graph dartAt removed).Reachable
        (dartAt left.1) (dartAt right.1) ↔
      Relation.ReflTransGen
        (fun first second : SurvivingInterfaceSlot dartAt removed =>
          InterfaceExteriorFactoredStep
            ((sourceLocalLayerSerialFaceDeletionStablePrefixStateAt corridor
              hunique offset hcell).code ())
            first.1 second.1)
        left right := by
  dsimp only
  exact boundedInterfaceExteriorFamilyCode_reachable_iff
    (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset)
    24
    (sourceLocalLayerSerialFaceTransitionCarrierAt_card_le_twentyFour corridor
      hunique offset hcell)
    (fun _ => faceRegionalDartGraph web.annular.RS
      (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset))
    () removed left right

end

end GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStablePrefixState

end Mettapedia.GraphTheory.FourColor
