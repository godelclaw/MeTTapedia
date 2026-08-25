import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStableParametricCapState
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceRecurrence
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceEnlargementCappedDeletion

/-!
# A fixed sufficient cap for the facial Cell rebase

The published profile caps partial face progress at five.  During one rolling
interface advance, however, darts formerly in the strict exterior can become
explicit coordinates of the uniform Cell--rebase carrier.  Their distinct
edge labels must be subtracted from the old exterior-component weight.

The complete uniform carrier has at most forty-eight darts.  Consequently an
internal cap at `5 + 48 = 53` determines the exact published cap after every
possible promotion, without a boundary-locality assumption and without
enlarging the receipt again.  This is conservative: aliases and repeated edge
labels only lower the actual deletion count.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStableWideCapRebase

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceRecurrence
open GoertzelV24DegreeTwoExteriorBoundary
open GoertzelV24FaceOrbitIncidence
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceEnlargementCappedDeletion
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance faceDeletionStableWideCapRebaseEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The complete uniform interface bounds the number of distinct labels
promoted out of any old exterior component by forty-eight. -/
theorem sourceLocalLayerSerialCellRebase_promotedFaceLabels_card_le_fortyEight
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (component :
      (exteriorGraph
        (faceRegionalDartGraph web.annular.RS
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
            offset))
        (fun slot : Fin
          (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            offset).card =>
          ((carrierCoordinate
            (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
              offset)).symm slot).1)).ConnectedComponent) :
    (promotedExteriorComponentLabels
      (faceRegionalDartGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset))
      (fun slot : Fin
        (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
          ).card =>
        ((carrierCoordinate
          (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            offset)).symm slot).1)
      (sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor hunique offset
        hnext)
      web.annular.RS.edgeOf component).card ≤ 48 := by
  let uniform := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique offset hnext
  let graph := faceRegionalDartGraph web.annular.RS
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
  let oldCarrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
    hunique offset
  let oldDartAt := fun slot : Fin oldCarrier.card =>
    ((carrierCoordinate oldCarrier).symm slot).1
  let newDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
    hunique offset hnext
  have hcover : ∀ vertex : component,
      (∃ slot, newDartAt slot = vertex.1) →
        ∃ added : Fin uniform.card, newDartAt added = vertex.1 := by
    intro vertex hvertex
    exact hvertex
  have hlabels := card_promotedExteriorComponentLabels_le_card_added
    graph oldDartAt newDartAt newDartAt web.annular.RS.edgeOf component hcover
  have hcard : Fintype.card (Fin uniform.card) ≤ 48 := by
    simpa [uniform] using
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt_card_le_fortyEight_of_cell
        corridor hunique offset hnext hcell)
  exact hlabels.trans hcard

/-- A cap at fifty-three on an old exterior face component determines its
exact cap at five after every dart promoted by the uniform interface is
removed. -/
theorem sourceLocalLayerSerialCellRebase_min_faceSupport_sdiff_promoted_five_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (component :
      (exteriorGraph
        (faceRegionalDartGraph web.annular.RS
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
            offset))
        (fun slot : Fin
          (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            offset).card =>
          ((carrierCoordinate
            (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
              offset)).symm slot).1)).ConnectedComponent) :
    let graph := faceRegionalDartGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    let oldCarrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
      hunique offset
    let oldDartAt := fun slot : Fin oldCarrier.card =>
      ((carrierCoordinate oldCarrier).symm slot).1
    let newDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
      hunique offset hnext
    min ((exteriorComponentLabelSupport graph oldDartAt web.annular.RS.edgeOf
          component) \
        promotedExteriorComponentLabels graph oldDartAt newDartAt
          web.annular.RS.edgeOf component).card 5 =
      min (min (exteriorComponentLabelSupport graph oldDartAt
          web.annular.RS.edgeOf component).card 53 -
        (promotedExteriorComponentLabels graph oldDartAt newDartAt
          web.annular.RS.edgeOf component).card) 5 := by
  dsimp only
  let uniform := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique offset hnext
  let graph := faceRegionalDartGraph web.annular.RS
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
  let oldCarrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
    hunique offset
  let oldDartAt := fun slot : Fin oldCarrier.card =>
    ((carrierCoordinate oldCarrier).symm slot).1
  let newDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
    hunique offset hnext
  have hcover : ∀ vertex : component,
      (∃ slot, newDartAt slot = vertex.1) →
        ∃ added : Fin uniform.card, newDartAt added = vertex.1 := by
    intro vertex hvertex
    exact hvertex
  have hcard : Fintype.card (Fin uniform.card) ≤ 48 := by
    simpa [uniform] using
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt_card_le_fortyEight_of_cell
        corridor hunique offset hnext hcell)
  exact min_componentLabelSupport_sdiff_promoted_five_eq_of_card_added_le
    graph oldDartAt newDartAt newDartAt web.annular.RS.edgeOf component 48
      hcover hcard

end

end GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStableWideCapRebase

end Mettapedia.GraphTheory.FourColor
