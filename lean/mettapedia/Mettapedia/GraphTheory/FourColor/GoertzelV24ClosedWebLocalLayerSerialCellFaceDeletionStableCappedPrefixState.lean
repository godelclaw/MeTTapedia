import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStablePrefixState
import Mettapedia.GraphTheory.FourColor.GoertzelV24CappedCardSubtraction
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationFaceInterfaceExteriorLabelCap

/-!
# Exterior-component edge caps in the cumulative facial prefix

The deletion-stable facial connectivity state is extended with the two
face-neighbour incidences of each carrier dart.  Every live incidence records
the strict-exterior face component that it enters and the cap at seven of that
component's distinct underlying primal edges.  The two extra units are the
exact lookahead budget needed when a rolling face path promotes at most its
two exterior endpoints; the published profile cap at five is recovered after
that bounded subtraction.

This is still mask-independent: a later rebase mask merely chooses which
interface darts survive.  No table indexed by all masks is introduced.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStableCappedPrefixState

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStablePrefixState
open GoertzelV24FaceOrbitIncidence
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24RotationFaceInterfaceExteriorLabelCap
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance faceDeletionStableCappedPrefixEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The finite weighted deletion-stable facial state of one cumulative
prefix. -/
abbrev SourceLocalLayerSerialFaceDeletionStableCappedPrefixState :=
  BoundedInterfaceExteriorLabelCapFamilyCode 24 Unit 7

/-- Extract exact exterior-component edge caps on the rolling literal-dart
carrier. -/
noncomputable def sourceLocalLayerSerialFaceDeletionStableCappedPrefixStateAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6) :
    SourceLocalLayerSerialFaceDeletionStableCappedPrefixState :=
  let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    offset
  let dartAt := fun slot : Fin carrier.card =>
    ((carrierCoordinate carrier).symm slot).1
  { vertexCount := ⟨carrier.card, Nat.lt_succ_of_le
      (sourceLocalLayerSerialFaceTransitionCarrierAt_card_le_twentyFour
        corridor hunique offset hcell)⟩
    code := fun _ => exactFaceInterfaceExteriorLabelCapCode web.annular.RS
      (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
      dartAt 7 }

@[simp]
theorem sourceLocalLayerSerialFaceDeletionStableCappedPrefixStateAt_vertexCount
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6) :
    (sourceLocalLayerSerialFaceDeletionStableCappedPrefixStateAt corridor
      hunique offset hcell).vertexCount.val =
        (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
          ).card :=
  rfl

/-- Forgetting the weighted rows recovers the exact deletion-stable
connectivity code already used by the facial recurrence. -/
theorem sourceLocalLayerSerialFaceDeletionStableCappedPrefixStateAt_connectivity
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6) :
    ((sourceLocalLayerSerialFaceDeletionStableCappedPrefixStateAt corridor
      hunique offset hcell).code ()).connectivity =
      (sourceLocalLayerSerialFaceDeletionStablePrefixStateAt corridor hunique
        offset hcell).code () :=
  rfl

/-- Each stored exterior incidence cap is the exact cap at seven of the
distinct primal edges in that strict-exterior component. -/
theorem sourceLocalLayerSerialFaceDeletionStableCappedPrefixStateAt_incidenceCap
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (incidence :
      Fin (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
        offset).card × Bool) :
    let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
      hunique offset
    let dartAt := fun slot : Fin carrier.card =>
      ((carrierCoordinate carrier).symm slot).1
    (((sourceLocalLayerSerialFaceDeletionStableCappedPrefixStateAt corridor
      hunique offset hcell).code ()).incidenceCap incidence).val =
      min (exteriorIncidenceLabelSupport
        (faceRegionalDartGraph web.annular.RS
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset))
        dartAt Prod.fst
        (faceInterfaceIncidenceVertex web.annular.RS dartAt)
        web.annular.RS.edgeOf incidence).card 7 := by
  dsimp only
  rfl

end

end GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStableCappedPrefixState

end Mettapedia.GraphTheory.FourColor
