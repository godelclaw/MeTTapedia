import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputCap
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFaceFiniteOutputPort

/-!
# Exact selected outgoing face-cap support

The outgoing cap counts distinct primal edges, not literal dart occurrences.
For a pointwise-selected output fragment, its edge support is exactly the
image under `edgeOf` of the complete regional dart component rooted at the
fragment's canonical outgoing cut occurrence.  Hence capping either support
at five gives the same result.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedFaceFiniteOutputCap

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputCap
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteOutputFragment
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteOutputPort
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedFaceFiniteOutputCapEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- A selected outgoing fragment and the complete regional component rooted
at its canonical cut dart have the same distinct primal-edge support. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentEdges_eq_componentEdges
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt
      formation corridor hinterior offset) :
    boundaryRegionalFragmentEdges formation.annular.RS
        (indexedCrossingEdgeSet
          (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
            hinterior offset))
        (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
          corridor hinterior offset) fragment =
      sourceLocalLayerBoundaryRebaseFaceComponentEdges formation.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
          corridor hinterior offset)
        (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt
          formation corridor hinterior offset fragment).1 := by
  exact boundaryRegionalFragmentEdges_eq_componentEdges
    formation.annular.RS
    (indexedCrossingEdgeSet
      (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
        hinterior offset))
    (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
      corridor hinterior offset) fragment

/-- The actual selected profile cap is the cap of that rooted component's
distinct primal-edge support. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceOutputFragment_min_card_eq_component
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt
      formation corridor hinterior offset) :
    min (boundaryRegionalFragmentEdges formation.annular.RS
        (indexedCrossingEdgeSet
          (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
            hinterior offset))
        (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
          corridor hinterior offset) fragment).card 5 =
      min (sourceLocalLayerBoundaryRebaseFaceComponentEdges
        formation.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
          corridor hinterior offset)
        (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt
          formation corridor hinterior offset fragment).1).card 5 := by
  rw [pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentEdges_eq_componentEdges
    formation corridor hinterior offset fragment]

end

end GoertzelV24ClosedWebPointwiseSelectedFaceFiniteOutputCap

end Mettapedia.GraphTheory.FourColor
