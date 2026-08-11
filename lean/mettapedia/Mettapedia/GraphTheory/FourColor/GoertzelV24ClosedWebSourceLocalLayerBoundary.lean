import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerFormation
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSpliceBoundary

/-!
# Source-derived local Cell-3 splice boundary

Addendum XXVII(iii) takes its finite profiles on simple layer boundaries.
The local geometry and the ordered-splice adapter were deliberately proved in
separate modules: the former stays on the light open-tangle import surface,
while the latter owns the deletion-component API.  This file is their narrow
composition.  A boundary-clean Cell-3 corridor now supplies the actual local
layer pair and hence the concrete ordered cut data; no caller chooses the two
rail faces and no chord wall is presented as a transversal.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularCrosscut
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24SpliceUnification
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebSourceLocalLayerBoundaryEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The literal two-rail layer pair selected by the actual Cell-3 corridor.
This is merely the source-derived choice constructed in
`localLayerPairOfCorridor`, named here so the splice adapter has a single
entry point. -/
noncomputable def sourceLocalLayerPair
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    LocalLayerPair web corridor leftInterior hnext :=
  localLayerPairOfCorridor corridor hunique leftInterior hnext

/-- The source-selected Cell-3 rails carry the exact deletion-side package
needed by the open splice.  The component, the removed vertex, crossing
orientations, and port order are all constructed by the existing local
boundary proof after the rails above have been derived from the source face. -/
theorem sourceLocalLayerPair_crosscutBoundaryData_nonempty
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    Nonempty (SeparatedAlignedSimpleDualCrosscuts.SourceCrosscutBoundaryData
      web.annular.cellulation.rotation
      ((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
        hunique)) :=
  (sourceLocalLayerPair corridor hunique leftInterior hnext).sourceCrosscutBoundaryData_nonempty
    hunique

/-- The canonical source-derived deletion-side package for a Cell-3 local
layer.  It is a real simple-layer boundary, not a syntactic profile carrier or
an arbitrary cyclic cut. -/
noncomputable def sourceLocalLayerPairCrosscutBoundaryData
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    SeparatedAlignedSimpleDualCrosscuts.SourceCrosscutBoundaryData
      web.annular.cellulation.rotation
      ((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
        hunique) :=
  (sourceLocalLayerPair corridor hunique leftInterior hnext).sourceCrosscutBoundaryData hunique

/-- The source-selected simple layer is now in the ordered port carrier used
by the finite profile and splice constructions. -/
noncomputable def sourceLocalLayerPairOrderedCutSidesData
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    OrderedCutSidesData web.annular.RS
      (sourceLocalLayerPair corridor hunique leftInterior hnext).firstLayer.walk.length 0
      (((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
        hunique).sourceCrosscutFaceFragmentCount
          web.annular.cellulation.rotation
          (sourceLocalLayerPairCrosscutBoundaryData corridor hunique leftInterior hnext)) :=
  (sourceLocalLayerPair corridor hunique leftInterior hnext).orderedCutSidesData hunique

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
