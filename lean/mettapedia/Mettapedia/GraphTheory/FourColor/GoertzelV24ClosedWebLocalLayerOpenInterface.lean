import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutOpenInterface
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSeamAudit

/-!
# Open-interface realization of a source Cell-3 layer

Addendum XXVII takes profiles on completed simple transversals or layer
boundaries.  A Cell-3 tile supplies one local pair of rails, whose first old
endpoints can coincide; it is therefore not a closed retained-vertex splice
boundary.  Opening the four crossed edges is the source-faithful first step:
the literal fresh stubs form the input and output interfaces of an open
tangle, and corresponding stubs are automatically distinct.

This module exposes that fact for the source-selected local layer.  It does
not claim that one tile is already the completed annular splice boundary;
the corridor assembly remains responsible for that geometric construction.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularCrosscut
open GoertzelV24AnnularCrosscutSlitRotation
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebBoundaryData.AnnularBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerOpenInterfaceEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/- Keep the literal cut-dart interface on its ordinary subtype instances.
   The source local-layer modules use the same representation for concrete
   face-boundary incidence, so this avoids an irrelevant instance mismatch at
   the open-tangle boundary. -/
local instance closedWebLocalLayerOpenInterfaceCutDartFintype
    {RS : RotationSystem V G.edgeSet} (cut : Finset G.edgeSet) :
    Fintype (CutDart RS cut) :=
  Subtype.fintype _

local instance closedWebLocalLayerOpenInterfaceCutDartDecidableEq
    {RS : RotationSystem V G.edgeSet} (cut : Finset G.edgeSet) :
    DecidableEq (CutDart RS cut) :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The source-selected Cell-3 rail pair, viewed as the actual pair of
open interfaces on which the finite profile is read. -/
noncomputable abbrev sourceLocalLayerPairOpenInterfaces
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :=
  (sourceLocalLayerPair corridor hunique leftInterior hnext).alignedLocalLayerPair hunique

/-- Although the local rails share an old corner, after opening their crossed
edges every left/right port has a different literal boundary vertex.  Thus any
source-order matching between these two open interfaces is loop-free.  This
is the well-formedness premise needed by the later open-tangle composition,
without making the false closed-seam endpoint-disjointness claim. -/
theorem sourceLocalLayerPair_openInterface_matching_no_selfLoop
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength)
    (matching :
      (sourceLocalLayerPairOpenInterfaces corridor hunique leftInterior hnext).LeftInterfaceEnd →
        (sourceLocalLayerPairOpenInterfaces corridor hunique leftInterior hnext).RightInterfaceEnd) :
    ∀ left,
      ((sourceLocalLayerPairOpenInterfaces corridor hunique leftInterior hnext).slitRotationSystem).vertOf
          ((sourceLocalLayerPairOpenInterfaces corridor hunique leftInterior hnext).leftInterfaceStub left) ≠
        ((sourceLocalLayerPairOpenInterfaces corridor hunique leftInterior hnext).slitRotationSystem).vertOf
          ((sourceLocalLayerPairOpenInterfaces corridor hunique leftInterior hnext).rightInterfaceStub
            (matching left)) := by
  exact AlignedSimpleDualCrosscuts.openInterface_matching_no_selfLoop
    (sourceLocalLayerPairOpenInterfaces corridor hunique leftInterior hnext) matching

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
