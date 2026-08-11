import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorLocalSourceSplice
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedCutSerialOpenTangle

/-!
# Source corridor cells as serial open tangles

Each consecutive Cell-3 slab interface already constructs two literal layer
boundaries and the deletion component between them.  This file exposes that
source object as a two-sided open tangle and composes two such objects through
their common two-position source order.

The composite is the categorical serial join of two tagged open pieces.  A
later formation theorem must still identify an appropriate chain of these
pieces with the corresponding region of the ambient annulus; no such global
geometric identification is asserted here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24OpenTangleComposition
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24SpliceUnification
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorLocalSerialOpenTangleEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceConsecutiveSlabInterface

variable {source : SourceTrail G}
  {embedded : source.AnnularEmbedding} {blockLength : Nat}
  {realization : BoundaryCleanCorridorRealization embedded blockLength}
  {htwoSided : OrbitFacesTwoSided
    embedded.cellulation.rotation.toRotationSystem}
  {hunique : PairwiseUniqueSharedInteriorEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
  {leftInterior rightInterior : CorridorInterior blockLength}
  {hleftNext : leftInterior.center.val + 2 < blockLength}
  {hrightNext : rightInterior.center.val + 2 < blockLength}

/-- A literal source Cell-3 layer tile, retaining its two ordered boundary
interfaces as unpaired input and output half-edges. -/
noncomputable def localLayerPairTwoSidedOpenTangle
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hleftNext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic) :=
  (interface.localLayerPairOrderedCutSidesData hcubic).toTwoSidedOpenTangle

/-- The source proves that every local layer has exactly two transversal
positions.  Normalize the ordered-cut package to that common finite carrier
before serial composition. -/
noncomputable def localLayerPairOrderedCutSidesDataTwo
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hleftNext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic) :
    OrderedCutSidesData embedded.cellulation.rotation.toRotationSystem
      2 0
      (interface.separatedLocalLayerPair.sourceCrosscutFaceFragmentCount
        embedded.cellulation.rotation
        (interface.localLayerPairSourceCrosscutBoundaryData hcubic)) := by
  simpa only [interface.localLayer_walk_length_eq_two] using
    interface.localLayerPairOrderedCutSidesData hcubic

/-- Serially join two actual source Cell-3 tiles by their common ordered pair
of transversal positions.  The two retained vertex carriers remain tagged,
so this operation records composition without identifying either piece with
an ambient global region. -/
noncomputable def serialComposeLocalLayerPairs
    (leftInterface : SourceConsecutiveSlabInterface realization htwoSided
      hunique leftInterior hleftNext)
    (rightInterface : SourceConsecutiveSlabInterface realization htwoSided
      hunique rightInterior hrightNext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic) :=
  (leftInterface.localLayerPairOrderedCutSidesDataTwo hcubic).serialCompose
    (rightInterface.localLayerPairOrderedCutSidesDataTwo hcubic)

end SourceConsecutiveSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
