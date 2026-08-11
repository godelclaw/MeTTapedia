import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorLocalSourceSplice
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedCutSerialOpenTangle

/-!
# Retained-side tangles at source corridor layer cuts

Each consecutive Cell-3 slab interface already constructs two literal layer
boundaries and selects the outer deletion component.  This file exposes that
*retained* side as a two-sided open tangle in its common two-position source
order.

This is not the small Cell-3 generator used by the source's `Count` functor.
That generator is the complementary removed region between the layers.
Consequently this module provides no source-level serial composition of two
retained sides: doing so would duplicate the ambient exterior rather than
assemble adjacent cells.
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

/-- The outer retained side of a literal source Cell-3 layer cut, with its two
ordered boundary interfaces left unpaired.  This is a splice-side object, not
the local corridor generator. -/
noncomputable def localLayerPairRetainedTwoSidedOpenTangle
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

end SourceConsecutiveSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
