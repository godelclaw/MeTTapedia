import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutLiteralCountComposition
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorLocalSourceSplice

/-!
# Literal `Count` semantics for one realized source corridor tile

This adapter specializes the source-crosscut `Count` composition law to a
real two-layer tile of a boundary-clean hex corridor.  Thus the finite open
coloring fibers are attached to the manuscript's actual layer boundaries,
not merely to an abstract paired-crosscut input.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24AnnularCrosscut
open GoertzelV24CleanHexCorridor
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexCorridorSkeleton
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24SpliceUnification
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorLocalCountGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
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
  {leftInterior : CorridorInterior blockLength}
  {hnext : leftInterior.center.val + 2 < blockLength}

/-- On a concrete two-layer source corridor tile, the original map is
Tait-colorable exactly when the literal retained and complementary tangles
have positive finite `Count` fibers at the same ordered pair of layer words. -/
theorem localLayerPair_taitColorable_iff_exists_positiveBoundaryColorCounts
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic) :
    TaitColorable (RS := embedded.cellulation.rotation.toRotationSystem) ↔
      ∃ left : Fin interface.separatedLocalLayerPair.left.walk.length → Color,
        ∃ right : Fin interface.separatedLocalLayerPair.right.walk.length → Color,
          0 < interface.separatedLocalLayerPair.sourceCrosscutLiteralOpenBoundaryColorCount
              embedded.cellulation.rotation
              (interface.localLayerPairSourceCrosscutBoundaryData hcubic) left right ∧
          0 < interface.separatedLocalLayerPair.sourceCrosscutComplementBoundaryColorCount
              embedded.cellulation.rotation
              (interface.localLayerPairSourceCrosscutBoundaryData hcubic) hcubic left right := by
  exact interface.separatedLocalLayerPair.taitColorable_iff_exists_positive_sourceCrosscutBoundaryColorCounts
      embedded.cellulation.rotation
      (interface.localLayerPairSourceCrosscutBoundaryData hcubic) hcubic

end SourceConsecutiveSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
