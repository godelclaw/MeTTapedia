import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSourceProfileWord
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSourceRailPair
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorLocalLayerPair

/-!
# Consecutive source-Cell loops overlap

The source-indexed `localLayerLoop` at one position uses the two consecutive
corridor centres at that position.  Hence the loops at consecutive positions
share the intervening centre face.  This is a fact about the older local-Cell
windows; it does not assert that the physical aligned slabs used for the
literal open-tangle construction overlap.

In particular, the tagged serial composite of those local Cells must not be
identified with an ambient serial gluing merely from its abstract composition
law.  The physical-gluing route has to use its own carrier and boundary
decomposition theorem.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CleanHexCorridor
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorConsecutiveCellLoopOverlapEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Consecutive source-indexed local-Cell loops share their intervening
corridor centre.  Thus the older local-Cell windows cannot themselves serve
as a proof that the abstract tagged serial composite is a physical ambient
gluing. -/
theorem sourceSlabRailAdjacent_localLayerLoops_not_disjoint
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4)) :
    ¬ (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
          (sourceSlabRailStartOffset offset)).localLayerLoop.support.Disjoint
        (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
          (sourceSlabRailFinishOffset offset)).localLayerLoop.support := by
  let first := sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
    (sourceSlabRailStartOffset offset)
  let second := sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
    (sourceSlabRailFinishOffset offset)
  have hcentre : first.nextCenterLayerFace = second.centerLayerFace := by
    change
      realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior
            (sourceSlabLeftInterior (sourceSlabRailStartOffset offset))
            (sourceSlabLeftInterior_hasNext (sourceSlabRailStartOffset offset))).center =
        realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (sourceSlabLeftInterior (sourceSlabRailFinishOffset offset)).center
    rw [sourceSlabLeftInterior_railFinish_eq_next offset]
  have hfirst : first.nextCenterLayerFace ∈ first.localLayerLoop.support := by
    rw [SourceConsecutiveSlabInterface.localLayerLoop,
      SimpleGraph.Walk.mem_support_append_iff]
    right
    change first.nextCenterLayerFace ∈ first.nextLocalLayerWalk.reverse.support
    rw [SimpleGraph.Walk.support_reverse]
    simp [SourceConsecutiveSlabInterface.nextLocalLayerWalk]
  have hsecond : second.centerLayerFace ∈ second.localLayerLoop.support := by
    rw [SourceConsecutiveSlabInterface.localLayerLoop,
      SimpleGraph.Walk.mem_support_append_iff]
    left
    change second.centerLayerFace ∈ second.localLayerWalk.support
    simp [SourceConsecutiveSlabInterface.localLayerWalk]
  intro hdisjoint
  exact (List.disjoint_left.mp hdisjoint) hfirst (hcentre.symm ▸ hsecond)

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
