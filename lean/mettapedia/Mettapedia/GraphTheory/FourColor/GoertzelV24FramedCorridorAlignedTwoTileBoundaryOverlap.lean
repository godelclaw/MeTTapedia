import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTileSuccessorDualInterface

/-!
# Consecutive aligned two-tile boundaries overlap

The locally constructed six-edge boundaries at consecutive source offsets
share their intervening dual interface.  They are therefore useful local
windows, but they are not themselves the two separated radial cuts of the
source's cut-open collar decomposition.  This is a fact about the displayed
facial-dual cycles only; it makes no claim about the primal deletion sides.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorAlignedTwoTileBoundaryOverlapEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Consecutive literal aligned two-tile boundary cycles share the centre of
their common source interface.  Consequently these local cycles cannot be
used directly as the separated crosscuts that cut open one physical corridor
into serial slabs. -/
theorem sourceTwoTileAlignedBoundaryWalks_consecutive_not_disjoint
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
    (offset : Fin (blockLength - 5)) :
    ¬ (sourceTwoTileAlignedBoundaryWalkAt realization hcubic hrotation
          htwoSided hunique (sourceTwoTileSuccessorStartOffset offset)).support.Disjoint
        (sourceTwoTileAlignedBoundaryWalkAt realization hcubic hrotation
          htwoSided hunique (sourceTwoTileSuccessorNextOffset offset)).support := by
  let firstOffset := sourceTwoTileSuccessorStartOffset offset
  let secondOffset := sourceTwoTileSuccessorNextOffset offset
  let first := sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
    hunique firstOffset
  let shared := sourceTwoTileSecondInterfaceAt realization hcubic hrotation htwoSided
    hunique firstOffset
  let second := sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
    hunique secondOffset
  have hinterface : shared.toInterface = second.toInterface := by
    simpa [firstOffset, secondOffset, shared, second] using
      sourceTwoTileSecondInterfaceAt_toInterface_eq_successorFirst realization hcubic
        hrotation htwoSided hunique offset
  have hcentre : shared.toInterface.centerLayerFace = second.toInterface.centerLayerFace :=
    congrArg SourceConsecutiveSlabInterface.centerLayerFace hinterface
  have hleft : shared.toInterface.centerLayerFace ∈
      (sourceTwoTileAlignedBoundaryWalkAt realization hcubic hrotation htwoSided
        hunique firstOffset).support := by
    simp only [sourceTwoTileAlignedBoundaryWalkAt,
      SimpleGraph.Walk.mem_support_append_iff]
    left
    right
    change shared.toInterface.centerLayerFace ∈ shared.toInterface.localLayerWalk.reverse.support
    rw [SimpleGraph.Walk.support_reverse]
    simp [SourceConsecutiveSlabInterface.localLayerWalk]
  have hright : second.toInterface.centerLayerFace ∈
      (sourceTwoTileAlignedBoundaryWalkAt realization hcubic hrotation htwoSided
        hunique secondOffset).support := by
    simp only [sourceTwoTileAlignedBoundaryWalkAt,
      SimpleGraph.Walk.mem_support_append_iff]
    left
    left
    left
    change second.toInterface.centerLayerFace ∈ second.toInterface.localLayerWalk.support
    simp [SourceConsecutiveSlabInterface.localLayerWalk]
  intro hdisjoint
  exact (List.disjoint_left.mp hdisjoint) hleft (hcentre.symm ▸ hright)

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
