import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseStableTrackedTransitionRegion

/-!
# Ordered factorization of one stable tracked source transition

One outgoing-prefix state advances through two distinct literal source
operations: a boundary rebase exposes the successor input, and the successor
Cell then produces the next outgoing prefix.  This file expands that temporal
order into the five graph factors already proved for those operations.

The theorem is deliberately an equality of ambient tracked graphs.  It does
not yet contract either residual seam onto the stable twelve-slot transition
carrier or assert an executable recurrence.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseStableTrackedTransitionFactorizationEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The successor stable graph is obtained in the source's literal order:
current prefix, boundary-rebase region, rebase seam, successor Cell, and
Cell-input seam. -/
theorem sourceCorridorSerialPrefixTrackedGraph_next_eq_stableTransition_five_factor
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
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color) (first second : Color) :
    regionalTrackedEdgeGraph embedded.cellulation.rotation.toRotationSystem
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
          ).regionEdges color first second =
      ((((regionalTrackedEdgeGraph
              embedded.cellulation.rotation.toRotationSystem
              (sourceCorridorSerialPrefixCutDataAt realization hcubic
                hrotation htwoSided hunique offset).regionEdges color first
                second ⊔
            regionalTrackedEdgeGraph
              embedded.cellulation.rotation.toRotationSystem
              (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
                hrotation htwoSided hunique offset hnext) color first second) ⊔
          sourceCorridorSerialBoundaryRebaseTrackedSeamAt realization hcubic
            hrotation htwoSided hunique offset hnext color first second) ⊔
        regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          (sourceSlabLiteralCellRegionAt realization hcubic hrotation
            htwoSided hunique (sourceCorridorSerialNextOffset offset hnext))
          color first second) ⊔
        sourceCorridorSerialInputTrackedSeamGraphAt realization hcubic
          hrotation htwoSided hunique
          (sourceCorridorSerialNextOffset offset hnext) color first second) := by
  change regionalTrackedEdgeGraph
      embedded.cellulation.rotation.toRotationSystem
      (sourceCorridorSerialPrefixRegion realization hcubic hrotation htwoSided
        hunique ((sourceCorridorSerialNextOffset offset hnext).val + 1))
      color first second = _
  rw [sourceCorridorSerialPrefixTrackedGraph_eq_input_three_factor realization
    hcubic hrotation htwoSided hunique
    (sourceCorridorSerialNextOffset offset hnext) color first second]
  rw [sourceCorridorSerialInputTrackedGraph_next_eq_rebase_three_factor
    realization hcubic hrotation htwoSided hunique offset hnext color first
    second]

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
