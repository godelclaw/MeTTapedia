import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseStableTrackedTransitionSlots
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialOneStepRegion

/-!
# The exact local region of a stable tracked-state transition

A stable rebase state is measured after one literal source Cell, on its
outgoing prefix.  Advancing to the next stable state therefore adds, in order,
the current boundary-rebase edges and the successor literal Cell.  This is a
different cut convention from the input-to-input one-step region, which adds
the current Cell and then its rebase.

This file proves the exact prefix-to-prefix region equation and the resulting
tracked graph factorization.  The successor graph is the current graph, the
finite local transition region, and their residual attachment seam.  No
finite contraction of that seam or executable recurrence is asserted here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24TerminalProfileSeamResidual
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseStableTrackedTransitionRegionEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The literal local region added from one stable outgoing-prefix state to
the next: first the current rebase edges, then the successor Cell. -/
noncomputable def sourceCorridorSerialBoundaryRebaseStableTransitionRegionAt
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
    (hnext : offset.val + 1 < blockLength - 3) : Finset G.edgeSet :=
  sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
      htwoSided hunique offset hnext ∪
    sourceSlabLiteralCellRegionAt realization hcubic hrotation htwoSided
      hunique (sourceCorridorSerialNextOffset offset hnext)

/-- Consecutive stable prefix regions differ by exactly the local
rebase-plus-successor-Cell region. -/
theorem sourceCorridorSerialPrefixCutDataAt_next_regionEdges_eq_current_union_stableTransition
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
    (hnext : offset.val + 1 < blockLength - 3) :
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
        ).regionEdges =
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset).regionEdges ∪
        sourceCorridorSerialBoundaryRebaseStableTransitionRegionAt realization
          hcubic hrotation htwoSided hunique offset hnext := by
  rw [sourceCorridorSerialPrefixCutDataAt_regionEdges_eq_input_union_cell,
    sourceCorridorSerialCutRegionAt_next_eq_prefixCut_union_rebase]
  simp only [sourceCorridorSerialBoundaryRebaseStableTransitionRegionAt,
    Finset.union_assoc]

/-- The tracked graph contributed by the local stable transition. -/
def sourceCorridorSerialBoundaryRebaseStableTransitionTrackedGraphAt
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
    SimpleGraph G.edgeSet :=
  regionalTrackedEdgeGraph embedded.cellulation.rotation.toRotationSystem
    (sourceCorridorSerialBoundaryRebaseStableTransitionRegionAt realization
      hcubic hrotation htwoSided hunique offset hnext)
    color first second

/-- The residual tracked seam attaching the local stable transition to the
current accumulated prefix. -/
def sourceCorridorSerialBoundaryRebaseStableTransitionTrackedSeamAt
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
    SimpleGraph G.edgeSet :=
  regionalTrackedSeamGraph embedded.cellulation.rotation.toRotationSystem
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
    (sourceCorridorSerialBoundaryRebaseStableTransitionRegionAt realization
      hcubic hrotation htwoSided hunique offset hnext)
    color first second

/-- The successor stable tracked graph is exactly the current stable graph,
the local rebase-plus-Cell graph, and their residual seam. -/
theorem sourceCorridorSerialPrefixTrackedGraph_next_eq_stableTransition_three_factor
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
      (regionalTrackedEdgeGraph embedded.cellulation.rotation.toRotationSystem
          (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
            htwoSided hunique offset).regionEdges color first second ⊔
        sourceCorridorSerialBoundaryRebaseStableTransitionTrackedGraphAt
          realization hcubic hrotation htwoSided hunique offset hnext color
            first second) ⊔
        sourceCorridorSerialBoundaryRebaseStableTransitionTrackedSeamAt
          realization hcubic hrotation htwoSided hunique offset hnext color
            first second := by
  rw [sourceCorridorSerialPrefixCutDataAt_next_regionEdges_eq_current_union_stableTransition
    realization hcubic hrotation htwoSided hunique offset hnext]
  exact regionalTrackedEdgeGraph_union_eq_sup_sup_seam
    embedded.cellulation.rotation.toRotationSystem
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
    (sourceCorridorSerialBoundaryRebaseStableTransitionRegionAt realization
      hcubic hrotation htwoSided hunique offset hnext)
    color first second

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
