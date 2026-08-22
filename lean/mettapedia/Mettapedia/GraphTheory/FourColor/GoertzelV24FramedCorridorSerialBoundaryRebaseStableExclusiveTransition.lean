import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseStableTrackedTransitionRegion
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileExclusiveRegionFactorization

/-!
# Exclusive factorization of one stable literal source transition

The local rebase-plus-successor-Cell region can overlap the accumulated
prefix.  This module assigns every such overlap to the prefix and retains only
the set difference as the genuinely new local region.  The corresponding
residual seam is recomputed rather than reused from the overlapping
factorization.

The result is exact for both tracked connectivity and occurrence-sensitive
facial progress.  Moreover, every old endpoint of the recomputed seam lies on
the true vertex-side frontier of the accumulated prefix.  This is the source
specialization needed before historical frontier positions can be contracted
to the fixed transition state; it does not yet perform that final locality
classification or compute a reachable closure.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TerminalProfileExclusiveRegionFactorization
open GoertzelV24TerminalProfileFaceUpdate
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseStableExclusiveTransitionEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The part of one rebase-plus-successor-Cell region not already owned by
the accumulated prefix. -/
noncomputable def sourceCorridorSerialBoundaryRebaseStableExclusiveTransitionRegionAt
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
  sourceCorridorSerialBoundaryRebaseStableTransitionRegionAt realization
      hcubic hrotation htwoSided hunique offset hnext \
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges

/-- The recomputed tracked seam after assigning all transition overlap to the
old prefix. -/
def sourceCorridorSerialBoundaryRebaseStableExclusiveTrackedSeamAt
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
  regionalTrackedExclusiveSeamGraph
    embedded.cellulation.rotation.toRotationSystem
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
    (sourceCorridorSerialBoundaryRebaseStableTransitionRegionAt realization
      hcubic hrotation htwoSided hunique offset hnext)
    color first second

/-- The successor prefix tracked graph is exactly old prefix, genuinely new
local region, and the recomputed exclusive seam. -/
theorem sourceCorridorSerialPrefixTrackedGraph_next_eq_stableExclusiveTransition_three_factor
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
        regionalTrackedEdgeGraph embedded.cellulation.rotation.toRotationSystem
          (sourceCorridorSerialBoundaryRebaseStableExclusiveTransitionRegionAt
            realization hcubic hrotation htwoSided hunique offset hnext)
          color first second) ⊔
        sourceCorridorSerialBoundaryRebaseStableExclusiveTrackedSeamAt
          realization hcubic hrotation htwoSided hunique offset hnext color
            first second := by
  rw [sourceCorridorSerialPrefixCutDataAt_next_regionEdges_eq_current_union_stableTransition
    realization hcubic hrotation htwoSided hunique offset hnext]
  exact regionalTrackedEdgeGraph_union_eq_sup_sup_exclusiveSeam
    embedded.cellulation.rotation.toRotationSystem
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
    (sourceCorridorSerialBoundaryRebaseStableTransitionRegionAt realization
      hcubic hrotation htwoSided hunique offset hnext)
    color first second

/-- Every old endpoint of the recomputed tracked seam lies on the actual
frontier of the accumulated source prefix. -/
theorem sourceCorridorSerialBoundaryRebaseStableExclusiveTrackedSeamAt_adj_oldEndpoint_mem_truePrefixCrossing
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
    (color : G.edgeSet → Color) (first second : Color) {x y : G.edgeSet}
    (hadj : (sourceCorridorSerialBoundaryRebaseStableExclusiveTrackedSeamAt
      realization hcubic hrotation htwoSided hunique offset hnext color first
        second).Adj x y) :
    (x ∈ (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset).regionEdges ∧
        x ∈ sourceCorridorSerialPrefixTrueCrossingEdges realization hcubic
          hrotation htwoSided hunique (offset.val + 1) ∧
        y ∈ sourceCorridorSerialBoundaryRebaseStableTransitionRegionAt
          realization hcubic hrotation htwoSided hunique offset hnext ∧
        y ∉ (sourceCorridorSerialPrefixCutDataAt realization hcubic
          hrotation htwoSided hunique offset).regionEdges) ∨
      (y ∈ (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset).regionEdges ∧
        y ∈ sourceCorridorSerialPrefixTrueCrossingEdges realization hcubic
          hrotation htwoSided hunique (offset.val + 1) ∧
        x ∈ sourceCorridorSerialBoundaryRebaseStableTransitionRegionAt
          realization hcubic hrotation htwoSided hunique offset hnext ∧
        x ∉ (sourceCorridorSerialPrefixCutDataAt realization hcubic
          hrotation htwoSided hunique offset).regionEdges) := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let oldRegion :=
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
  let side := sourceCorridorSerialPrefixVertexSide realization hcubic
    hrotation htwoSided hunique (offset.val + 1)
  have holdRegion : oldRegion = vertexSetRegionEdges RS side := by
    change sourceCorridorSerialPrefixRegion realization hcubic hrotation
        htwoSided hunique (offset.val + 1) =
      vertexSetRegionEdges RS side
    exact sourceCorridorSerialPrefixRegion_eq_vertexSetRegionEdges realization
      hcubic hrotation htwoSided hunique (offset.val + 1)
  have hlocalized :=
    regionalTrackedExclusiveSeamGraph_adj_localizes_to_oldVertexCut RS side
      (sourceCorridorSerialBoundaryRebaseStableTransitionRegionAt realization
        hcubic hrotation htwoSided hunique offset hnext)
      color first second (by simpa [sourceCorridorSerialBoundaryRebaseStableExclusiveTrackedSeamAt,
        oldRegion, holdRegion] using hadj)
  simpa [oldRegion, holdRegion, side,
    sourceCorridorSerialPrefixTrueCrossingEdges, RS] using hlocalized

/-- The occurrence-sensitive facial exclusive seam. -/
def sourceCorridorSerialBoundaryRebaseStableExclusiveFaceSeamAt
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
    (root : embedded.cellulation.rotation.toRotationSystem.D) :
    SimpleGraph
      (Fin (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card) :=
  faceRegionalExclusiveSeamGraph
    embedded.cellulation.rotation.toRotationSystem root
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
    (sourceCorridorSerialBoundaryRebaseStableTransitionRegionAt realization
      hcubic hrotation htwoSided hunique offset hnext)

/-- The successor facial position graph has the same exact exclusive
three-factor presentation. -/
theorem sourceCorridorSerialPrefixFaceGraph_next_eq_stableExclusiveTransition_three_factor
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
    (root : embedded.cellulation.rotation.toRotationSystem.D) :
    faceRegionalAmbientPositionGraph embedded.cellulation.rotation.toRotationSystem
        root
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
          ).regionEdges =
      (faceRegionalAmbientPositionGraph
          embedded.cellulation.rotation.toRotationSystem root
          (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
            htwoSided hunique offset).regionEdges ⊔
        faceRegionalAmbientPositionGraph
          embedded.cellulation.rotation.toRotationSystem root
          (sourceCorridorSerialBoundaryRebaseStableExclusiveTransitionRegionAt
            realization hcubic hrotation htwoSided hunique offset hnext)) ⊔
        sourceCorridorSerialBoundaryRebaseStableExclusiveFaceSeamAt
          realization hcubic hrotation htwoSided hunique offset hnext root := by
  rw [sourceCorridorSerialPrefixCutDataAt_next_regionEdges_eq_current_union_stableTransition
    realization hcubic hrotation htwoSided hunique offset hnext]
  exact faceRegionalAmbientPositionGraph_union_eq_sup_sup_exclusiveSeam
    embedded.cellulation.rotation.toRotationSystem root
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
    (sourceCorridorSerialBoundaryRebaseStableTransitionRegionAt realization
      hcubic hrotation htwoSided hunique offset hnext)

/-- Facial seam occurrences project to the same true old-prefix frontier. -/
theorem sourceCorridorSerialBoundaryRebaseStableExclusiveFaceSeamAt_adj_oldEndpoint_mem_truePrefixCrossing
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
    (root : embedded.cellulation.rotation.toRotationSystem.D)
    {x y : Fin
      (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card}
    (hadj : (sourceCorridorSerialBoundaryRebaseStableExclusiveFaceSeamAt
      realization hcubic hrotation htwoSided hunique offset hnext root).Adj x y) :
    (faceCycleEdge embedded.cellulation.rotation.toRotationSystem root x ∈
          (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
            htwoSided hunique offset).regionEdges ∧
        faceCycleEdge embedded.cellulation.rotation.toRotationSystem root x ∈
          sourceCorridorSerialPrefixTrueCrossingEdges realization hcubic
            hrotation htwoSided hunique (offset.val + 1) ∧
        faceCycleEdge embedded.cellulation.rotation.toRotationSystem root y ∈
          sourceCorridorSerialBoundaryRebaseStableTransitionRegionAt
            realization hcubic hrotation htwoSided hunique offset hnext ∧
        faceCycleEdge embedded.cellulation.rotation.toRotationSystem root y ∉
          (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
            htwoSided hunique offset).regionEdges) ∨
      (faceCycleEdge embedded.cellulation.rotation.toRotationSystem root y ∈
          (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
            htwoSided hunique offset).regionEdges ∧
        faceCycleEdge embedded.cellulation.rotation.toRotationSystem root y ∈
          sourceCorridorSerialPrefixTrueCrossingEdges realization hcubic
            hrotation htwoSided hunique (offset.val + 1) ∧
        faceCycleEdge embedded.cellulation.rotation.toRotationSystem root x ∈
          sourceCorridorSerialBoundaryRebaseStableTransitionRegionAt
            realization hcubic hrotation htwoSided hunique offset hnext ∧
        faceCycleEdge embedded.cellulation.rotation.toRotationSystem root x ∉
          (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
            htwoSided hunique offset).regionEdges) := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let oldRegion :=
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
  let side := sourceCorridorSerialPrefixVertexSide realization hcubic
    hrotation htwoSided hunique (offset.val + 1)
  have holdRegion : oldRegion = vertexSetRegionEdges RS side := by
    change sourceCorridorSerialPrefixRegion realization hcubic hrotation
        htwoSided hunique (offset.val + 1) =
      vertexSetRegionEdges RS side
    exact sourceCorridorSerialPrefixRegion_eq_vertexSetRegionEdges realization
      hcubic hrotation htwoSided hunique (offset.val + 1)
  have hlocalized :=
    faceRegionalExclusiveSeamGraph_adj_localizes_to_oldVertexCut RS hcubic
      hrotation root side
      (sourceCorridorSerialBoundaryRebaseStableTransitionRegionAt realization
        hcubic hrotation htwoSided hunique offset hnext)
      (by simpa [sourceCorridorSerialBoundaryRebaseStableExclusiveFaceSeamAt,
        oldRegion, holdRegion] using hadj)
  simpa [oldRegion, holdRegion, side,
    sourceCorridorSerialPrefixTrueCrossingEdges, RS] using hlocalized

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
