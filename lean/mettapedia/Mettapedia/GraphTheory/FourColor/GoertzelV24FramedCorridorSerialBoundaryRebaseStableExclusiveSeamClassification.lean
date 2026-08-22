import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseStableExclusiveTransition
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixSeamSupport

/-!
# Classifying the overlap-corrected stable-transition seam

After transition overlap is assigned to the accumulated prefix, a residual
turn has only three possible sources.  Its genuinely new endpoint is either
one of the two rebase edges, it is an ordinary successor-Cell seam turn and
therefore touches a named outgoing crossing, or its old endpoint also belongs
to the successor Cell region.  The last case is the exact overlap-created
residue that cannot be inherited from the earlier staged seam by monotonicity.

This file proves that trichotomy for tracked connectivity and for literal
face-cycle occurrences.  It deliberately does not discard or assume away the
Cell-overlap branch; eliminating or finitely coding that branch is the next
geometric obligation before the stable reachable-state recurrence closes.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationFaceFragments
open GoertzelV24TerminalProfileExclusiveRegionFactorization
open GoertzelV24TerminalProfileSeamResidual
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseStableExclusiveSeamClassificationEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The genuinely new case left after a tracked exclusive-seam turn enters
the successor Cell through an old-prefix edge that already belongs to that
same Cell region. -/
def SourceCorridorSerialStableExclusiveTrackedCellOverlapTurnAt
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
    (color : G.edgeSet → Color) (first second : Color)
    (oldEdge newEdge : G.edgeSet) : Prop :=
  (embedded.cellulation.rotation.toRotationSystem.trackedEdgeGraph
      color first second).Adj oldEdge newEdge ∧
    oldEdge ∈ (sourceCorridorSerialPrefixCutDataAt realization hcubic
      hrotation htwoSided hunique offset).regionEdges ∧
    oldEdge ∈ sourceCorridorSerialPrefixTrueCrossingEdges realization hcubic
      hrotation htwoSided hunique (offset.val + 1) ∧
    oldEdge ∈ sourceSlabLiteralCellRegionAt realization hcubic hrotation
      htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) ∧
    newEdge ∈ sourceSlabLiteralCellRegionAt realization hcubic hrotation
      htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) ∧
    newEdge ∉ (sourceCorridorSerialPrefixCutDataAt realization hcubic
      hrotation htwoSided hunique offset).regionEdges ∧
    newEdge ∉ sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
      hrotation htwoSided hunique offset hnext

/-- Every tracked turn of the overlap-corrected stable transition is either
supported at a rebase edge, supported at a named successor-Cell output, or is
one explicitly oriented Cell-overlap turn. -/
theorem sourceCorridorSerialBoundaryRebaseStableExclusiveTrackedSeamAt_adj_classify
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
    (x ∈ sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
        hrotation htwoSided hunique offset hnext ∨
      y ∈ sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
        hrotation htwoSided hunique offset hnext) ∨
    (∃ step : Fin 2,
      x = (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
          hunique (sourceCorridorSerialNextOffset offset hnext)
          ).nextLocalLayerPrefixCrossing step ∨
        y = (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
          hunique (sourceCorridorSerialNextOffset offset hnext)
          ).nextLocalLayerPrefixCrossing step) ∨
    SourceCorridorSerialStableExclusiveTrackedCellOverlapTurnAt realization
        hcubic hrotation htwoSided hunique offset hnext color first second x y ∨
      SourceCorridorSerialStableExclusiveTrackedCellOverlapTurnAt realization
        hcubic hrotation htwoSided hunique offset hnext color first second y x := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let oldRegion :=
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
  let rebase := sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
    hrotation htwoSided hunique offset hnext
  let nextOffset := sourceCorridorSerialNextOffset offset hnext
  let cell := sourceSlabLiteralCellRegionAt realization hcubic hrotation
    htwoSided hunique nextOffset
  let transition := sourceCorridorSerialBoundaryRebaseStableTransitionRegionAt
    realization hcubic hrotation htwoSided hunique offset hnext
  let nextInput := sourceCorridorSerialCutRegionAt realization hcubic hrotation
    htwoSided hunique nextOffset
  have hraw := (regionalTrackedSeamGraph_adj_iff RS oldRegion
    (transition \ oldRegion) color first second x y).1 (by
      simpa [sourceCorridorSerialBoundaryRebaseStableExclusiveTrackedSeamAt,
        regionalTrackedExclusiveSeamGraph, RS, oldRegion, transition] using hadj)
  have hlocalized :=
    sourceCorridorSerialBoundaryRebaseStableExclusiveTrackedSeamAt_adj_oldEndpoint_mem_truePrefixCrossing
      realization hcubic hrotation htwoSided hunique offset hnext color first
        second hadj
  have hnextInput : nextInput = oldRegion ∪ rebase := by
    simpa [nextInput, oldRegion, rebase, nextOffset] using
      sourceCorridorSerialCutRegionAt_next_eq_prefixCut_union_rebase
        realization hcubic hrotation htwoSided hunique offset hnext
  have htransition : transition = rebase ∪ cell := by
    rfl
  rcases hlocalized with hforward | hbackward
  · rcases hforward with ⟨hxOld, hxBoundary, hyTransition, hyNotOld⟩
    by_cases hyRebase : y ∈ rebase
    · exact Or.inl (Or.inr hyRebase)
    · have hyCell : y ∈ cell := by
        change y ∈ transition at hyTransition
        rw [htransition] at hyTransition
        exact (Finset.mem_union.1 hyTransition).resolve_left hyRebase
      by_cases hxCell : x ∈ cell
      · exact Or.inr (Or.inr (Or.inl ⟨hraw.1, hxOld, hxBoundary,
          hxCell, hyCell, hyNotOld, hyRebase⟩))
      · have hxNextInput : x ∈ nextInput := by
          rw [hnextInput]
          exact Finset.mem_union_left _ hxOld
        have hyNotNextInput : y ∉ nextInput := by
          rw [hnextInput]
          simpa only [Finset.mem_union, not_or] using ⟨hyNotOld, hyRebase⟩
        have hcellSeam :
            (sourceCorridorSerialInputTrackedSeamGraphAt realization hcubic
              hrotation htwoSided hunique nextOffset color first second).Adj
                x y := by
          apply (regionalTrackedSeamGraph_adj_iff RS nextInput cell color first
            second x y).2
          exact ⟨hraw.1, Or.inl
            ⟨hxNextInput, hxCell, hyCell, hyNotNextInput⟩⟩
        exact Or.inr (Or.inl
          (sourceCorridorSerialInputTrackedSeamGraphAt_adj_touches_outputCrossing
            realization hcubic hrotation htwoSided hunique nextOffset color
              first second hcellSeam))
  · rcases hbackward with ⟨hyOld, hyBoundary, hxTransition, hxNotOld⟩
    by_cases hxRebase : x ∈ rebase
    · exact Or.inl (Or.inl hxRebase)
    · have hxCell : x ∈ cell := by
        change x ∈ transition at hxTransition
        rw [htransition] at hxTransition
        exact (Finset.mem_union.1 hxTransition).resolve_left hxRebase
      by_cases hyCell : y ∈ cell
      · exact Or.inr (Or.inr (Or.inr ⟨hraw.1.symm, hyOld, hyBoundary,
          hyCell, hxCell, hxNotOld, hxRebase⟩))
      · have hyNextInput : y ∈ nextInput := by
          rw [hnextInput]
          exact Finset.mem_union_left _ hyOld
        have hxNotNextInput : x ∉ nextInput := by
          rw [hnextInput]
          simpa only [Finset.mem_union, not_or] using ⟨hxNotOld, hxRebase⟩
        have hcellSeam :
            (sourceCorridorSerialInputTrackedSeamGraphAt realization hcubic
              hrotation htwoSided hunique nextOffset color first second).Adj
                x y := by
          apply (regionalTrackedSeamGraph_adj_iff RS nextInput cell color first
            second x y).2
          exact ⟨hraw.1, Or.inr
            ⟨hxCell, hxNotNextInput, hyNextInput, hyCell⟩⟩
        exact Or.inr (Or.inl
          (sourceCorridorSerialInputTrackedSeamGraphAt_adj_touches_outputCrossing
            realization hcubic hrotation htwoSided hunique nextOffset color
              first second hcellSeam))

/-- The occurrence-sensitive version of the Cell-overlap residue.  Positions
are retained so repeated visits to one ambient edge are not collapsed. -/
def SourceCorridorSerialStableExclusiveFaceCellOverlapTurnAt
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
    (oldPosition newPosition : Fin
      (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card) : Prop :=
  (faceCyclePositionGraph embedded.cellulation.rotation.toRotationSystem
      root).Adj oldPosition newPosition ∧
    faceCycleEdge embedded.cellulation.rotation.toRotationSystem root
        oldPosition ∈
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges ∧
    faceCycleEdge embedded.cellulation.rotation.toRotationSystem root
        oldPosition ∈
      sourceCorridorSerialPrefixTrueCrossingEdges realization hcubic hrotation
        htwoSided hunique (offset.val + 1) ∧
    faceCycleEdge embedded.cellulation.rotation.toRotationSystem root
        oldPosition ∈
      sourceSlabLiteralCellRegionAt realization hcubic hrotation htwoSided
        hunique (sourceCorridorSerialNextOffset offset hnext) ∧
    faceCycleEdge embedded.cellulation.rotation.toRotationSystem root
        newPosition ∈
      sourceSlabLiteralCellRegionAt realization hcubic hrotation htwoSided
        hunique (sourceCorridorSerialNextOffset offset hnext) ∧
    faceCycleEdge embedded.cellulation.rotation.toRotationSystem root
        newPosition ∉
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges ∧
    faceCycleEdge embedded.cellulation.rotation.toRotationSystem root
        newPosition ∉
      sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
        htwoSided hunique offset hnext

/-- Every occurrence-sensitive exclusive seam turn has the same three-way
classification after projecting its two positions to ambient edges. -/
theorem sourceCorridorSerialBoundaryRebaseStableExclusiveFaceSeamAt_adj_classify
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
          sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
            hrotation htwoSided hunique offset hnext ∨
      faceCycleEdge embedded.cellulation.rotation.toRotationSystem root y ∈
          sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
            hrotation htwoSided hunique offset hnext) ∨
    (∃ step : Fin 2,
      faceCycleEdge embedded.cellulation.rotation.toRotationSystem root x =
          (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
            hunique (sourceCorridorSerialNextOffset offset hnext)
            ).nextLocalLayerPrefixCrossing step ∨
        faceCycleEdge embedded.cellulation.rotation.toRotationSystem root y =
          (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
            hunique (sourceCorridorSerialNextOffset offset hnext)
            ).nextLocalLayerPrefixCrossing step) ∨
    SourceCorridorSerialStableExclusiveFaceCellOverlapTurnAt realization
        hcubic hrotation htwoSided hunique offset hnext root x y ∨
      SourceCorridorSerialStableExclusiveFaceCellOverlapTurnAt realization
        hcubic hrotation htwoSided hunique offset hnext root y x := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let oldRegion :=
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
  let rebase := sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
    hrotation htwoSided hunique offset hnext
  let nextOffset := sourceCorridorSerialNextOffset offset hnext
  let cell := sourceSlabLiteralCellRegionAt realization hcubic hrotation
    htwoSided hunique nextOffset
  let transition := sourceCorridorSerialBoundaryRebaseStableTransitionRegionAt
    realization hcubic hrotation htwoSided hunique offset hnext
  let nextInput := sourceCorridorSerialCutRegionAt realization hcubic hrotation
    htwoSided hunique nextOffset
  have hraw := (faceRegionalSeamGraph_adj_iff RS root oldRegion
    (transition \ oldRegion) x y).1 (by
      simpa [sourceCorridorSerialBoundaryRebaseStableExclusiveFaceSeamAt,
        faceRegionalExclusiveSeamGraph, RS, oldRegion, transition] using hadj)
  have hlocalized :=
    sourceCorridorSerialBoundaryRebaseStableExclusiveFaceSeamAt_adj_oldEndpoint_mem_truePrefixCrossing
      realization hcubic hrotation htwoSided hunique offset hnext root hadj
  have hnextInput : nextInput = oldRegion ∪ rebase := by
    simpa [nextInput, oldRegion, rebase, nextOffset] using
      sourceCorridorSerialCutRegionAt_next_eq_prefixCut_union_rebase
        realization hcubic hrotation htwoSided hunique offset hnext
  have htransition : transition = rebase ∪ cell := by
    rfl
  rcases hlocalized with hforward | hbackward
  · rcases hforward with ⟨hxOld, hxBoundary, hyTransition, hyNotOld⟩
    by_cases hyRebase : faceCycleEdge RS root y ∈ rebase
    · exact Or.inl (Or.inr hyRebase)
    · have hyCell : faceCycleEdge RS root y ∈ cell := by
        change faceCycleEdge RS root y ∈ transition at hyTransition
        rw [htransition] at hyTransition
        exact (Finset.mem_union.1 hyTransition).resolve_left hyRebase
      by_cases hxCell : faceCycleEdge RS root x ∈ cell
      · exact Or.inr (Or.inr (Or.inl ⟨hraw.1, hxOld, hxBoundary,
          hxCell, hyCell, hyNotOld, hyRebase⟩))
      · have hxNextInput : faceCycleEdge RS root x ∈ nextInput := by
          rw [hnextInput]
          exact Finset.mem_union_left _ hxOld
        have hyNotNextInput : faceCycleEdge RS root y ∉ nextInput := by
          rw [hnextInput]
          simpa only [Finset.mem_union, not_or] using ⟨hyNotOld, hyRebase⟩
        have hcellSeam :
            (sourceCorridorSerialInputFaceSeamGraphAt realization hcubic
              hrotation htwoSided hunique nextOffset root).Adj x y := by
          apply (faceRegionalSeamGraph_adj_iff RS root nextInput cell x y).2
          exact ⟨hraw.1, Or.inl
            ⟨hxNextInput, hxCell, hyCell, hyNotNextInput⟩⟩
        exact Or.inr (Or.inl
          (sourceCorridorSerialInputFaceSeamGraphAt_adj_touches_outputCrossing
            realization hcubic hrotation htwoSided hunique nextOffset root
              hcellSeam))
  · rcases hbackward with ⟨hyOld, hyBoundary, hxTransition, hxNotOld⟩
    by_cases hxRebase : faceCycleEdge RS root x ∈ rebase
    · exact Or.inl (Or.inl hxRebase)
    · have hxCell : faceCycleEdge RS root x ∈ cell := by
        change faceCycleEdge RS root x ∈ transition at hxTransition
        rw [htransition] at hxTransition
        exact (Finset.mem_union.1 hxTransition).resolve_left hxRebase
      by_cases hyCell : faceCycleEdge RS root y ∈ cell
      · exact Or.inr (Or.inr (Or.inr ⟨hraw.1.symm, hyOld, hyBoundary,
          hyCell, hxCell, hxNotOld, hxRebase⟩))
      · have hyNextInput : faceCycleEdge RS root y ∈ nextInput := by
          rw [hnextInput]
          exact Finset.mem_union_left _ hyOld
        have hxNotNextInput : faceCycleEdge RS root x ∉ nextInput := by
          rw [hnextInput]
          simpa only [Finset.mem_union, not_or] using ⟨hxNotOld, hxRebase⟩
        have hcellSeam :
            (sourceCorridorSerialInputFaceSeamGraphAt realization hcubic
              hrotation htwoSided hunique nextOffset root).Adj x y := by
          apply (faceRegionalSeamGraph_adj_iff RS root nextInput cell x y).2
          exact ⟨hraw.1, Or.inr
            ⟨hxCell, hxNotNextInput, hyNextInput, hyCell⟩⟩
        exact Or.inr (Or.inl
          (sourceCorridorSerialInputFaceSeamGraphAt_adj_touches_outputCrossing
            realization hcubic hrotation htwoSided hunique nextOffset root
              hcellSeam))

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
