import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseStableTrackedTransitionFiniteSwitch
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixSeamRelation
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileSeamUnion

/-!
# Reusing the two staged seams in one stable source transition

One stable transition adjoins a boundary rebase and then the successor
literal Cell.  The residual seam against their union is not a third
independent local object: every one of its turns belongs either to the
already-coded rebase seam or to the already-coded successor-Cell seam.

For tracked connectivity, the resulting residual carrier is the union of the
quotient-aware twelve-edge transition switch and the successor Cell's bounded
fourteen-edge outgoing neighborhood, hence has cardinality at most twenty-six.
The facial statement is retained occurrence-sensitively as a graph inclusion.

This removes an independent residual input from the future recurrence.  It
does not yet contract the accumulated prefix factor or compute the successor
stable state.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24TerminalProfileSeamResidual
open GoertzelV24TerminalProfileSeamUnion
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseStableTrackedTransitionSeamEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The tracked residual seam of the whole stable transition is contained in
the supremum of its two temporally ordered literal seams. -/
theorem sourceCorridorSerialBoundaryRebaseStableTransitionTrackedSeamAt_le_stagedSeams
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
    sourceCorridorSerialBoundaryRebaseStableTransitionTrackedSeamAt
        realization hcubic hrotation htwoSided hunique offset hnext color
          first second ≤
      sourceCorridorSerialBoundaryRebaseTrackedSeamAt realization hcubic
          hrotation htwoSided hunique offset hnext color first second ⊔
        sourceCorridorSerialInputTrackedSeamGraphAt realization hcubic
          hrotation htwoSided hunique
          (sourceCorridorSerialNextOffset offset hnext) color first second := by
  unfold sourceCorridorSerialBoundaryRebaseStableTransitionTrackedSeamAt
  unfold sourceCorridorSerialBoundaryRebaseStableTransitionRegionAt
  have hrefine := regionalTrackedSeamGraph_left_union_le
    embedded.cellulation.rotation.toRotationSystem
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
    (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
      htwoSided hunique offset hnext)
    (sourceSlabLiteralCellRegionAt realization hcubic hrotation htwoSided
      hunique (sourceCorridorSerialNextOffset offset hnext))
    color first second
  rw [← sourceCorridorSerialCutRegionAt_next_eq_prefixCut_union_rebase
    realization hcubic hrotation htwoSided hunique offset hnext] at hrefine
  simpa [sourceCorridorSerialBoundaryRebaseTrackedSeamAt,
    sourceCorridorSerialInputTrackedSeamGraphAt] using hrefine

/-- Occurrence-sensitive facial residual for the whole stable transition. -/
def sourceCorridorSerialBoundaryRebaseStableTransitionFaceSeamAt
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
  faceRegionalSeamGraph embedded.cellulation.rotation.toRotationSystem root
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
    (sourceCorridorSerialBoundaryRebaseStableTransitionRegionAt realization
      hcubic hrotation htwoSided hunique offset hnext)

/-- The whole facial residual likewise refines to the rebase and successor
Cell seams already present in the literal five-factor update. -/
theorem sourceCorridorSerialBoundaryRebaseStableTransitionFaceSeamAt_le_stagedSeams
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
    sourceCorridorSerialBoundaryRebaseStableTransitionFaceSeamAt realization
        hcubic hrotation htwoSided hunique offset hnext root ≤
      sourceCorridorSerialBoundaryRebaseFaceSeamAt realization hcubic
          hrotation htwoSided hunique offset hnext root ⊔
        sourceCorridorSerialInputFaceSeamGraphAt realization hcubic hrotation
          htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
            root := by
  unfold sourceCorridorSerialBoundaryRebaseStableTransitionFaceSeamAt
  unfold sourceCorridorSerialBoundaryRebaseStableTransitionRegionAt
  have hrefine := faceRegionalSeamGraph_left_union_le
    embedded.cellulation.rotation.toRotationSystem root
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
    (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
      htwoSided hunique offset hnext)
    (sourceSlabLiteralCellRegionAt realization hcubic hrotation htwoSided
      hunique (sourceCorridorSerialNextOffset offset hnext))
  rw [← sourceCorridorSerialCutRegionAt_next_eq_prefixCut_union_rebase
    realization hcubic hrotation htwoSided hunique offset hnext] at hrefine
  simpa [sourceCorridorSerialBoundaryRebaseFaceSeamAt,
    sourceCorridorSerialInputFaceSeamGraphAt] using hrefine

/-- Actual ambient edges sufficient for every tracked residual turn of one
stable transition. -/
noncomputable def sourceCorridorSerialBoundaryRebaseStableTransitionResidualCarrierAt
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
    (hnextNext :
      (sourceCorridorSerialNextOffset offset hnext).val + 1 < blockLength - 3) :
    Finset G.edgeSet :=
  sourceCorridorSerialBoundaryRebaseStableTransitionFiniteSwitchAt realization
      hcubic hrotation htwoSided hunique offset hnext hnextNext ∪
    sourceCorridorSerialOutgoingEdgeCarrierAt realization hcubic hrotation
      htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)

/-- Quotienting all overlaps can only improve the `12 + 14` bound. -/
theorem sourceCorridorSerialBoundaryRebaseStableTransitionResidualCarrierAt_card_le_twentySix
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
    (hnextNext :
      (sourceCorridorSerialNextOffset offset hnext).val + 1 < blockLength - 3) :
    (sourceCorridorSerialBoundaryRebaseStableTransitionResidualCarrierAt
      realization hcubic hrotation htwoSided hunique offset hnext hnextNext
      ).card ≤ 26 := by
  calc
    _ ≤
        (sourceCorridorSerialBoundaryRebaseStableTransitionFiniteSwitchAt
          realization hcubic hrotation htwoSided hunique offset hnext
            hnextNext).card +
        (sourceCorridorSerialOutgoingEdgeCarrierAt realization hcubic hrotation
          htwoSided hunique
          (sourceCorridorSerialNextOffset offset hnext)).card :=
      Finset.card_union_le _ _
    _ ≤ 12 + 14 := Nat.add_le_add
      (sourceCorridorSerialBoundaryRebaseStableTransitionFiniteSwitchAt_card_le_twelve
        realization hcubic hrotation htwoSided hunique offset hnext hnextNext)
      (sourceCorridorSerialOutgoingEdgeCarrierAt_card_le_fourteen realization
        hcubic hrotation htwoSided hunique
        (sourceCorridorSerialNextOffset offset hnext))
    _ = 26 := by norm_num

/-- Every tracked turn in the combined residual lies on the bounded
twenty-six-edge carrier assembled from the two staged seam carriers. -/
theorem sourceCorridorSerialBoundaryRebaseStableTransitionTrackedSeamAt_support_subset_residualCarrier
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
    (hnextNext :
      (sourceCorridorSerialNextOffset offset hnext).val + 1 < blockLength - 3)
    (color : G.edgeSet → Color) (first second : Color) :
    (sourceCorridorSerialBoundaryRebaseStableTransitionTrackedSeamAt
      realization hcubic hrotation htwoSided hunique offset hnext color first
        second).support ⊆
      sourceCorridorSerialBoundaryRebaseStableTransitionResidualCarrierAt
        realization hcubic hrotation htwoSided hunique offset hnext
          hnextNext := by
  intro edge hedge
  rcases (SimpleGraph.mem_support _).1 hedge with ⟨neighbor, hadj⟩
  have hstaged :=
    sourceCorridorSerialBoundaryRebaseStableTransitionTrackedSeamAt_le_stagedSeams
      realization hcubic hrotation htwoSided hunique offset hnext color first
        second hadj
  rcases (SimpleGraph.sup_adj _ _ edge neighbor).1 hstaged with
    hrebase | hcell
  · apply Finset.mem_union_left
    apply sourceCorridorSerialBoundaryRebaseFiniteSwitchAt_subset_stableTransitionFiniteSwitch
      realization hcubic hrotation htwoSided hunique offset hnext hnextNext
    apply sourceCorridorSerialBoundaryRebaseTrackedSeamAt_support_subset_finiteSwitch
      realization hcubic hrotation htwoSided hunique offset hnext color first
        second
    exact hrebase.mem_support_left
  · apply Finset.mem_union_right
    apply sourceCorridorSerialInputTrackedSeamGraphAt_support_subset_outgoingCarrier
      realization hcubic hrotation htwoSided hunique
        (sourceCorridorSerialNextOffset offset hnext) color first second
    exact hcell.mem_support_left

end AnnularEmbedding

end SourceTrail

end


end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
