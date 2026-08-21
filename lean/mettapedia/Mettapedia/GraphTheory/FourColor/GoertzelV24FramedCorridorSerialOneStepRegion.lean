import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebase

/-!
# The exact state-to-state region of one literal source step

The serial input cut at one source offset and the serial input cut at its
successor are not separated by the literal Cell alone.  The successor input
presentation also displays two new crossing edges.  This file packages the
Cell and those two edges as one local extension and proves the exact
state-to-state region equation.

Tracked connectivity and occurrence-sensitive facial continuation are then
factored twice: first inside the local extension, and then between the old
input region and that extension.  These equations identify the literal
one-step letter that a finite support relation must encode.  They do not claim
that its residual seams are already determined by a boundary profile, compute
a reachable closure, or derive a numerical threshold.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24TerminalProfileFaceUpdate
open GoertzelV24TerminalProfileSeamResidual
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialOneStepRegionEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The local edge region added between two consecutive serial input cuts:
the current literal Cell together with the successor presentation's two new
crossing edges. -/
noncomputable def sourceCorridorSerialOneStepRegionAt
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
  sourceSlabLiteralCellRegionAt realization hcubic hrotation htwoSided hunique
      offset ∪
    sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
      htwoSided hunique offset hnext

/-- One source step is exactly old serial input plus the literal local
extension. -/
theorem sourceCorridorSerialCutRegionAt_next_eq_current_union_oneStep
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
    sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
        hunique (sourceCorridorSerialNextOffset offset hnext) =
      sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
          hunique offset ∪
        sourceCorridorSerialOneStepRegionAt realization hcubic hrotation
          htwoSided hunique offset hnext := by
  rw [sourceCorridorSerialCutRegionAt_next_eq_prefixCut_union_rebase
    realization hcubic hrotation htwoSided hunique offset hnext]
  rw [sourceCorridorSerialPrefixCutDataAt_regionEdges_eq_input_union_cell
    realization hcubic hrotation htwoSided hunique offset]
  simp only [sourceCorridorSerialOneStepRegionAt, Finset.union_assoc]

/-- The tracked seam internal to the one-step local extension, between the
literal Cell and the two rebase edges. -/
def sourceCorridorSerialOneStepInternalTrackedSeamAt
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
  regionalTrackedSeamGraph
    embedded.cellulation.rotation.toRotationSystem
    (sourceSlabLiteralCellRegionAt realization hcubic hrotation htwoSided
      hunique offset)
    (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
      htwoSided hunique offset hnext)
    color first second

/-- The tracked graph internal to the local one-step letter. -/
def sourceCorridorSerialOneStepTrackedGraphAt
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
    (sourceCorridorSerialOneStepRegionAt realization hcubic hrotation htwoSided
      hunique offset hnext) color first second

/-- The local tracked letter is exactly Cell, rebase, and their residual
seam. -/
theorem sourceCorridorSerialOneStepTrackedGraphAt_eq_three_factor
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
    sourceCorridorSerialOneStepTrackedGraphAt realization hcubic hrotation
        htwoSided hunique offset hnext color first second =
      (regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          (sourceSlabLiteralCellRegionAt realization hcubic hrotation
            htwoSided hunique offset) color first second ⊔
        regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
            hrotation htwoSided hunique offset hnext) color first second) ⊔
        sourceCorridorSerialOneStepInternalTrackedSeamAt realization hcubic
          hrotation htwoSided hunique offset hnext color first second := by
  rw [sourceCorridorSerialOneStepTrackedGraphAt,
    sourceCorridorSerialOneStepRegionAt]
  exact regionalTrackedEdgeGraph_union_eq_sup_sup_seam
    embedded.cellulation.rotation.toRotationSystem
    (sourceSlabLiteralCellRegionAt realization hcubic hrotation htwoSided
      hunique offset)
    (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
      htwoSided hunique offset hnext) color first second

/-- The tracked seam attaching the whole local one-step letter to the old
serial input region. -/
def sourceCorridorSerialOneStepAttachmentTrackedSeamAt
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
  regionalTrackedSeamGraph
    embedded.cellulation.rotation.toRotationSystem
    (sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
      hunique offset)
    (sourceCorridorSerialOneStepRegionAt realization hcubic hrotation htwoSided
      hunique offset hnext)
    color first second

/-- The successor tracked state is exactly old state, the local one-step
letter, and their attachment seam. -/
theorem sourceCorridorSerialInputTrackedGraph_next_eq_oneStep_three_factor
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
    regionalTrackedEdgeGraph
        embedded.cellulation.rotation.toRotationSystem
        (sourceCorridorSerialCutRegionAt realization hcubic hrotation
          htwoSided hunique (sourceCorridorSerialNextOffset offset hnext))
        color first second =
      (regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          (sourceCorridorSerialCutRegionAt realization hcubic hrotation
            htwoSided hunique offset) color first second ⊔
        sourceCorridorSerialOneStepTrackedGraphAt realization hcubic hrotation
          htwoSided hunique offset hnext color first second) ⊔
        sourceCorridorSerialOneStepAttachmentTrackedSeamAt realization hcubic
          hrotation htwoSided hunique offset hnext color first second := by
  rw [sourceCorridorSerialCutRegionAt_next_eq_current_union_oneStep
    realization hcubic hrotation htwoSided hunique offset hnext]
  exact regionalTrackedEdgeGraph_union_eq_sup_sup_seam
    embedded.cellulation.rotation.toRotationSystem
    (sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
      hunique offset)
    (sourceCorridorSerialOneStepRegionAt realization hcubic hrotation htwoSided
      hunique offset hnext) color first second

/-- The facial seam internal to the one-step local extension. -/
def sourceCorridorSerialOneStepInternalFaceSeamAt
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
    (sourceSlabLiteralCellRegionAt realization hcubic hrotation htwoSided
      hunique offset)
    (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
      htwoSided hunique offset hnext)

/-- The occurrence-sensitive facial graph internal to the local one-step
letter. -/
def sourceCorridorSerialOneStepFaceGraphAt
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
  faceRegionalAmbientPositionGraph
    embedded.cellulation.rotation.toRotationSystem root
    (sourceCorridorSerialOneStepRegionAt realization hcubic hrotation htwoSided
      hunique offset hnext)

/-- The local facial letter is exactly Cell, rebase, and their residual
seam. -/
theorem sourceCorridorSerialOneStepFaceGraphAt_eq_three_factor
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
    sourceCorridorSerialOneStepFaceGraphAt realization hcubic hrotation
        htwoSided hunique offset hnext root =
      (faceRegionalAmbientPositionGraph
          embedded.cellulation.rotation.toRotationSystem root
          (sourceSlabLiteralCellRegionAt realization hcubic hrotation
            htwoSided hunique offset) ⊔
        faceRegionalAmbientPositionGraph
          embedded.cellulation.rotation.toRotationSystem root
          (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
            hrotation htwoSided hunique offset hnext)) ⊔
        sourceCorridorSerialOneStepInternalFaceSeamAt realization hcubic
          hrotation htwoSided hunique offset hnext root := by
  rw [sourceCorridorSerialOneStepFaceGraphAt,
    sourceCorridorSerialOneStepRegionAt]
  exact faceRegionalAmbientPositionGraph_union_eq_sup_sup_seam
    embedded.cellulation.rotation.toRotationSystem root
    (sourceSlabLiteralCellRegionAt realization hcubic hrotation htwoSided
      hunique offset)
    (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
      htwoSided hunique offset hnext)

/-- The facial seam attaching the whole local one-step letter to the old
serial input region. -/
def sourceCorridorSerialOneStepAttachmentFaceSeamAt
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
    (sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
      hunique offset)
    (sourceCorridorSerialOneStepRegionAt realization hcubic hrotation htwoSided
      hunique offset hnext)

/-- The successor facial state is exactly old state, the local one-step
letter, and their attachment seam. -/
theorem sourceCorridorSerialInputFaceGraph_next_eq_oneStep_three_factor
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
    faceRegionalAmbientPositionGraph
        embedded.cellulation.rotation.toRotationSystem root
        (sourceCorridorSerialCutRegionAt realization hcubic hrotation
          htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)) =
      (faceRegionalAmbientPositionGraph
          embedded.cellulation.rotation.toRotationSystem root
          (sourceCorridorSerialCutRegionAt realization hcubic hrotation
            htwoSided hunique offset) ⊔
        sourceCorridorSerialOneStepFaceGraphAt realization hcubic hrotation
          htwoSided hunique offset hnext root) ⊔
        sourceCorridorSerialOneStepAttachmentFaceSeamAt realization hcubic
          hrotation htwoSided hunique offset hnext root := by
  rw [sourceCorridorSerialCutRegionAt_next_eq_current_union_oneStep
    realization hcubic hrotation htwoSided hunique offset hnext]
  exact faceRegionalAmbientPositionGraph_union_eq_sup_sup_seam
    embedded.cellulation.rotation.toRotationSystem root
    (sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
      hunique offset)
    (sourceCorridorSerialOneStepRegionAt realization hcubic hrotation htwoSided
      hunique offset hnext)

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
