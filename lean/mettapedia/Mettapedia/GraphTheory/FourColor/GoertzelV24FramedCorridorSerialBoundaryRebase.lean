import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicEdgeAdjacencyNeighborhood
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixUpdate

/-!
# The bounded boundary-rebase letter between literal source Cells

After one literal source Cell has been adjoined, its outgoing cut is not
definitionally the input cut of the next Cell.  The accumulated literal
prefix is the same, but the next input presentation also retains its two
displayed crossing edges.  This file isolates that change as a second local
letter in the heterogeneous corridor word.

The region equation is exact.  Its tracked and occurrence-sensitive facial
updates are the old prefix, the two newly displayed edges, and the canonical
residual seam.  Every residual adjacency touches one of those two edges, so
the entire seam lies in their closed cubic edge neighbourhood, of cardinality
at most fourteen.

This is the finite-support geometry of the rebase letter.  It does not claim
that an input profile determines the letter, compute the reachable closure,
or derive a numerical vertex threshold.
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
open GoertzelV24TerminalProfileRegionalCoverage
open GoertzelV24TerminalProfileSeamResidual
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The next source position when there is another literal Cell. -/
def sourceCorridorSerialNextOffset
    {blockLength : Nat} (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) : Fin (blockLength - 3) :=
  ⟨offset.val + 1, hnext⟩

/-- One ordered crossing of the successor input presentation. -/
noncomputable def sourceCorridorSerialBoundaryRebaseCrossingAt
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
    (hnext : offset.val + 1 < blockLength - 3) (step : Fin 2) : G.edgeSet :=
  (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
    (sourceCorridorSerialNextOffset offset hnext)).localLayerPrefixCrossing step

/-- The two displayed edges added when the successor prefix is presented as
the input cut of the next literal Cell. -/
noncomputable def sourceCorridorSerialBoundaryRebaseEdgeSetAt
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
  indexedCrossingEdgeSet
    (sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic hrotation
      htwoSided hunique offset hnext)

/-- The boundary-rebase carrier has at most the two displayed crossing
edges. -/
theorem sourceCorridorSerialBoundaryRebaseEdgeSetAt_card_le_two
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
    (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
      htwoSided hunique offset hnext).card ≤ 2 := by
  exact card_indexedCrossingEdgeSet_le _

/-- The next input cut is exactly the previous output prefix together with
the next pair of displayed crossing edges. -/
theorem sourceCorridorSerialCutRegionAt_next_eq_prefixCut_union_rebase
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
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset).regionEdges ∪
        sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
          hrotation htwoSided hunique offset hnext := by
  simp only [sourceCorridorSerialCutRegionAt,
    sourceCorridorSerialPrefixCutDataAt,
    GoertzelV24RegionalBoundaryProfileFiniteState.regionalBoundaryGraphCutData,
    sourceCorridorSerialBoundaryRebaseEdgeSetAt,
    sourceCorridorSerialNextOffset]
  congr 2

/-- The residual tracked seam of the boundary-rebase letter. -/
def sourceCorridorSerialBoundaryRebaseTrackedSeamAt
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
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
    (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
      htwoSided hunique offset hnext)
    color first second

/-- The next input tracked graph is the exact three-factor rebase update. -/
theorem sourceCorridorSerialInputTrackedGraph_next_eq_rebase_three_factor
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
          (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
            htwoSided hunique offset).regionEdges color first second ⊔
        regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
            hrotation htwoSided hunique offset hnext) color first second) ⊔
        sourceCorridorSerialBoundaryRebaseTrackedSeamAt realization hcubic
          hrotation htwoSided hunique offset hnext color first second := by
  rw [sourceCorridorSerialCutRegionAt_next_eq_prefixCut_union_rebase
    realization hcubic hrotation htwoSided hunique offset hnext]
  exact regionalTrackedEdgeGraph_union_eq_sup_sup_seam
    embedded.cellulation.rotation.toRotationSystem
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
    (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
      htwoSided hunique offset hnext) color first second

/-- The residual occurrence-sensitive facial seam of the boundary rebase. -/
def sourceCorridorSerialBoundaryRebaseFaceSeamAt
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
    (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
      htwoSided hunique offset hnext)

/-- The next input facial graph is the exact three-factor rebase update. -/
theorem sourceCorridorSerialInputFaceGraph_next_eq_rebase_three_factor
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
          (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
            htwoSided hunique offset).regionEdges ⊔
        faceRegionalAmbientPositionGraph
          embedded.cellulation.rotation.toRotationSystem root
          (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
            hrotation htwoSided hunique offset hnext)) ⊔
        sourceCorridorSerialBoundaryRebaseFaceSeamAt realization hcubic
          hrotation htwoSided hunique offset hnext root := by
  rw [sourceCorridorSerialCutRegionAt_next_eq_prefixCut_union_rebase
    realization hcubic hrotation htwoSided hunique offset hnext]
  exact faceRegionalAmbientPositionGraph_union_eq_sup_sup_seam
    embedded.cellulation.rotation.toRotationSystem root
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
    (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
      htwoSided hunique offset hnext)

/-- Every tracked residual turn of the rebase touches one of the two newly
displayed crossing edges. -/
theorem sourceCorridorSerialBoundaryRebaseTrackedSeamAt_adj_touches_newCrossing
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
    (hadj : (sourceCorridorSerialBoundaryRebaseTrackedSeamAt realization
      hcubic hrotation htwoSided hunique offset hnext color first second).Adj
        x y) :
    ∃ step : Fin 2,
      x = sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
          hrotation htwoSided hunique offset hnext step ∨
        y = sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
          hrotation htwoSided hunique offset hnext step := by
  have hraw := (regionalTrackedSeamGraph_adj_iff
    embedded.cellulation.rotation.toRotationSystem
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
    (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
      htwoSided hunique offset hnext) color first second x y).1 hadj
  rcases hraw.2 with hforward | hbackward
  · rcases (mem_indexedCrossingEdgeSet_iff _ _).1 hforward.2.2.1 with
      ⟨step, heq⟩
    exact ⟨step, Or.inr heq.symm⟩
  · rcases (mem_indexedCrossingEdgeSet_iff _ _).1 hbackward.1 with
      ⟨step, heq⟩
    exact ⟨step, Or.inl heq.symm⟩

/-- Every facial residual turn of the rebase touches an occurrence of one of
the two newly displayed crossing edges. -/
theorem sourceCorridorSerialBoundaryRebaseFaceSeamAt_adj_touches_newCrossing
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
    (hadj : (sourceCorridorSerialBoundaryRebaseFaceSeamAt realization hcubic
      hrotation htwoSided hunique offset hnext root).Adj x y) :
    ∃ step : Fin 2,
      faceCycleEdge embedded.cellulation.rotation.toRotationSystem root x =
          sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
            hrotation htwoSided hunique offset hnext step ∨
        faceCycleEdge embedded.cellulation.rotation.toRotationSystem root y =
          sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
            hrotation htwoSided hunique offset hnext step := by
  have hraw := (faceRegionalSeamGraph_adj_iff
    embedded.cellulation.rotation.toRotationSystem root
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
    (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
      htwoSided hunique offset hnext) x y).1 hadj
  rcases hraw.2 with hforward | hbackward
  · rcases (mem_indexedCrossingEdgeSet_iff _ _).1 hforward.2.2.1 with
      ⟨step, heq⟩
    exact ⟨step, Or.inr heq.symm⟩
  · rcases (mem_indexedCrossingEdgeSet_iff _ _).1 hbackward.1 with
      ⟨step, heq⟩
    exact ⟨step, Or.inl heq.symm⟩

/-- The common closed cubic neighbourhood supporting every rebase seam. -/
noncomputable def sourceCorridorSerialBoundaryRebaseCarrierAt
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
  embedded.cellulation.rotation.toRotationSystem.edgeAdjacencyClosedCarrier
    (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
      htwoSided hunique offset hnext)

/-- The rebase seam has a graph-independent carrier bound of fourteen. -/
theorem sourceCorridorSerialBoundaryRebaseCarrierAt_card_le_fourteen
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
    (sourceCorridorSerialBoundaryRebaseCarrierAt realization hcubic hrotation
      htwoSided hunique offset hnext).card ≤ 14 := by
  calc
    _ ≤ 7 *
        (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
          hrotation htwoSided hunique offset hnext).card :=
      embedded.cellulation.rotation.toRotationSystem
        |>.edgeAdjacencyClosedCarrier_card_le_seven_mul hcubic _
    _ ≤ 7 * 2 := Nat.mul_le_mul_left 7
      (sourceCorridorSerialBoundaryRebaseEdgeSetAt_card_le_two realization
        hcubic hrotation htwoSided hunique offset hnext)
    _ = 14 := by norm_num

/-- Every non-isolated tracked seam edge belongs to the same bounded rebase
carrier. -/
theorem sourceCorridorSerialBoundaryRebaseTrackedSeamAt_support_subset_carrier
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
    (sourceCorridorSerialBoundaryRebaseTrackedSeamAt realization hcubic
      hrotation htwoSided hunique offset hnext color first second).support ⊆
      sourceCorridorSerialBoundaryRebaseCarrierAt realization hcubic hrotation
        htwoSided hunique offset hnext := by
  intro edge hedge
  rcases (SimpleGraph.mem_support
      (sourceCorridorSerialBoundaryRebaseTrackedSeamAt realization hcubic
        hrotation htwoSided hunique offset hnext color first second)).1 hedge with
    ⟨neighbor, hadj⟩
  rcases
      sourceCorridorSerialBoundaryRebaseTrackedSeamAt_adj_touches_newCrossing
        realization hcubic hrotation htwoSided hunique offset hnext color
        first second hadj with ⟨step, hedgeNew | hneighborNew⟩
  · apply (embedded.cellulation.rotation.toRotationSystem
      |>.mem_edgeAdjacencyClosedCarrier_iff _ _).2
    exact Or.inl ((mem_indexedCrossingEdgeSet_iff _ _).2
      ⟨step, hedgeNew.symm⟩)
  · apply (embedded.cellulation.rotation.toRotationSystem
      |>.mem_edgeAdjacencyClosedCarrier_iff _ _).2
    refine Or.inr ⟨neighbor,
      (mem_indexedCrossingEdgeSet_iff _ _).2 ⟨step, hneighborNew.symm⟩, ?_⟩
    have hraw := (regionalTrackedSeamGraph_adj_iff
      embedded.cellulation.rotation.toRotationSystem
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges
      (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
        htwoSided hunique offset hnext) color first second edge neighbor).1 hadj
    exact hraw.1.1

/-- Every non-isolated facial seam occurrence projects into the same bounded
edge carrier. -/
theorem sourceCorridorSerialBoundaryRebaseFaceSeamAt_support_projects_carrier
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
    ∀ position ∈
      (sourceCorridorSerialBoundaryRebaseFaceSeamAt realization hcubic
        hrotation htwoSided hunique offset hnext root).support,
      faceCycleEdge embedded.cellulation.rotation.toRotationSystem root
          position ∈
        sourceCorridorSerialBoundaryRebaseCarrierAt realization hcubic
          hrotation htwoSided hunique offset hnext := by
  intro position hposition
  rcases (SimpleGraph.mem_support
      (sourceCorridorSerialBoundaryRebaseFaceSeamAt realization hcubic
        hrotation htwoSided hunique offset hnext root)).1 hposition with
    ⟨neighbor, hadj⟩
  rcases sourceCorridorSerialBoundaryRebaseFaceSeamAt_adj_touches_newCrossing
      realization hcubic hrotation htwoSided hunique offset hnext root hadj with
    ⟨step, hpositionNew | hneighborNew⟩
  · apply (embedded.cellulation.rotation.toRotationSystem
      |>.mem_edgeAdjacencyClosedCarrier_iff _ _).2
    exact Or.inl ((mem_indexedCrossingEdgeSet_iff _ _).2
      ⟨step, hpositionNew.symm⟩)
  · apply (embedded.cellulation.rotation.toRotationSystem
      |>.mem_edgeAdjacencyClosedCarrier_iff _ _).2
    refine Or.inr ⟨_,
      (mem_indexedCrossingEdgeSet_iff _ _).2 ⟨step, hneighborNew.symm⟩, ?_⟩
    have hraw := (faceRegionalSeamGraph_adj_iff
      embedded.cellulation.rotation.toRotationSystem root
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges
      (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
        htwoSided hunique offset hnext) position neighbor).1 hadj
    exact edgeAdjacencyGraph_adj_of_faceCyclePositionGraph_adj
      embedded.cellulation.rotation.toRotationSystem hcubic hrotation root
      hraw.1

/-- Two-sidedness makes the projected facial support injective, hence the
occurrence-sensitive rebase seam itself also has at most fourteen vertices. -/
theorem sourceCorridorSerialBoundaryRebaseFaceSeamAt_support_card_le_fourteen
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
    (sourceCorridorSerialBoundaryRebaseFaceSeamAt realization hcubic hrotation
      htwoSided hunique offset hnext root).support.ncard ≤ 14 := by
  let support :=
    (sourceCorridorSerialBoundaryRebaseFaceSeamAt realization hcubic hrotation
      htwoSided hunique offset hnext root).support
  let project := faceCycleEdge
    embedded.cellulation.rotation.toRotationSystem root
  have himage : project '' support ⊆
      (sourceCorridorSerialBoundaryRebaseCarrierAt realization hcubic hrotation
        htwoSided hunique offset hnext : Set G.edgeSet) := by
    intro edge hedge
    rcases hedge with ⟨position, hposition, rfl⟩
    exact
      sourceCorridorSerialBoundaryRebaseFaceSeamAt_support_projects_carrier
        realization hcubic hrotation htwoSided hunique offset hnext root
        position hposition
  calc
    support.ncard = (project '' support).ncard :=
      (Set.ncard_image_of_injective support
        (faceCycleEdge_injective
          embedded.cellulation.rotation.toRotationSystem htwoSided root)).symm
    _ ≤ (sourceCorridorSerialBoundaryRebaseCarrierAt realization hcubic
          hrotation htwoSided hunique offset hnext : Set G.edgeSet).ncard :=
      Set.ncard_le_ncard himage
    _ = (sourceCorridorSerialBoundaryRebaseCarrierAt realization hcubic
          hrotation htwoSided hunique offset hnext).card :=
      Set.ncard_coe_finset _
    _ ≤ 14 :=
      sourceCorridorSerialBoundaryRebaseCarrierAt_card_le_fourteen realization
        hcubic hrotation htwoSided hunique offset hnext

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
