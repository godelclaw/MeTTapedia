import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixCombinedCell
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSourceProfileWord

/-!
# Serial prefixes of the literal source Cells

The source's corridor generators are the complementary removed regions
between consecutive layer boundaries.  They are not the unions of complete
hex-face boundaries used by the older geometric prefix construction: a
complete hexagon can contain a tracked long arc that the literal open Cell
does not contain.

This file therefore starts the cumulative transfer carrier from the actual
source Cells.  It names the removed edge region at each source position and
forms prefixes by taking source-ordered unions of those regions.  The
successor equation is literal: adjoining one position adds exactly that
Cell's region.  No profile update, region adjacency, or identification with
the final annular splice is asserted here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24AnnularCrosscut
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialPrefixRegionEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The literal removed-region edge carrier of the source Cell at one
indexed corridor position. -/
noncomputable def sourceSlabLiteralCellRegionAt
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
    (offset : Fin (blockLength - 3)) : Finset G.edgeSet :=
  let interface :=
    sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique offset
  (interface.separatedLocalLayerPair
      |>.sourceCrosscutComplementBoundaryProfileData
        embedded.cellulation.rotation
        (interface.localLayerPairSourceCrosscutBoundaryData hcubic)).regionEdges

/-- The incoming two-edge source interface is genuinely part of its literal
Cell region. -/
theorem sourceSlabLiteralCellRegionAt_leftCrossing
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
    (offset : Fin (blockLength - 3)) (step : Fin 2) :
    (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).localLayerPrefixCrossing step ∈
      sourceSlabLiteralCellRegionAt realization hcubic hrotation htwoSided
        hunique offset := by
  let interface :=
    sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique offset
  let pair := interface.separatedLocalLayerPair
  let boundary := interface.localLayerPairSourceCrosscutBoundaryData hcubic
  let cutData := pair.sourceCrosscutComplementBoundaryProfileData
    embedded.cellulation.rotation boundary
  have hport := pair.sourceCrosscutComplementBoundaryProfileData_portsInRegion
    embedded.cellulation.rotation boundary
    (.inl (interface.localLayerPairCellLeftCombinedIndex hcubic step))
  change cutData.crossingEdge
      (interface.localLayerPairCellLeftCombinedIndex hcubic step) ∈
    cutData.regionEdges at hport
  rw [interface.localLayerPairCellCombinedData_crossingEdge_left] at hport
  exact hport

/-- The outgoing two-edge source interface is genuinely part of the same
literal Cell region. -/
theorem sourceSlabLiteralCellRegionAt_rightCrossing
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
    (offset : Fin (blockLength - 3)) (step : Fin 2) :
    (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).nextLocalLayerPrefixCrossing step ∈
      sourceSlabLiteralCellRegionAt realization hcubic hrotation htwoSided
        hunique offset := by
  let interface :=
    sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique offset
  let pair := interface.separatedLocalLayerPair
  let boundary := interface.localLayerPairSourceCrosscutBoundaryData hcubic
  let cutData := pair.sourceCrosscutComplementBoundaryProfileData
    embedded.cellulation.rotation boundary
  have hport := pair.sourceCrosscutComplementBoundaryProfileData_portsInRegion
    embedded.cellulation.rotation boundary
    (.inl (interface.localLayerPairCellRightCombinedIndex hcubic step))
  change cutData.crossingEdge
      (interface.localLayerPairCellRightCombinedIndex hcubic step) ∈
    cutData.regionEdges at hport
  rw [interface.localLayerPairCellCombinedData_crossingEdge_right] at hport
  exact hport

/-- The union of the first `cut` literal source Cells.  The filter keeps the
definition total when `cut` lies beyond the realized corridor; successor
lemmas state the meaningful in-range behavior explicitly. -/
noncomputable def sourceCorridorSerialPrefixRegion
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
    (cut : Nat) : Finset G.edgeSet :=
  (Finset.univ.filter fun offset : Fin (blockLength - 3) => offset.val < cut)
    |>.biUnion
      (sourceSlabLiteralCellRegionAt realization hcubic hrotation htwoSided
        hunique)

@[simp]
theorem sourceCorridorSerialPrefixRegion_zero
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
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))) :
    sourceCorridorSerialPrefixRegion realization hcubic hrotation htwoSided
        hunique 0 = ∅ := by
  ext edge
  simp [sourceCorridorSerialPrefixRegion]

/-- Adjoining one in-range source position adds exactly its literal Cell
region to the serial prefix. -/
theorem sourceCorridorSerialPrefixRegion_succ
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength cut : Nat}
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
    (hcut : cut < blockLength - 3) :
    sourceCorridorSerialPrefixRegion realization hcubic hrotation htwoSided
        hunique (cut + 1) =
      sourceCorridorSerialPrefixRegion realization hcubic hrotation htwoSided
          hunique cut ∪
        sourceSlabLiteralCellRegionAt realization hcubic hrotation htwoSided
          hunique ⟨cut, hcut⟩ := by
  classical
  ext edge
  simp only [sourceCorridorSerialPrefixRegion, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨offset, hoffset, hedge⟩
    by_cases hbefore : offset.val < cut
    · exact Or.inl ⟨offset, hbefore, hedge⟩
    · have heq : offset = (⟨cut, hcut⟩ : Fin (blockLength - 3)) := by
        apply Fin.ext
        have hle : offset.val ≤ cut := by omega
        have hge : cut ≤ offset.val := Nat.le_of_not_gt hbefore
        exact Nat.le_antisymm hle hge
      exact Or.inr (heq ▸ hedge)
  · rintro (⟨offset, hoffset, hedge⟩ | hedge)
    · exact ⟨offset, lt_trans hoffset (Nat.lt_succ_self cut), hedge⟩
    · refine ⟨⟨cut, hcut⟩, ?_, hedge⟩
      exact Nat.lt_succ_self cut

/-- Every edge of the newly adjoined Cell belongs to the corresponding
successor prefix. -/
theorem sourceSlabLiteralCellRegionAt_subset_serialPrefix_succ
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength cut : Nat}
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
    (hcut : cut < blockLength - 3) :
    sourceSlabLiteralCellRegionAt realization hcubic hrotation htwoSided
        hunique ⟨cut, hcut⟩ ⊆
      sourceCorridorSerialPrefixRegion realization hcubic hrotation htwoSided
        hunique (cut + 1) := by
  rw [sourceCorridorSerialPrefixRegion_succ realization hcubic hrotation
    htwoSided hunique hcut]
  exact Finset.subset_union_right

/-- The open prefix at one moving cut.  Besides the Cells strictly to its
left, it contains the two incoming cut edges themselves.  At cut zero this
is the identity interface rather than an empty edge carrier; at later cuts
the same two edges are the shared boundary with the next literal Cell. -/
noncomputable def sourceCorridorSerialCutRegionAt
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
    (offset : Fin (blockLength - 3)) : Finset G.edgeSet :=
  sourceCorridorSerialPrefixRegion realization hcubic hrotation htwoSided
      hunique offset.val ∪
    indexedCrossingEdgeSet
      ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).localLayerPrefixCrossing)

/-- Each incoming coordinate is an actual edge of the corresponding open
prefix carrier, including at the zero-length identity prefix. -/
theorem sourceCorridorSerialCutRegionAt_inputCrossing
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
    (offset : Fin (blockLength - 3)) (step : Fin 2) :
    (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).localLayerPrefixCrossing step ∈
      sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
        hunique offset := by
  apply Finset.mem_union_right
  exact (mem_indexedCrossingEdgeSet_iff _ _).2 ⟨step, rfl⟩

/-- Gluing the next literal Cell to its open input prefix gives exactly the
successor prefix.  The displayed input stubs add no spurious edges because
they are already part of that Cell's literal regional carrier. -/
theorem sourceCorridorSerialCutRegionAt_union_cell
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
    (offset : Fin (blockLength - 3)) :
    sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
          hunique offset ∪
        sourceSlabLiteralCellRegionAt realization hcubic hrotation htwoSided
          hunique offset =
      sourceCorridorSerialPrefixRegion realization hcubic hrotation htwoSided
        hunique (offset.val + 1) := by
  rw [sourceCorridorSerialPrefixRegion_succ realization hcubic hrotation
    htwoSided hunique offset.isLt]
  ext edge
  constructor
  · intro hedge
    rcases Finset.mem_union.1 hedge with hcut | hcell
    · rcases Finset.mem_union.1 hcut with hprefix | hcrossing
      · exact Finset.mem_union_left _ hprefix
      · rcases (mem_indexedCrossingEdgeSet_iff _ _).1 hcrossing with
          ⟨step, rfl⟩
        exact Finset.mem_union_right _
          (sourceSlabLiteralCellRegionAt_leftCrossing realization hcubic
            hrotation htwoSided hunique offset step)
    · exact Finset.mem_union_right _ hcell
  · intro hedge
    rcases Finset.mem_union.1 hedge with hprefix | hcell
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hprefix)
    · exact Finset.mem_union_right _ hcell

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
