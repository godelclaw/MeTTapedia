import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerLiteralCount
import Mettapedia.GraphTheory.FourColor.GoertzelV24RegionalBoundaryProfileFiniteState

/-!
# Serial prefixes of actual opened-source Cells

The route-correct cumulative carrier is the union of the literal complementary
Cell regions, not the union of complete hexagon boundaries.  The older serial
prefix construction has this shape but assumes global cubicity and global
face two-sidedness, both false on the opened source annulus.

This file reconstructs the carrier directly from the source-local Cell data.
For every indexed Cell it names the literal region, its two ordered incoming
and outgoing crossings, the prefix before the Cell, and the prefix after the
Cell.  The successor equation is set-theoretic and the corresponding complete
five-coordinate graph-derived profiles are defined from the source coloring.

No transition adequacy is claimed here.  In particular, relating these
cumulative profiles to the joint local `Count` receipt and composing the
separate boundary rebase remain later theorems.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularCrosscut
open GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialPrefixRegionEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The interior corridor position underlying one indexed literal Cell. -/
def sourceLocalLayerInteriorAt {blockLength : Nat}
    (offset : Fin (blockLength - 3)) : CorridorInterior blockLength :=
  corridorInteriorOfOffset ⟨offset.val, by
    have hoffset := (Nat.lt_sub_iff_add_lt).mp offset.isLt
    omega⟩

/-- Every indexed literal Cell has the consecutive corridor face needed by
the source-local layer construction. -/
theorem sourceLocalLayerInteriorAt_hasNext {blockLength : Nat}
    (offset : Fin (blockLength - 3)) :
    (sourceLocalLayerInteriorAt offset).center.val + 2 < blockLength := by
  have hoffset := (Nat.lt_sub_iff_add_lt).mp offset.isLt
  change offset.val + 1 + 2 < blockLength
  omega

/-- The actual source-selected local layer pair at one corridor offset. -/
noncomputable def sourceLocalLayerPairAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    LocalLayerPair web corridor (sourceLocalLayerInteriorAt offset)
      (sourceLocalLayerInteriorAt_hasNext offset) :=
  sourceLocalLayerPair corridor hunique (sourceLocalLayerInteriorAt offset)
    (sourceLocalLayerInteriorAt_hasNext offset)

/-- The canonical deletion-side boundary datum at one indexed Cell. -/
noncomputable def sourceLocalLayerBoundaryAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    SeparatedAlignedSimpleDualCrosscuts.SourceCrosscutBoundaryData
      web.annular.cellulation.rotation
      ((sourceLocalLayerPairAt corridor hunique offset).separatedLocalLayerPair
        hunique) :=
  sourceLocalLayerPairCrosscutBoundaryData corridor hunique
    (sourceLocalLayerInteriorAt offset)
    (sourceLocalLayerInteriorAt_hasNext offset)

/-- The incoming two-edge crossing in literal facial-dual path order. -/
noncomputable def sourceLocalLayerLeftCrossingAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (step : Fin 2) : G.edgeSet :=
  let layers := sourceLocalLayerPairAt corridor hunique offset
  layers.firstLayer.crossingEdge hunique
    ⟨step.val, by
      simpa [LocalLayerPair.firstLayer, LocalLayerPair.firstWalk] using step.isLt⟩

/-- The outgoing two-edge crossing of the same literal Cell. -/
noncomputable def sourceLocalLayerRightCrossingAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (step : Fin 2) : G.edgeSet :=
  let layers := sourceLocalLayerPairAt corridor hunique offset
  layers.secondLayer.crossingEdge hunique
    ⟨step.val, by
      simpa [LocalLayerPair.secondLayer, LocalLayerPair.secondWalk] using step.isLt⟩

theorem sourceLocalLayerLeftCrossingAt_injective
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    Function.Injective (sourceLocalLayerLeftCrossingAt corridor hunique offset) := by
  intro first second heq
  let layers := sourceLocalLayerPairAt corridor hunique offset
  have hindex := layers.firstLayer.crossingEdge_injective
    (orbitFace_incidence_le_two web.annular.RS) hunique heq
  apply Fin.ext
  exact congrArg Fin.val hindex

theorem sourceLocalLayerRightCrossingAt_injective
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    Function.Injective (sourceLocalLayerRightCrossingAt corridor hunique offset) := by
  intro first second heq
  let layers := sourceLocalLayerPairAt corridor hunique offset
  have hindex := layers.secondLayer.crossingEdge_injective
    (orbitFace_incidence_le_two web.annular.RS) hunique heq
  apply Fin.ext
  exact congrArg Fin.val hindex

/-- The exact complementary-region edge carrier of one actual source Cell. -/
noncomputable def sourceLocalLayerCellRegionAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) : Finset G.edgeSet :=
  let layers := sourceLocalLayerPairAt corridor hunique offset
  let pair := layers.separatedLocalLayerPair hunique
  let boundary := sourceLocalLayerBoundaryAt corridor hunique offset
  (pair.sourceCrosscutComplementBoundaryProfileData
    web.annular.cellulation.rotation boundary).regionEdges

/-- The incoming crossing is part of its literal Cell carrier. -/
theorem sourceLocalLayerCellRegionAt_leftCrossing
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (step : Fin 2) :
    sourceLocalLayerLeftCrossingAt corridor hunique offset step ∈
      sourceLocalLayerCellRegionAt corridor hunique offset := by
  let layers := sourceLocalLayerPairAt corridor hunique offset
  let pair := layers.separatedLocalLayerPair hunique
  let boundary := sourceLocalLayerBoundaryAt corridor hunique offset
  let cellData := pair.sourceCrosscutComplementBoundaryProfileData
    web.annular.cellulation.rotation boundary
  let index : Fin layers.firstLayer.walk.length :=
    ⟨step.val, by
      simpa [LocalLayerPair.firstLayer, LocalLayerPair.firstWalk] using step.isLt⟩
  have hport := pair.sourceCrosscutComplementBoundaryProfileData_portsInRegion
    web.annular.cellulation.rotation boundary
    (.inl (pair.sourceCrosscutComplementLeftCombinedIndex
      web.annular.cellulation.rotation boundary index))
  change cellData.crossingEdge
      (pair.sourceCrosscutComplementLeftCombinedIndex
        web.annular.cellulation.rotation boundary index) ∈ cellData.regionEdges at hport
  rw [pair.sourceCrosscutComplementBoundaryProfileData_crossingEdge_left] at hport
  simpa [sourceLocalLayerCellRegionAt, sourceLocalLayerLeftCrossingAt, layers,
    pair, boundary, cellData, index,
    LocalLayerPair.separatedLocalLayerPair] using hport

/-- The outgoing crossing is part of the same literal Cell carrier. -/
theorem sourceLocalLayerCellRegionAt_rightCrossing
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (step : Fin 2) :
    sourceLocalLayerRightCrossingAt corridor hunique offset step ∈
      sourceLocalLayerCellRegionAt corridor hunique offset := by
  let layers := sourceLocalLayerPairAt corridor hunique offset
  let pair := layers.separatedLocalLayerPair hunique
  let boundary := sourceLocalLayerBoundaryAt corridor hunique offset
  let cellData := pair.sourceCrosscutComplementBoundaryProfileData
    web.annular.cellulation.rotation boundary
  let index : Fin layers.firstLayer.walk.length :=
    ⟨step.val, by
      simpa [LocalLayerPair.firstLayer, LocalLayerPair.firstWalk] using step.isLt⟩
  have hport := pair.sourceCrosscutComplementBoundaryProfileData_portsInRegion
    web.annular.cellulation.rotation boundary
    (.inl (pair.sourceCrosscutComplementRightCombinedIndex
      web.annular.cellulation.rotation boundary index))
  change cellData.crossingEdge
      (pair.sourceCrosscutComplementRightCombinedIndex
        web.annular.cellulation.rotation boundary index) ∈ cellData.regionEdges at hport
  rw [pair.sourceCrosscutComplementBoundaryProfileData_crossingEdge_right] at hport
  have hrightIndex : Fin.cast pair.length_eq index =
      (⟨step.val, by
        simpa [LocalLayerPair.secondLayer, LocalLayerPair.secondWalk] using
          step.isLt⟩ : Fin layers.secondLayer.walk.length) := by
    apply Fin.ext
    rfl
  rw [hrightIndex] at hport
  simpa [sourceLocalLayerCellRegionAt, sourceLocalLayerRightCrossingAt, layers,
    pair, boundary, cellData, index,
    LocalLayerPair.separatedLocalLayerPair] using hport

/-- Union of the first `cut` actual literal Cell regions. -/
noncomputable def sourceLocalLayerSerialPrefixRegion
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (cut : Nat) : Finset G.edgeSet :=
  (Finset.univ.filter fun offset : Fin (blockLength - 3) => offset.val < cut)
    |>.biUnion (sourceLocalLayerCellRegionAt corridor hunique)

@[simp]
theorem sourceLocalLayerSerialPrefixRegion_zero
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :
    sourceLocalLayerSerialPrefixRegion corridor hunique 0 = ∅ := by
  ext edge
  simp [sourceLocalLayerSerialPrefixRegion]

/-- Adjoining one in-range source position adds exactly its literal Cell. -/
theorem sourceLocalLayerSerialPrefixRegion_succ
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength cut : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (hcut : cut < blockLength - 3) :
    sourceLocalLayerSerialPrefixRegion corridor hunique (cut + 1) =
      sourceLocalLayerSerialPrefixRegion corridor hunique cut ∪
        sourceLocalLayerCellRegionAt corridor hunique ⟨cut, hcut⟩ := by
  classical
  ext edge
  simp only [sourceLocalLayerSerialPrefixRegion, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨offset, hoffset, hedge⟩
    by_cases hbefore : offset.val < cut
    · exact Or.inl ⟨offset, hbefore, hedge⟩
    · have heq : offset = (⟨cut, hcut⟩ : Fin (blockLength - 3)) := by
        apply Fin.ext
        have hle : offset.val ≤ cut := Nat.le_of_lt_succ hoffset
        have hge : cut ≤ offset.val := Nat.le_of_not_gt hbefore
        exact Nat.le_antisymm hle hge
      exact Or.inr (heq ▸ hedge)
  · rintro (⟨offset, hoffset, hedge⟩ | hedge)
    · exact ⟨offset, lt_trans hoffset (Nat.lt_succ_self cut), hedge⟩
    · exact ⟨⟨cut, hcut⟩, Nat.lt_succ_self cut, hedge⟩

/-- The open cumulative input at one moving cut. -/
noncomputable def sourceLocalLayerSerialInputRegionAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) : Finset G.edgeSet :=
  sourceLocalLayerSerialPrefixRegion corridor hunique offset.val ∪
    indexedCrossingEdgeSet
      (sourceLocalLayerLeftCrossingAt corridor hunique offset)

/-- The cumulative output after adjoining the indexed Cell. -/
noncomputable def sourceLocalLayerSerialOutputRegionAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) : Finset G.edgeSet :=
  sourceLocalLayerSerialPrefixRegion corridor hunique (offset.val + 1)

theorem sourceLocalLayerSerialInputRegionAt_leftCrossing
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (step : Fin 2) :
    sourceLocalLayerLeftCrossingAt corridor hunique offset step ∈
      sourceLocalLayerSerialInputRegionAt corridor hunique offset := by
  apply Finset.mem_union_right
  exact (mem_indexedCrossingEdgeSet_iff _ _).2 ⟨step, rfl⟩

theorem sourceLocalLayerSerialOutputRegionAt_rightCrossing
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (step : Fin 2) :
    sourceLocalLayerRightCrossingAt corridor hunique offset step ∈
      sourceLocalLayerSerialOutputRegionAt corridor hunique offset := by
  rw [sourceLocalLayerSerialOutputRegionAt,
    sourceLocalLayerSerialPrefixRegion_succ corridor hunique offset.isLt]
  exact Finset.mem_union_right _
    (sourceLocalLayerCellRegionAt_rightCrossing corridor hunique offset step)

/-- The moving input glued to its literal Cell is exactly the cumulative
output region. -/
theorem sourceLocalLayerSerialInputRegionAt_union_cell
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    sourceLocalLayerSerialInputRegionAt corridor hunique offset ∪
        sourceLocalLayerCellRegionAt corridor hunique offset =
      sourceLocalLayerSerialOutputRegionAt corridor hunique offset := by
  rw [sourceLocalLayerSerialOutputRegionAt,
    sourceLocalLayerSerialPrefixRegion_succ corridor hunique offset.isLt]
  ext edge
  constructor
  · intro hedge
    rcases Finset.mem_union.1 hedge with hinput | hcell
    · rcases Finset.mem_union.1 hinput with hprefix | hcrossing
      · exact Finset.mem_union_left _ hprefix
      · rcases (mem_indexedCrossingEdgeSet_iff _ _).1 hcrossing with
          ⟨step, rfl⟩
        exact Finset.mem_union_right _
          (sourceLocalLayerCellRegionAt_leftCrossing corridor hunique offset step)
    · exact Finset.mem_union_right _ hcell
  · intro hedge
    rcases Finset.mem_union.1 hedge with hprefix | hcell
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hprefix)
    · exact Finset.mem_union_right _ hcell

/-- The exact graph-derived cumulative input profile on the opened source. -/
noncomputable def sourceLocalLayerSerialInputBoundedProfileAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    BoundedCorridorCutProfile 2 0 4 :=
  regionalBoundaryBoundedProfile web.annular.RS
    (sourceLocalLayerSerialInputRegionAt corridor hunique offset)
    (sourceLocalLayerLeftCrossingAt corridor hunique offset) coloring
    (fun _ => web.tait _)

/-- The exact graph-derived cumulative output profile after one source Cell. -/
noncomputable def sourceLocalLayerSerialOutputBoundedProfileAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    BoundedCorridorCutProfile 2 0 4 :=
  regionalBoundaryBoundedProfile web.annular.RS
    (sourceLocalLayerSerialOutputRegionAt corridor hunique offset)
    (sourceLocalLayerRightCrossingAt corridor hunique offset) coloring
    (fun _ => web.tait _)

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
