import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedLocalLayerCount
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseLocalLayerFormation
import Mettapedia.GraphTheory.FourColor.GoertzelV24RegionalBoundaryProfileFiniteState

/-!
# Cumulative prefixes of pointwise-selected literal Cells

The literal selected-Cell `Count` has an eight-fragment joint receipt because
it sees both two-edge boundaries at once.  The cumulative automaton instead
stores the boundary-local profile of the prefix at one moving two-edge cut,
and therefore has at most four fragments.  This file constructs those two
different carriers from the same selected primal edges.

Everything is colouring-free until the final profile definitions.  In
particular, only the restricted annular interior-face uniqueness receipt is
used; the refuted global unique-shared-edge hypothesis is absent.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24SelectedDualPathTransversal
open GoertzelV24SelectedDualPathTransversal.SeparatedAlignedSelectedDualTransversals
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedSerialPrefixRegionEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Formation

/-- The interior corridor position underlying one indexed selected Cell. -/
def pointwiseSelectedSourceLocalLayerInteriorAt {blockLength : Nat}
    (offset : Fin (blockLength - 3)) : CorridorInterior blockLength :=
  corridorInteriorOfOffset ⟨offset.val, by
    have hoffset := (Nat.lt_sub_iff_add_lt).mp offset.isLt
    omega⟩

/-- Every indexed selected Cell has its consecutive successor face. -/
theorem pointwiseSelectedSourceLocalLayerInteriorAt_hasNext
    {blockLength : Nat} (offset : Fin (blockLength - 3)) :
    (pointwiseSelectedSourceLocalLayerInteriorAt offset).center.val + 2 <
      blockLength := by
  have hoffset := (Nat.lt_sub_iff_add_lt).mp offset.isLt
  change offset.val + 1 + 2 < blockLength
  omega

/-- Canonical colouring-free local layer pair at one corridor offset. -/
noncomputable def pointwiseSelectedSourceLocalLayerPairAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    LocalLayerPair formation corridor
      (pointwiseSelectedSourceLocalLayerInteriorAt offset)
      (pointwiseSelectedSourceLocalLayerInteriorAt_hasNext offset) :=
  Classical.choice
    (LocalLayerFormation.exists_pointwiseLocalLayerPair_of_interiorUnique
      formation corridor hinterior
      (pointwiseSelectedSourceLocalLayerInteriorAt offset)
      (pointwiseSelectedSourceLocalLayerInteriorAt_hasNext offset))

/-- Canonical selected deletion-side boundary at one indexed Cell. -/
noncomputable def pointwiseSelectedSourceLocalLayerBoundaryAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :=
  (pointwiseSelectedSourceLocalLayerPairAt formation corridor hinterior offset)
    |>.pointwiseSelectedSourceBoundaryData hinterior

/-- Incoming selected crossing in the literal facial-dual path order. -/
noncomputable def pointwiseSelectedSourceLocalLayerLeftCrossingAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) (step : Fin 2) : G.edgeSet :=
  let layers := pointwiseSelectedSourceLocalLayerPairAt formation corridor
    hinterior offset
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  pair.left.crossingEdge ⟨step.val, by
    simpa [pair, Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
      Formation.LocalLayerPair.pointwiseSelectedFirstLayer,
      Formation.LocalLayerPair.firstLayer,
      Formation.LocalLayerPair.firstWalk] using step.isLt⟩

/-- Outgoing selected crossing of the same literal Cell. -/
noncomputable def pointwiseSelectedSourceLocalLayerRightCrossingAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) (step : Fin 2) : G.edgeSet :=
  let layers := pointwiseSelectedSourceLocalLayerPairAt formation corridor
    hinterior offset
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  pair.right.crossingEdge ⟨step.val, by
    simpa [pair, Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
      Formation.LocalLayerPair.pointwiseSelectedSecondLayer,
      Formation.LocalLayerPair.secondLayer,
      Formation.LocalLayerPair.secondWalk] using step.isLt⟩

theorem pointwiseSelectedSourceLocalLayerLeftCrossingAt_injective
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    Function.Injective
      (pointwiseSelectedSourceLocalLayerLeftCrossingAt formation corridor
        hinterior offset) := by
  intro first second heq
  let layers := pointwiseSelectedSourceLocalLayerPairAt formation corridor
    hinterior offset
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  let boundary := pointwiseSelectedSourceLocalLayerBoundaryAt formation corridor
    hinterior offset
  let firstIndex : Fin pair.left.crosscut.walk.length := ⟨first.val, by
    simpa [pair, Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
      Formation.LocalLayerPair.pointwiseSelectedFirstLayer,
      Formation.LocalLayerPair.firstLayer,
      Formation.LocalLayerPair.firstWalk] using first.isLt⟩
  let secondIndex : Fin pair.left.crosscut.walk.length := ⟨second.val, by
    simpa [pair, Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
      Formation.LocalLayerPair.pointwiseSelectedFirstLayer,
      Formation.LocalLayerPair.firstLayer,
      Formation.LocalLayerPair.firstWalk] using second.isLt⟩
  have hindex : firstIndex = secondIndex := boundary.leftInjective (by
    simpa [pointwiseSelectedSourceLocalLayerLeftCrossingAt, layers, pair,
      firstIndex, secondIndex] using heq)
  apply Fin.ext
  exact congrArg Fin.val hindex

theorem pointwiseSelectedSourceLocalLayerRightCrossingAt_injective
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    Function.Injective
      (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
        hinterior offset) := by
  intro first second heq
  let layers := pointwiseSelectedSourceLocalLayerPairAt formation corridor
    hinterior offset
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  let boundary := pointwiseSelectedSourceLocalLayerBoundaryAt formation corridor
    hinterior offset
  let firstIndex : Fin pair.right.crosscut.walk.length := ⟨first.val, by
    simpa [pair, Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
      Formation.LocalLayerPair.pointwiseSelectedSecondLayer,
      Formation.LocalLayerPair.secondLayer,
      Formation.LocalLayerPair.secondWalk] using first.isLt⟩
  let secondIndex : Fin pair.right.crosscut.walk.length := ⟨second.val, by
    simpa [pair, Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
      Formation.LocalLayerPair.pointwiseSelectedSecondLayer,
      Formation.LocalLayerPair.secondLayer,
      Formation.LocalLayerPair.secondWalk] using second.isLt⟩
  have hindex : firstIndex = secondIndex := boundary.rightInjective (by
    simpa [pointwiseSelectedSourceLocalLayerRightCrossingAt, layers, pair,
      firstIndex, secondIndex] using heq)
  apply Fin.ext
  exact congrArg Fin.val hindex

/-- Exact selected complementary-region edge carrier of one literal Cell. -/
noncomputable def pointwiseSelectedSourceLocalLayerCellRegionAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) : Finset G.edgeSet :=
  let layers := pointwiseSelectedSourceLocalLayerPairAt formation corridor
    hinterior offset
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  let boundary := pointwiseSelectedSourceLocalLayerBoundaryAt formation corridor
    hinterior offset
  (pair.sourceSelectedComplementBoundaryProfileData
    formation.annular.cellulation.rotation boundary).regionEdges

/-- Every incoming selected crossing belongs to its literal Cell. -/
theorem pointwiseSelectedSourceLocalLayerCellRegionAt_leftCrossing
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) (step : Fin 2) :
    pointwiseSelectedSourceLocalLayerLeftCrossingAt formation corridor
        hinterior offset step ∈
      pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
        hinterior offset := by
  let layers := pointwiseSelectedSourceLocalLayerPairAt formation corridor
    hinterior offset
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  let boundary := pointwiseSelectedSourceLocalLayerBoundaryAt formation corridor
    hinterior offset
  let cellData := pair.sourceSelectedComplementBoundaryProfileData
    formation.annular.cellulation.rotation boundary
  let index : Fin pair.left.crosscut.walk.length := ⟨step.val, by
    simpa [pair, Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
      Formation.LocalLayerPair.pointwiseSelectedFirstLayer,
      Formation.LocalLayerPair.firstLayer,
      Formation.LocalLayerPair.firstWalk] using step.isLt⟩
  have hport := pair.sourceSelectedComplementBoundaryProfileData_portsInRegion
    formation.annular.cellulation.rotation boundary
    (.inl (pair.sourceSelectedComplementLeftCombinedIndex
      formation.annular.cellulation.rotation boundary index))
  change cellData.crossingEdge
      (pair.sourceSelectedComplementLeftCombinedIndex
        formation.annular.cellulation.rotation boundary index) ∈
    cellData.regionEdges at hport
  rw [pair.sourceSelectedComplementBoundaryProfileData_crossingEdge_left] at hport
  simpa [pointwiseSelectedSourceLocalLayerCellRegionAt,
    pointwiseSelectedSourceLocalLayerLeftCrossingAt, layers, pair, boundary,
    cellData, index] using hport

/-- Every outgoing selected crossing belongs to the same literal Cell. -/
theorem pointwiseSelectedSourceLocalLayerCellRegionAt_rightCrossing
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) (step : Fin 2) :
    pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
        hinterior offset step ∈
      pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
        hinterior offset := by
  let layers := pointwiseSelectedSourceLocalLayerPairAt formation corridor
    hinterior offset
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  let boundary := pointwiseSelectedSourceLocalLayerBoundaryAt formation corridor
    hinterior offset
  let cellData := pair.sourceSelectedComplementBoundaryProfileData
    formation.annular.cellulation.rotation boundary
  let index : Fin pair.left.crosscut.walk.length := ⟨step.val, by
    simpa [pair, Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
      Formation.LocalLayerPair.pointwiseSelectedFirstLayer,
      Formation.LocalLayerPair.firstLayer,
      Formation.LocalLayerPair.firstWalk] using step.isLt⟩
  have hport := pair.sourceSelectedComplementBoundaryProfileData_portsInRegion
    formation.annular.cellulation.rotation boundary
    (.inl (pair.sourceSelectedComplementRightCombinedIndex
      formation.annular.cellulation.rotation boundary index))
  change cellData.crossingEdge
      (pair.sourceSelectedComplementRightCombinedIndex
        formation.annular.cellulation.rotation boundary index) ∈
    cellData.regionEdges at hport
  rw [pair.sourceSelectedComplementBoundaryProfileData_crossingEdge_right] at hport
  have hrightIndex : Fin.cast pair.length_eq index =
      (⟨step.val, by
        simpa [pair, Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
          Formation.LocalLayerPair.pointwiseSelectedSecondLayer,
          Formation.LocalLayerPair.secondLayer,
          Formation.LocalLayerPair.secondWalk] using step.isLt⟩ :
        Fin pair.right.crosscut.walk.length) := by
    apply Fin.ext
    rfl
  rw [hrightIndex] at hport
  simpa [pointwiseSelectedSourceLocalLayerCellRegionAt,
    pointwiseSelectedSourceLocalLayerRightCrossingAt, layers, pair, boundary,
    cellData, index] using hport

/-- Union of the first `cut` pointwise-selected literal Cell regions. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialPrefixRegion
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (cut : Nat) : Finset G.edgeSet :=
  (Finset.univ.filter fun offset : Fin (blockLength - 3) => offset.val < cut)
    |>.biUnion
      (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
        hinterior)

@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialPrefixRegion_zero
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation) :
    pointwiseSelectedSourceLocalLayerSerialPrefixRegion formation corridor
      hinterior 0 = ∅ := by
  ext edge
  simp [pointwiseSelectedSourceLocalLayerSerialPrefixRegion]

/-- Adjoining one in-range position adds exactly its selected literal Cell. -/
theorem pointwiseSelectedSourceLocalLayerSerialPrefixRegion_succ
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength cut : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (hcut : cut < blockLength - 3) :
    pointwiseSelectedSourceLocalLayerSerialPrefixRegion formation corridor
        hinterior (cut + 1) =
      pointwiseSelectedSourceLocalLayerSerialPrefixRegion formation corridor
          hinterior cut ∪
        pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
          hinterior ⟨cut, hcut⟩ := by
  classical
  ext edge
  simp only [pointwiseSelectedSourceLocalLayerSerialPrefixRegion,
    Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union]
  constructor
  · rintro ⟨offset, hoffset, hedge⟩
    by_cases hbefore : offset.val < cut
    · exact Or.inl ⟨offset, hbefore, hedge⟩
    · have heq : offset = (⟨cut, hcut⟩ : Fin (blockLength - 3)) := by
        apply Fin.ext
        exact Nat.le_antisymm (Nat.le_of_lt_succ hoffset)
          (Nat.le_of_not_gt hbefore)
      exact Or.inr (heq ▸ hedge)
  · rintro (⟨offset, hoffset, hedge⟩ | hedge)
    · exact ⟨offset, lt_trans hoffset (Nat.lt_succ_self cut), hedge⟩
    · exact ⟨⟨cut, hcut⟩, Nat.lt_succ_self cut, hedge⟩

/-- Open cumulative input at one moving selected cut. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialInputRegionAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) : Finset G.edgeSet :=
  pointwiseSelectedSourceLocalLayerSerialPrefixRegion formation corridor
      hinterior offset.val ∪
    indexedCrossingEdgeSet
      (pointwiseSelectedSourceLocalLayerLeftCrossingAt formation corridor
        hinterior offset)

/-- Cumulative output after adjoining the indexed selected Cell. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialOutputRegionAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) : Finset G.edgeSet :=
  pointwiseSelectedSourceLocalLayerSerialPrefixRegion formation corridor
    hinterior (offset.val + 1)

theorem pointwiseSelectedSourceLocalLayerSerialInputRegionAt_leftCrossing
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) (step : Fin 2) :
    pointwiseSelectedSourceLocalLayerLeftCrossingAt formation corridor
        hinterior offset step ∈
      pointwiseSelectedSourceLocalLayerSerialInputRegionAt formation corridor
        hinterior offset := by
  apply Finset.mem_union_right
  exact (mem_indexedCrossingEdgeSet_iff _ _).2 ⟨step, rfl⟩

theorem pointwiseSelectedSourceLocalLayerSerialOutputRegionAt_rightCrossing
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) (step : Fin 2) :
    pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
        hinterior offset step ∈
      pointwiseSelectedSourceLocalLayerSerialOutputRegionAt formation corridor
        hinterior offset := by
  rw [pointwiseSelectedSourceLocalLayerSerialOutputRegionAt,
    pointwiseSelectedSourceLocalLayerSerialPrefixRegion_succ formation corridor
      hinterior offset.isLt]
  exact Finset.mem_union_right _
    (pointwiseSelectedSourceLocalLayerCellRegionAt_rightCrossing formation
      corridor hinterior offset step)

/-- The moving input glued to its selected Cell is exactly the cumulative
output region. -/
theorem pointwiseSelectedSourceLocalLayerSerialInputRegionAt_union_cell
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    pointwiseSelectedSourceLocalLayerSerialInputRegionAt formation corridor
          hinterior offset ∪
        pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
          hinterior offset =
      pointwiseSelectedSourceLocalLayerSerialOutputRegionAt formation corridor
        hinterior offset := by
  rw [pointwiseSelectedSourceLocalLayerSerialOutputRegionAt,
    pointwiseSelectedSourceLocalLayerSerialPrefixRegion_succ formation corridor
      hinterior offset.isLt]
  ext edge
  constructor
  · intro hedge
    rcases Finset.mem_union.1 hedge with hinput | hcell
    · rcases Finset.mem_union.1 hinput with hprefix | hcrossing
      · exact Finset.mem_union_left _ hprefix
      · rcases (mem_indexedCrossingEdgeSet_iff _ _).1 hcrossing with
          ⟨step, rfl⟩
        exact Finset.mem_union_right _
          (pointwiseSelectedSourceLocalLayerCellRegionAt_leftCrossing formation
            corridor hinterior offset step)
    · exact Finset.mem_union_right _ hcell
  · intro hedge
    rcases Finset.mem_union.1 hedge with hprefix | hcell
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hprefix)
    · exact Finset.mem_union_right _ hcell

/-- Exact graph-derived cumulative input profile for an arbitrary prefix
colour assignment. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialInputBoundedProfileAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (pointwiseSelectedSourceLocalLayerLeftCrossingAt formation corridor
        hinterior offset step) ≠ 0) :
    BoundedCorridorCutProfile 2 0 4 :=
  regionalBoundaryBoundedProfile formation.annular.RS
    (pointwiseSelectedSourceLocalLayerSerialInputRegionAt formation corridor
      hinterior offset)
    (pointwiseSelectedSourceLocalLayerLeftCrossingAt formation corridor
      hinterior offset) color hcolor

/-- Exact graph-derived cumulative output profile after adjoining one selected
Cell colouring to the prefix. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialOutputBoundedProfileAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
        hinterior offset step) ≠ 0) :
    BoundedCorridorCutProfile 2 0 4 :=
  regionalBoundaryBoundedProfile formation.annular.RS
    (pointwiseSelectedSourceLocalLayerSerialOutputRegionAt formation corridor
      hinterior offset)
    (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
      hinterior offset) color hcolor

end Formation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
