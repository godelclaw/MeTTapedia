import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedSerialTerminalProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24RegionalProfileColorCongruence

/-!
# Compatible cumulative-prefix and selected Cell Count witnesses

A positive entry of the literal selected-Cell `Count` supplies its own open
Cell colouring.  A cumulative prefix may carry a different colouring.  This
file performs the exact source composition: use the Cell colouring on the
literal Cell and the prefix colouring elsewhere, under explicit agreement on
their actual finite overlap.

The construction uses only the pointwise-selected boundary and the restricted
annular interior-face uniqueness receipt.  In particular, it does not recover
the refuted global unique-shared-edge hypothesis.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexCorridorSkeleton
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SelectedDualPathTransversal
open GoertzelV24SelectedDualPathTransversal.SeparatedAlignedSelectedDualTransversals
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedSerialCellCountWitnessEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Formation

open LocalLayerPair

/-- Literal open Tait colourings of the canonical pointwise-selected Cell at
one corridor offset. -/
abbrev PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :=
  let layers := pointwiseSelectedSourceLocalLayerPairAt formation corridor
    hinterior offset
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  let boundary := pointwiseSelectedSourceLocalLayerBoundaryAt formation corridor
    hinterior offset
  pair.SourceSelectedComplementLiteralOpenTaitColoring
    formation.annular.cellulation.rotation boundary

/-- Extend a literal selected-Cell colouring to the ambient edge carrier,
returning zero away from the Cell. -/
noncomputable def pointwiseSelectedSourceLocalLayerCellLiteralColorAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt formation
        corridor hinterior offset) : G.edgeSet → Color :=
  let layers := pointwiseSelectedSourceLocalLayerPairAt formation corridor
    hinterior offset
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  let boundary := pointwiseSelectedSourceLocalLayerBoundaryAt formation corridor
    hinterior offset
  pair.sourceSelectedComplementColor formation.annular.cellulation.rotation
    boundary cellColoring.1

/-- Every retained Cell edge receives a nonzero colour from a literal Count
witness. -/
theorem pointwiseSelectedSourceLocalLayerCellLiteralColorAt_ne_zero_of_mem
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt formation
        corridor hinterior offset)
    {edge : G.edgeSet}
    (hedge : edge ∈ pointwiseSelectedSourceLocalLayerCellRegionAt formation
      corridor hinterior offset) :
    pointwiseSelectedSourceLocalLayerCellLiteralColorAt formation corridor
        hinterior offset cellColoring edge ≠ 0 := by
  let layers := pointwiseSelectedSourceLocalLayerPairAt formation corridor
    hinterior offset
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  let boundary := pointwiseSelectedSourceLocalLayerBoundaryAt formation corridor
    hinterior offset
  apply pair.sourceSelectedComplementColor_ne_zero
    formation.annular.cellulation.rotation boundary cellColoring.1
      cellColoring.2
  have hregion : edge ∈ vertexSetRegionEdges
      formation.annular.cellulation.rotation.toRotationSystem
      (pair.componentSide boundary.component)ᶜ := by
    simpa only [pointwiseSelectedSourceLocalLayerCellRegionAt,
      sourceSelectedComplementBoundaryProfileData,
      vertexSetBoundaryGraphCutDataWithIndexing] using hedge
  exact hregion

/-- In particular, both outgoing crossings of a positive Count witness are
nonzero. -/
theorem pointwiseSelectedSourceLocalLayerCellLiteralColorAt_rightCrossing_ne_zero
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt formation
        corridor hinterior offset)
    (step : Fin 2) :
    pointwiseSelectedSourceLocalLayerCellLiteralColorAt formation corridor
        hinterior offset cellColoring
        (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
          hinterior offset step) ≠ 0 :=
  pointwiseSelectedSourceLocalLayerCellLiteralColorAt_ne_zero_of_mem formation
    corridor hinterior offset cellColoring
      (pointwiseSelectedSourceLocalLayerCellRegionAt_rightCrossing formation
        corridor hinterior offset step)

/-- Prefix and Cell colours agree on precisely the retained edges shared by
the cumulative input and the literal Cell. -/
def PointwiseSelectedSourceLocalLayerSerialCellColorsCompatibleAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (prefixColor cellColor : G.edgeSet → Color) : Prop :=
  ∀ edge,
    edge ∈ pointwiseSelectedSourceLocalLayerSerialInputRegionAt formation
        corridor hinterior offset →
    edge ∈ pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
        hinterior offset →
      prefixColor edge = cellColor edge

/-- Compatibility on the actual terminal-aware input.  This is the receipt
consumed by the rooted Cell machine: it additionally covers the retained
shared rung when that rung belongs to the literal Cell. -/
def PointwiseSelectedSourceLocalLayerSerialTerminalCellColorsCompatibleAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (prefixColor cellColor : G.edgeSet → Color) : Prop :=
  ∀ edge,
    edge ∈ pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
        formation corridor hinterior offset →
    edge ∈ pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
        hinterior offset →
      prefixColor edge = cellColor edge

theorem pointwiseSelectedSourceLocalLayerSerialTerminalCellColorsCompatibleAt_to_input
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (prefixColor cellColor : G.edgeSet → Color)
    (hcompatible :
      PointwiseSelectedSourceLocalLayerSerialTerminalCellColorsCompatibleAt
        formation corridor hinterior offset prefixColor cellColor) :
    PointwiseSelectedSourceLocalLayerSerialCellColorsCompatibleAt formation
      corridor hinterior offset prefixColor cellColor := by
  intro edge hinput hcell
  exact hcompatible edge (Finset.mem_union_left _ hinput) hcell

/-- Use the literal Count witness on the new Cell and the arbitrary prefix
colouring everywhere else. -/
def pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (prefixColor cellColor : G.edgeSet → Color) : G.edgeSet → Color :=
  fun edge =>
    if edge ∈ pointwiseSelectedSourceLocalLayerCellRegionAt formation
        corridor hinterior offset then
      cellColor edge
    else
      prefixColor edge

theorem pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_eq_cell_of_mem
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (prefixColor cellColor : G.edgeSet → Color) {edge : G.edgeSet}
    (hedge : edge ∈ pointwiseSelectedSourceLocalLayerCellRegionAt formation
      corridor hinterior offset) :
    pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt formation corridor
        hinterior offset prefixColor cellColor edge = cellColor edge := by
  simp [pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt, hedge]

theorem pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_eq_prefix_of_mem
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (prefixColor cellColor : G.edgeSet → Color)
    (hcompatible :
      PointwiseSelectedSourceLocalLayerSerialCellColorsCompatibleAt formation
        corridor hinterior offset prefixColor cellColor)
    {edge : G.edgeSet}
    (hedge : edge ∈ pointwiseSelectedSourceLocalLayerSerialInputRegionAt
      formation corridor hinterior offset) :
    pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt formation corridor
        hinterior offset prefixColor cellColor edge = prefixColor edge := by
  by_cases hcell : edge ∈
      pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
        hinterior offset
  · rw [pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_eq_cell_of_mem
      formation corridor hinterior offset prefixColor cellColor hcell]
    exact (hcompatible edge hedge hcell).symm
  · simp [pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt, hcell]

/-- Under terminal-aware compatibility, splicing preserves every edge colour
read by the rooted input state, including its retained rung. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_eq_prefix_of_mem_terminalInput
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (prefixColor cellColor : G.edgeSet → Color)
    (hcompatible :
      PointwiseSelectedSourceLocalLayerSerialTerminalCellColorsCompatibleAt
        formation corridor hinterior offset prefixColor cellColor)
    {edge : G.edgeSet}
    (hedge : edge ∈
      pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
        corridor hinterior offset) :
    pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt formation corridor
        hinterior offset prefixColor cellColor edge = prefixColor edge := by
  by_cases hcell : edge ∈
      pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
        hinterior offset
  · rw [pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_eq_cell_of_mem
      formation corridor hinterior offset prefixColor cellColor hcell]
    exact (hcompatible edge hedge hcell).symm
  · simp [pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt, hcell]

/-- Compatibility preserves the entire five-coordinate cumulative input
profile, not merely its displayed colour word. -/
theorem pointwiseSelectedSourceLocalLayerSerialInputBoundedProfileAt_spliced
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (prefixColor cellColor : G.edgeSet → Color)
    (hprefix : ∀ step,
      prefixColor (pointwiseSelectedSourceLocalLayerLeftCrossingAt formation
        corridor hinterior offset step) ≠ 0)
    (hcompatible :
      PointwiseSelectedSourceLocalLayerSerialCellColorsCompatibleAt formation
        corridor hinterior offset prefixColor cellColor) :
    pointwiseSelectedSourceLocalLayerSerialInputBoundedProfileAt formation
        corridor hinterior offset
        (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt formation
          corridor hinterior offset prefixColor cellColor)
        (fun step => by
          rw [pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_eq_prefix_of_mem
            formation corridor hinterior offset prefixColor cellColor
              hcompatible
              (pointwiseSelectedSourceLocalLayerSerialInputRegionAt_leftCrossing
                formation corridor hinterior offset step)]
          exact hprefix step) =
      pointwiseSelectedSourceLocalLayerSerialInputBoundedProfileAt formation
        corridor hinterior offset prefixColor hprefix := by
  unfold pointwiseSelectedSourceLocalLayerSerialInputBoundedProfileAt
  unfold regionalBoundaryBoundedProfile
  congr 1
  apply GraphCorridorCutData.regionalProfile_eq_of_eq_on_region
  · apply regionalBoundaryGraphCutData_portsInRegion
    exact pointwiseSelectedSourceLocalLayerSerialInputRegionAt_leftCrossing
      formation corridor hinterior offset
  · intro edge hedge
    exact pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_eq_prefix_of_mem
      formation corridor hinterior offset prefixColor cellColor hcompatible
        hedge

/-- Compatibility preserves the complete terminal-aware rooted input profile.
The proof is local to the exact input edge region, so all five stored profile
coordinates are preserved at once. -/
theorem pointwiseSelectedSourceLocalLayerSerialTerminalInputBoundedProfileAt_spliced
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (prefixColor cellColor : G.edgeSet → Color)
    (hprefix : ∀ step,
      prefixColor (pointwiseSelectedSourceLocalLayerLeftCrossingAt formation
        corridor hinterior offset step) ≠ 0)
    (hcompatible :
      PointwiseSelectedSourceLocalLayerSerialTerminalCellColorsCompatibleAt
        formation corridor hinterior offset prefixColor cellColor) :
    pointwiseSelectedSourceLocalLayerSerialTerminalInputBoundedProfileAt
        formation corridor hinterior offset
        (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt formation
          corridor hinterior offset prefixColor cellColor)
        (fun step => by
          rw [pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_eq_prefix_of_mem_terminalInput
            formation corridor hinterior offset prefixColor cellColor
              hcompatible
              (Finset.mem_union_left _
                (pointwiseSelectedSourceLocalLayerSerialInputRegionAt_leftCrossing
                  formation corridor hinterior offset step))]
          exact hprefix step) =
      pointwiseSelectedSourceLocalLayerSerialTerminalInputBoundedProfileAt
        formation corridor hinterior offset prefixColor hprefix := by
  unfold pointwiseSelectedSourceLocalLayerSerialTerminalInputBoundedProfileAt
  congr 1
  apply GraphCorridorCutData.regionalProfile_eq_of_eq_on_region
  · exact
      pointwiseSelectedSourceLocalLayerSerialTerminalInputCutDataAt_portsInRegion
        formation corridor hinterior offset
  · intro edge hedge
    exact pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_eq_prefix_of_mem_terminalInput
      formation corridor hinterior offset prefixColor cellColor hcompatible
        hedge

/-- Exact cumulative output profile formed after adjoining the positive-Count
Cell witness to a compatible arbitrary prefix. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialSplicedOutputBoundedProfileAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (prefixColor : G.edgeSet → Color)
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt formation
        corridor hinterior offset) :
    BoundedCorridorCutProfile 2 0 4 :=
  pointwiseSelectedSourceLocalLayerSerialOutputBoundedProfileAt formation
    corridor hinterior offset
    (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt formation
      corridor hinterior offset prefixColor
      (pointwiseSelectedSourceLocalLayerCellLiteralColorAt formation corridor
        hinterior offset cellColoring))
    (fun step => by
      rw [pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_eq_cell_of_mem
        formation corridor hinterior offset]
      · exact
          pointwiseSelectedSourceLocalLayerCellLiteralColorAt_rightCrossing_ne_zero
            formation corridor hinterior offset cellColoring step
      · exact pointwiseSelectedSourceLocalLayerCellRegionAt_rightCrossing
          formation corridor hinterior offset step)

/-- The exact immediate pre-rebase output after adjoining a positive selected
Cell witness to a cumulative prefix.  The consumed terminal is now an ordinary
regional edge. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialSplicedPreRebaseOutputBoundedProfileAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (prefixColor : G.edgeSet → Color)
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt formation
        corridor hinterior offset) :
    BoundedCorridorCutProfile 2 0 4 :=
  pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputBoundedProfileAt
    formation corridor hinterior offset
    (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt formation
      corridor hinterior offset prefixColor
      (pointwiseSelectedSourceLocalLayerCellLiteralColorAt formation corridor
        hinterior offset cellColoring))
    (fun step => by
      rw [pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_eq_cell_of_mem
        formation corridor hinterior offset]
      · exact
          pointwiseSelectedSourceLocalLayerCellLiteralColorAt_rightCrossing_ne_zero
            formation corridor hinterior offset cellColoring step
      · exact pointwiseSelectedSourceLocalLayerCellRegionAt_rightCrossing
          formation corridor hinterior offset step)

/-- The finite selected-Cell transfer relation has exactly the expected
concrete source witness, even for arbitrary elements of its bounded carrier. -/
theorem pointwiseSelectedSourceLocalLayerCellBoundedProfileTransfer_iff_exists_coloring
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (left right : PointwiseSelectedSourceLocalLayerCellBoundedProfile) :
    let layers := pointwiseSelectedSourceLocalLayerPairAt formation corridor
      hinterior offset
    layers.pointwiseSelectedSourceLocalLayerCellBoundedProfileTransfer
        hinterior left right ↔
      ∃ leftRaw rightRaw :
          PointwiseSelectedSourceLocalLayerCellProfile hinterior layers,
        layers.pointwiseSelectedSourceLocalLayerCellProfileCode hinterior
            leftRaw = left ∧
          layers.pointwiseSelectedSourceLocalLayerCellProfileCode hinterior
              rightRaw = right ∧
          ∃ cellColoring :
              PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt
                formation corridor hinterior offset,
            let pair := layers.pointwiseSelectedLocalLayerPair hinterior
            let boundary :=
              pointwiseSelectedSourceLocalLayerBoundaryAt formation corridor
                hinterior offset
            pair.sourceSelectedComplementLiteralOpenLeftProfile
                formation.annular.cellulation.rotation boundary cellColoring.1
                  cellColoring.2 = leftRaw ∧
              pair.sourceSelectedComplementLiteralOpenRightProfile
                formation.annular.cellulation.rotation boundary cellColoring.1
                  cellColoring.2 = rightRaw := by
  dsimp only
  constructor
  · rintro ⟨leftRaw, rightRaw, hleftCode, hrightCode, hpositive⟩
    let layers := pointwiseSelectedSourceLocalLayerPairAt formation corridor
      hinterior offset
    let pair := layers.pointwiseSelectedLocalLayerPair hinterior
    let boundary := pointwiseSelectedSourceLocalLayerBoundaryAt formation corridor
      hinterior offset
    rcases (pair.sourceSelectedComplementLiteralOpenProfileCount_pos_iff
      formation.annular.cellulation.rotation boundary leftRaw rightRaw).1
        hpositive with ⟨cellColoring, hleft, hright⟩
    exact ⟨leftRaw, rightRaw, hleftCode, hrightCode, cellColoring, hleft,
      hright⟩
  · rintro ⟨leftRaw, rightRaw, hleftCode, hrightCode, cellColoring,
      hleft, hright⟩
    refine ⟨leftRaw, rightRaw, hleftCode, hrightCode, ?_⟩
    let layers := pointwiseSelectedSourceLocalLayerPairAt formation corridor
      hinterior offset
    let pair := layers.pointwiseSelectedLocalLayerPair hinterior
    let boundary := pointwiseSelectedSourceLocalLayerBoundaryAt formation corridor
      hinterior offset
    exact (pair.sourceSelectedComplementLiteralOpenProfileCount_pos_iff
      formation.annular.cellulation.rotation boundary leftRaw rightRaw).2
        ⟨cellColoring, hleft, hright⟩

end Formation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
