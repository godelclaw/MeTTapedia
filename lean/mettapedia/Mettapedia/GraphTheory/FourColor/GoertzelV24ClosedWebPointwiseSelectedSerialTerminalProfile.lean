import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedSerialPrefixRegion
import Mettapedia.GraphTheory.FourColor.GoertzelV24GraphDerivedTerminalProfile

/-!
# Terminal-aware cumulative prefixes of pointwise-selected Cells

The finite rooted Cell machine remembers the corridor rung consumed by the
next Cell as one explicit terminal of its input state.  After adjoining the
Cell, that rung is an ordinary edge of the cumulative region and the immediate
output is again terminal-free.  This file constructs that exact adapter from
the corrected pointwise rung geometry.

Only annular-interior pairwise uniqueness is used.  In particular, none of the
definitions below depends on the refuted global unique-shared-edge receipt or
on an ambient closed colouring.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24GraphDerivedTerminalProfile
open GoertzelV24HexCorridorPointwiseRungs
open GoertzelV24HexCorridorSkeleton
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedSerialTerminalProfileEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Formation

/-- The pointwise-selected corridor rung retained as the input terminal while
adjoining the Cell at `offset`. -/
noncomputable def pointwiseSelectedSourceLocalLayerSharedRungAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) : G.edgeSet :=
  pointwiseRungEdge
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
    (boundaryCleanCorridor_consecutiveRungUnique formation.annular hinterior
      corridor)
    (pointwiseSelectedSourceLocalLayerInteriorAt offset).outgoing

/-- The cumulative input with the shared rung retained as one terminal edge. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) : Finset G.edgeSet :=
  pointwiseSelectedSourceLocalLayerSerialInputRegionAt formation corridor
      hinterior offset ∪
    {pointwiseSelectedSourceLocalLayerSharedRungAt formation corridor
      hinterior offset}

/-- The terminal-free cumulative output with the consumed rung retained as an
ordinary regional edge, before changing to the successor boundary. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) : Finset G.edgeSet :=
  pointwiseSelectedSourceLocalLayerSerialOutputRegionAt formation corridor
      hinterior offset ∪
    {pointwiseSelectedSourceLocalLayerSharedRungAt formation corridor
      hinterior offset}

/-- Adjoining the selected literal Cell to the terminal-aware predecessor is
exactly the immediate pre-rebase output region. -/
theorem pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt_union_cell
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
          corridor hinterior offset ∪
        pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
          hinterior offset =
      pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
        corridor hinterior offset := by
  rw [pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt,
    pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt]
  rw [Finset.union_assoc, Finset.union_comm
    ({pointwiseSelectedSourceLocalLayerSharedRungAt formation corridor hinterior
      offset} : Finset G.edgeSet),
    ← Finset.union_assoc,
    pointwiseSelectedSourceLocalLayerSerialInputRegionAt_union_cell formation
      corridor hinterior offset]

/-- Terminal-free graph data underlying the terminal-aware input. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialTerminalInputBaseCutDataAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :=
  regionalBoundaryGraphCutData formation.annular.RS
    (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
      corridor hinterior offset)
    (pointwiseSelectedSourceLocalLayerLeftCrossingAt formation corridor
      hinterior offset)

/-- The selected cumulative input cut with the shared rung named as its one
terminal port. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialTerminalInputCutDataAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :=
  withTerminalEdges
    (pointwiseSelectedSourceLocalLayerSerialTerminalInputBaseCutDataAt formation
      corridor hinterior offset)
    (fun _ : Fin 1 =>
      pointwiseSelectedSourceLocalLayerSharedRungAt formation corridor
        hinterior offset)

@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialTerminalInputCutDataAt_regionEdges
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    (pointwiseSelectedSourceLocalLayerSerialTerminalInputCutDataAt formation
      corridor hinterior offset).regionEdges =
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
          corridor hinterior offset :=
  rfl

@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialTerminalInputCutDataAt_crossingEdge
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) (step : Fin 2) :
    (pointwiseSelectedSourceLocalLayerSerialTerminalInputCutDataAt formation
      corridor hinterior offset).crossingEdge step =
        pointwiseSelectedSourceLocalLayerLeftCrossingAt formation corridor
          hinterior offset step :=
  rfl

@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialTerminalInputCutDataAt_terminalEdge
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) (terminal : Fin 1) :
    (pointwiseSelectedSourceLocalLayerSerialTerminalInputCutDataAt formation
      corridor hinterior offset).terminalEdge terminal =
        pointwiseSelectedSourceLocalLayerSharedRungAt formation corridor
          hinterior offset :=
  rfl

/-- Every displayed crossing and the one terminal are genuine input-region
edges. -/
theorem pointwiseSelectedSourceLocalLayerSerialTerminalInputCutDataAt_portsInRegion
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    (pointwiseSelectedSourceLocalLayerSerialTerminalInputCutDataAt formation
      corridor hinterior offset).PortsInRegion := by
  rw [pointwiseSelectedSourceLocalLayerSerialTerminalInputCutDataAt,
    withTerminalEdges_portsInRegion_iff]
  constructor
  · apply regionalBoundaryGraphCutData_portsInRegion
    intro step
    exact Finset.mem_union_left _
      (pointwiseSelectedSourceLocalLayerSerialInputRegionAt_leftCrossing
        formation corridor hinterior offset step)
  · intro terminal
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

/-- Terminal augmentation preserves the exact occurrence-sensitive regional
face fragments. -/
theorem pointwiseSelectedSourceLocalLayerSerialTerminalInputCutDataAt_fragmentsOnFaceInRegion
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    (pointwiseSelectedSourceLocalLayerSerialTerminalInputCutDataAt formation
      corridor hinterior offset).FragmentsOnFaceInRegion := by
  rw [pointwiseSelectedSourceLocalLayerSerialTerminalInputCutDataAt,
    withTerminalEdges_fragmentsOnFaceInRegion_iff]
  exact regionalBoundaryGraphCutData_fragmentsOnFaceInRegion
    formation.annular.RS
    (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
      corridor hinterior offset)
    (pointwiseSelectedSourceLocalLayerLeftCrossingAt formation corridor
      hinterior offset)

/-- Complete selected terminal-aware cumulative input profile for an arbitrary
open-region colour assignment. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialTerminalInputBoundedProfileAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color)
    (hcrossing : ∀ step,
      color (pointwiseSelectedSourceLocalLayerLeftCrossingAt formation corridor
        hinterior offset step) ≠ 0) :
    BoundedCorridorCutProfile 2 1 4 where
  faceFragmentCount :=
    ⟨Fintype.card (BoundaryRegionalFragment formation.annular.RS
        (indexedCrossingEdgeSet
          (pointwiseSelectedSourceLocalLayerLeftCrossingAt formation corridor
            hinterior offset))
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
          corridor hinterior offset)),
      Nat.lt_succ_of_le
        (regionalBoundaryGraphCutData_fragmentCount_le_two_mul
          formation.annular.RS
          (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
            corridor hinterior offset)
          (pointwiseSelectedSourceLocalLayerLeftCrossingAt formation corridor
            hinterior offset))⟩
  profile :=
    (pointwiseSelectedSourceLocalLayerSerialTerminalInputCutDataAt formation
      corridor hinterior offset).regionalProfile color hcrossing

/-- Complete terminal-free immediate output profile before boundary rebase. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputBoundedProfileAt
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
    (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
      corridor hinterior offset)
    (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
      hinterior offset) color hcolor

end Formation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
