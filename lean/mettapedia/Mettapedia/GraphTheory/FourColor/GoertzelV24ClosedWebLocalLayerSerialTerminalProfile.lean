import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialPrefixRegion
import Mettapedia.GraphTheory.FourColor.GoertzelV24GraphDerivedTerminalProfile

/-!
# Terminal-aware actual source prefixes

The cumulative source prefix meets the next literal Cell along one canonical
corridor rung.  This file retains that rung as an explicit terminal of the
incoming profile and as an ordinary regional edge after adjoining the Cell.
The intermediate seam state is kept visible: no theorem here assumes that the
rung was already redundant in the unaugmented cumulative region.

The resulting input has type `BoundedCorridorCutProfile 2 1 4`; the immediate
pre-rebase output has type `BoundedCorridorCutProfile 2 0 4`.  The exact union
identity is proved.  Identifying the pre-rebase output with the next indexed
input is the separate boundary-rebase obligation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularCrosscut
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24GraphDerivedTerminalProfile
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialTerminalProfileEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The one corridor rung retained as the seam terminal while adjoining the
indexed literal Cell. -/
noncomputable def sourceLocalLayerSharedRungAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) : G.edgeSet :=
  corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
    |>.rungEdge hunique (sourceLocalLayerInteriorAt offset).outgoing

/-- The actual predecessor region with its shared rung explicitly retained as
one seam terminal. -/
noncomputable def sourceLocalLayerSerialTerminalInputRegionAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) : Finset G.edgeSet :=
  sourceLocalLayerSerialInputRegionAt corridor hunique offset ∪
    {sourceLocalLayerSharedRungAt corridor hunique offset}

/-- The immediate successor before the boundary rebase: the cumulative output
with the just-consumed seam rung retained as an ordinary regional edge. -/
noncomputable def sourceLocalLayerSerialPreRebaseOutputRegionAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) : Finset G.edgeSet :=
  sourceLocalLayerSerialOutputRegionAt corridor hunique offset ∪
    {sourceLocalLayerSharedRungAt corridor hunique offset}

/-- Adjoining the literal Cell to the terminal-aware predecessor gives exactly
the pre-rebase successor region. -/
theorem sourceLocalLayerSerialTerminalInputRegionAt_union_cell
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset ∪
        sourceLocalLayerCellRegionAt corridor hunique offset =
      sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset := by
  rw [sourceLocalLayerSerialTerminalInputRegionAt,
    sourceLocalLayerSerialPreRebaseOutputRegionAt]
  rw [Finset.union_assoc, Finset.union_comm
    ({sourceLocalLayerSharedRungAt corridor hunique offset} : Finset G.edgeSet),
    ← Finset.union_assoc,
    sourceLocalLayerSerialInputRegionAt_union_cell corridor hunique offset]

/-- Zero-terminal graph data on the seam-augmented predecessor region. -/
noncomputable def sourceLocalLayerSerialTerminalInputBaseCutDataAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :=
  regionalBoundaryGraphCutData web.annular.RS
    (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
    (sourceLocalLayerLeftCrossingAt corridor hunique offset)

/-- The same predecessor cut with the shared rung named as its single terminal
port. -/
noncomputable def sourceLocalLayerSerialTerminalInputCutDataAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :=
  withTerminalEdges
    (sourceLocalLayerSerialTerminalInputBaseCutDataAt corridor hunique offset)
    (fun _ : Fin 1 => sourceLocalLayerSharedRungAt corridor hunique offset)

@[simp]
theorem sourceLocalLayerSerialTerminalInputCutDataAt_regionEdges
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    (sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique offset).regionEdges =
      sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset :=
  rfl

@[simp]
theorem sourceLocalLayerSerialTerminalInputCutDataAt_crossingEdge
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (step : Fin 2) :
    (sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique offset).crossingEdge step =
      sourceLocalLayerLeftCrossingAt corridor hunique offset step :=
  rfl

@[simp]
theorem sourceLocalLayerSerialTerminalInputCutDataAt_terminalEdge
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (terminal : Fin 1) :
    (sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique offset).terminalEdge terminal =
      sourceLocalLayerSharedRungAt corridor hunique offset :=
  rfl

/-- Every named crossing and the explicit seam terminal genuinely belongs to
the augmented predecessor region. -/
theorem sourceLocalLayerSerialTerminalInputCutDataAt_portsInRegion
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    (sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique offset)
      |>.PortsInRegion := by
  rw [sourceLocalLayerSerialTerminalInputCutDataAt,
    withTerminalEdges_portsInRegion_iff]
  constructor
  · apply regionalBoundaryGraphCutData_portsInRegion
    intro step
    exact Finset.mem_union_left _
      (sourceLocalLayerSerialInputRegionAt_leftCrossing corridor hunique offset step)
  · intro terminal
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

/-- Terminal augmentation retains the occurrence-sensitive facial fragments
computed from the actual augmented predecessor region. -/
theorem sourceLocalLayerSerialTerminalInputCutDataAt_fragmentsOnFaceInRegion
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    (sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique offset)
      |>.FragmentsOnFaceInRegion := by
  rw [sourceLocalLayerSerialTerminalInputCutDataAt,
    withTerminalEdges_fragmentsOnFaceInRegion_iff]
  exact regionalBoundaryGraphCutData_fragmentsOnFaceInRegion
    web.annular.RS
    (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
    (sourceLocalLayerLeftCrossingAt corridor hunique offset)

/-- The complete terminal-aware predecessor profile on the actual opened
source carrier.  Its four-fragment bound depends only on the two displayed
crossings; the seam terminal does not enlarge the cut. -/
noncomputable def sourceLocalLayerSerialTerminalInputBoundedProfileAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    BoundedCorridorCutProfile 2 1 4 where
  faceFragmentCount :=
    ⟨Fintype.card (BoundaryRegionalFragment web.annular.RS
        (indexedCrossingEdgeSet
          (sourceLocalLayerLeftCrossingAt corridor hunique offset))
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)),
      Nat.lt_succ_of_le
        (regionalBoundaryGraphCutData_fragmentCount_le_two_mul web.annular.RS
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
          (sourceLocalLayerLeftCrossingAt corridor hunique offset))⟩
  profile :=
    (sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique offset)
      |>.regionalProfile coloring (fun _ => web.tait _)

/-- The complete zero-terminal profile immediately after adjoining the Cell
and before changing to the successor seam. -/
noncomputable def sourceLocalLayerSerialPreRebaseOutputBoundedProfileAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    BoundedCorridorCutProfile 2 0 4 :=
  regionalBoundaryBoundedProfile web.annular.RS
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    (sourceLocalLayerRightCrossingAt corridor hunique offset) coloring
    (fun _ => web.tait _)

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
