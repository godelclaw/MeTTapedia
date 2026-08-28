import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseCarrierTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedBoundaryRebaseSuccessor
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedCellPastOverlap
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFiniteTrackedColorCode

/-!
# Exact colour-coordinate transport on the selected rolling carrier

The selected cumulative carrier uses twenty-one stable slots, but consecutive
cuts enumerate different literal edge sets.  This file supplies the exact
finite change of coordinates.  Every target slot is decoded either as one of
the four boundary-rebase roles or as a slot of the present selected carrier.

The pointwise-selected geometry proves the required coverage unconditionally:
every active target edge is a rebase edge or belongs to the present literal
Cell.  Consequently the finite transport agrees exactly with the canonical
colour table of the next cumulative prefix.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedCarrierTransport

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteTrackedColorCode
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseCarrierTransport
open GoertzelV24ClosedWebPointwiseSelectedCellPastOverlap
open GoertzelV24CorridorProfile
open GoertzelV24FacialPentagonCap
open GoertzelV24HexCorridorFiniteColorTransition
open GoertzelV24MinimalFacialPentagonCapPairPointwiseSelectedLocalCellCarrier
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedCarrierTransportOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- Decode a next-carrier slot into either a present stable slot or one of the
four boundary-rebase roles.  Roles take precedence because their regional
activity can change during the rebase. -/
noncomputable def
    pointwiseSelectedSourceLocalLayerSerialCellRebaseCarrierSourceAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card <= 6) :
    Fin 21 -> Option SourceLocalLayerSerialCellRebaseCarrierSource :=
  fun targetSlot =>
    (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionEdgeAtSlot?
      web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext) targetSlot).bind fun targetEdge =>
      if hrole : exists role : SourceLocalLayerBoundaryRebaseRole,
          pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt web.toFormation
            corridor hinterior offset hnext role = targetEdge.1 then
        some (Sum.inr (Classical.choose hrole))
      else if hcurrent : targetEdge.1 ∈
          pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
            web.toFormation corridor hinterior offset then
        some (Sum.inl
          (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionSlotAt web
            corridor hinterior offset hcell ⟨targetEdge.1, hcurrent⟩))
      else none

/-- The source decoder evaluates literally at every represented target edge. -/
theorem
    pointwiseSelectedSourceLocalLayerSerialCellRebaseCarrierSourceAt_targetSlot
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card <= 6)
    (hcellNext :
      (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior (sourceLocalLayerNextOffset offset hnext)).card <= 6)
    (targetEdge : {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)}) :
    pointwiseSelectedSourceLocalLayerSerialCellRebaseCarrierSourceAt web
        corridor hinterior offset hnext hcell
        (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionSlotAt web
          corridor hinterior (sourceLocalLayerNextOffset offset hnext)
            hcellNext targetEdge) =
      if hrole : exists role : SourceLocalLayerBoundaryRebaseRole,
          pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt web.toFormation
            corridor hinterior offset hnext role = targetEdge.1 then
        some (Sum.inr (Classical.choose hrole))
      else if hcurrent : targetEdge.1 ∈
          pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
            web.toFormation corridor hinterior offset then
        some (Sum.inl
          (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionSlotAt web
            corridor hinterior offset hcell ⟨targetEdge.1, hcurrent⟩))
      else none := by
  unfold pointwiseSelectedSourceLocalLayerSerialCellRebaseCarrierSourceAt
  rw [pointwiseSelectedSourceLocalLayerSerialTrackedTransitionEdgeAtSlot?_slot]
  rfl

/-- Finite post-Cell colour data transported onto the next selected carrier. -/
noncomputable def
    pointwiseSelectedSourceLocalLayerSerialCellRebaseTransportedColorCodeForColorAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card <= 6)
    (prefixColor cellColor : G.edgeSet -> Color)
    (hrole : forall role,
      pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt web.toFormation
          corridor hinterior offset prefixColor cellColor
          (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt web.toFormation
            corridor hinterior offset hnext role) ≠ 0) :
    GoertzelV24ClosedWebLocalLayerSerialCellFiniteColorCompatibility.SourceLocalLayerSerialCarrierColorCode :=
  let splice :=
    pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt web.toFormation
      corridor hinterior offset prefixColor cellColor
  SourceLocalLayerSerialCellRebaseTransportedColorCode
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseCarrierSourceAt web
      corridor hinterior offset hnext hcell)
    (SourceLocalLayerSerialFiniteSplicedColor
      (pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt web.toFormation
        corridor hinterior offset
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
          web.toFormation corridor hinterior offset) prefixColor)
      (pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt web.toFormation
        corridor hinterior offset
        (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
          hinterior offset) cellColor))
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt
      web.toFormation corridor hinterior offset hnext splice hrole)

/-- The finite selected transport is exactly the canonical colour table on the
next rolling carrier.  Coverage is discharged by selected Cell locality, not
carried as an additional receipt. -/
theorem
    pointwiseSelectedSourceLocalLayerSerialCellRebaseTransportedColorCodeForColorAt_eq_target
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (prefixColor cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hrole : ∀ role,
      pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt web.toFormation
          corridor hinterior offset prefixColor cellColor
          (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt web.toFormation
            corridor hinterior offset hnext role) ≠ 0) :
    pointwiseSelectedSourceLocalLayerSerialCellRebaseTransportedColorCodeForColorAt
        web corridor hinterior offset hnext hcell prefixColor cellColor hrole =
      pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt web.toFormation
        corridor hinterior (sourceLocalLayerNextOffset offset hnext)
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
          web.toFormation corridor hinterior
            (sourceLocalLayerNextOffset offset hnext))
        (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt web.toFormation
          corridor hinterior offset prefixColor cellColor) := by
  classical
  funext targetSlot
  let splice :=
    pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt web.toFormation
      corridor hinterior offset prefixColor cellColor
  cases hdecode :
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionEdgeAtSlot?
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext) targetSlot with
  | none =>
      unfold
        pointwiseSelectedSourceLocalLayerSerialCellRebaseTransportedColorCodeForColorAt
        SourceLocalLayerSerialCellRebaseTransportedColorCode
        pointwiseSelectedSourceLocalLayerSerialCellRebaseCarrierSourceAt
        pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt
      rw [hdecode]
      rfl
  | some targetEdge =>
      unfold
        pointwiseSelectedSourceLocalLayerSerialCellRebaseTransportedColorCodeForColorAt
        SourceLocalLayerSerialCellRebaseTransportedColorCode
        pointwiseSelectedSourceLocalLayerSerialCellRebaseCarrierSourceAt
        pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt
      rw [hdecode]
      simp only [Option.bind_some]
      by_cases hroleEdge : ∃ role : SourceLocalLayerBoundaryRebaseRole,
          pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt web.toFormation
            corridor hinterior offset hnext role = targetEdge.1
      · rw [dif_pos hroleEdge]
        let role := Classical.choose hroleEdge
        have hedge := Classical.choose_spec hroleEdge
        change (if
            (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt
              web.toFormation corridor hinterior offset hnext splice hrole
            ).roleInRegion role then
              some
                ((pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt
                  web.toFormation corridor hinterior offset hnext splice hrole
                ).roleColor role).toColor
            else none) = _
        unfold
          pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt
        dsimp only [SourceLocalLayerBoundaryRebaseTrackedState.roleInRegion,
          SourceLocalLayerBoundaryRebaseTrackedState.roleColor]
        have hmemIff :
            pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt web.toFormation
                corridor hinterior offset hnext role ∈
              pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
                web.toFormation corridor hinterior
                  (sourceLocalLayerNextOffset offset hnext) ↔
            targetEdge.1 ∈
              pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
                web.toFormation corridor hinterior
                  (sourceLocalLayerNextOffset offset hnext) := by
          rw [hedge]
        by_cases hmem : targetEdge.1 ∈
            pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
              web.toFormation corridor hinterior
                (sourceLocalLayerNextOffset offset hnext)
        · have hmemRole := hmemIff.mpr hmem
          have hcondition : decide
              (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt
                  web.toFormation corridor hinterior offset hnext role ∈
                pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
                  web.toFormation corridor hinterior
                    (sourceLocalLayerNextOffset offset hnext)) = true := by
            simp [hmemRole]
          rw [if_pos hcondition, if_pos hmem, strandColorOfNonzero_toColor]
          exact congrArg some (congrArg splice hedge)
        · have hmemRole :
              pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt
                  web.toFormation corridor hinterior offset hnext role ∉
                pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
                  web.toFormation corridor hinterior
                    (sourceLocalLayerNextOffset offset hnext) :=
            fun h => hmem (hmemIff.mp h)
          have hcondition : ¬ decide
              (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt
                  web.toFormation corridor hinterior offset hnext role ∈
                pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
                  web.toFormation corridor hinterior
                    (sourceLocalLayerNextOffset offset hnext)) = true := by
            simp [hmemRole]
          rw [if_neg hcondition, if_neg hmem]
      · rw [dif_neg hroleEdge]
        by_cases hcurrent : targetEdge.1 ∈
            pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
              web.toFormation corridor hinterior offset
        · rw [dif_pos hcurrent]
          change SourceLocalLayerSerialFiniteSplicedColor
              (pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt
                web.toFormation corridor hinterior offset
                (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
                  web.toFormation corridor hinterior offset) prefixColor)
              (pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt
                web.toFormation corridor hinterior offset
                (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
                  corridor hinterior offset) cellColor)
              (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionSlotAt
                web corridor hinterior offset hcell
                  ⟨targetEdge.1, hcurrent⟩) =
            if targetEdge.1 ∈
                pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
                  web.toFormation corridor hinterior
                    (sourceLocalLayerNextOffset offset hnext) then
              some (splice targetEdge.1)
            else none
          rw [pointwiseSelectedSourceLocalLayerSerialFiniteSplicedColorForColorAt_codeAt_slot]
          have hnotSwitch : targetEdge.1 ∉
              pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt
                web.toFormation corridor hinterior offset hnext := by
            rw [mem_pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_iff]
            exact hroleEdge
          have hregion :=
            pointwiseSelectedSourceLocalLayerSerialPreRebaseOutput_mem_iff_nextTerminalInput_of_not_mem_switch
              web.toFormation corridor hinterior offset hnext targetEdge.1
                hnotSwitch
          by_cases hcellMem : targetEdge.1 ∈
              pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
                corridor hinterior offset
          · have hpre : targetEdge.1 ∈
                pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt
                  web.toFormation corridor hinterior offset := by
              rw [←
                pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt_union_cell
                  web.toFormation corridor hinterior offset]
              exact Finset.mem_union_right _ hcellMem
            have htarget := hregion.1 hpre
            simp [hcellMem, htarget, splice,
              pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt]
          · by_cases hprefixMem : targetEdge.1 ∈
                pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
                  web.toFormation corridor hinterior offset
            · have hpre : targetEdge.1 ∈
                  pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt
                    web.toFormation corridor hinterior offset := by
                rw [←
                  pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt_union_cell
                    web.toFormation corridor hinterior offset]
                exact Finset.mem_union_left _ hprefixMem
              have htarget := hregion.1 hpre
              simp [hcellMem, hprefixMem, htarget, splice,
                pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt]
            · have hpre : targetEdge.1 ∉
                  pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt
                    web.toFormation corridor hinterior offset := by
                rw [←
                  pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt_union_cell
                    web.toFormation corridor hinterior offset]
                simp [hcellMem, hprefixMem]
              have htarget : targetEdge.1 ∉
                  pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
                    web.toFormation corridor hinterior
                      (sourceLocalLayerNextOffset offset hnext) :=
                fun h => hpre (hregion.2 h)
              simp [hcellMem, hprefixMem, htarget]
        · rw [dif_neg hcurrent]
          have hnotActive : targetEdge.1 ∉
              pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
                web.toFormation corridor hinterior
                  (sourceLocalLayerNextOffset offset hnext) := by
            intro hactive
            rcases
                pointwiseSelectedSourceLocalLayerSerialCellRebase_activeTarget_mem_switch_or_currentCell
                  graphData minimal caps coloring web corridor hinterior offset
                    hnext targetEdge hactive with hswitch | hcellMem
            · exact hroleEdge
                ((mem_pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_iff
                  web.toFormation corridor hinterior offset hnext
                    targetEdge.1).1 hswitch)
            · exact hcurrent
                (Finset.mem_union_left _ (Finset.mem_union_left _ hcellMem))
          simp [hnotActive]

end

end GoertzelV24ClosedWebPointwiseSelectedCarrierTransport

end Mettapedia.GraphTheory.FourColor
