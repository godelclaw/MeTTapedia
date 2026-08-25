import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialColoredCumulativeStateForColor

/-!
# Transport the stable Cell carrier across one boundary rebase

The cumulative state before and after one source Cell uses the same fixed
twenty-one-slot ABI, but the slots enumerate two different literal carriers.
The boundary rebase may additionally change four named edges.  This file
records the exact finite change of coordinates: every target slot is decoded
either as one of the four rebase roles or as a slot of the predecessor
carrier.

The coordinate map is prefix-independent.  It contains edge-identification
data from the bounded Cell--rebase window, not a successor connectivity table.
The later recurrence must prove that every target-carrier edge active in the
new prefix is covered by this map and then transport the tracked, facial, and
colour coordinates through it.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellRebaseCarrierTransport

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseOutputColorParametric
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteColorCompatibility
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteTrackedColorCode
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexCorridorFiniteColorTransition
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cellRebaseCarrierTransportOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- A target slot is supplied either by the predecessor's stable carrier or
by one of the four edges whose regional status may change in the rebase. -/
abbrev SourceLocalLayerSerialCellRebaseCarrierSource :=
  Fin 21 ⊕ SourceLocalLayerBoundaryRebaseRole

/-- Decode one target-carrier slot into the bounded predecessor Cell--rebase
window.  Rebase roles take precedence because their regional activity may
change even when the same edge is also present in the predecessor carrier. -/
noncomputable def sourceLocalLayerSerialCellRebaseCarrierSourceAt
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    Fin 21 → Option SourceLocalLayerSerialCellRebaseCarrierSource :=
  fun targetSlot =>
    (sourceLocalLayerSerialTrackedTransitionEdgeAtSlot? graphData caps coloring
      web corridor hunique (sourceLocalLayerNextOffset offset hnext)
      targetSlot).bind fun targetEdge =>
        if hrole : ∃ role : SourceLocalLayerBoundaryRebaseRole,
            sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
              role = targetEdge.1 then
          some (.inr (Classical.choose hrole))
        else if hcurrent : targetEdge.1 ∈
            sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
              coloring web corridor hunique offset then
          some (.inl
            (sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal
              caps coloring web corridor hunique offset
              ⟨targetEdge.1, hcurrent⟩))
        else none

/-- On a literal target edge, the finite map returns a rebase role exactly
when the edge has one; otherwise it returns the predecessor coordinate exactly
when that edge lies in the predecessor carrier. -/
theorem sourceLocalLayerSerialCellRebaseCarrierSourceAt_targetSlot
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (targetEdge : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique (sourceLocalLayerNextOffset offset hnext)}) :
    sourceLocalLayerSerialCellRebaseCarrierSourceAt graphData minimal caps
        coloring web corridor hunique offset hnext
        (sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal caps
          coloring web corridor hunique
          (sourceLocalLayerNextOffset offset hnext) targetEdge) =
      if hrole : ∃ role : SourceLocalLayerBoundaryRebaseRole,
          sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
            role = targetEdge.1 then
        some (.inr (Classical.choose hrole))
      else if hcurrent : targetEdge.1 ∈
          sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
            coloring web corridor hunique offset then
        some (.inl
          (sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal caps
            coloring web corridor hunique offset
            ⟨targetEdge.1, hcurrent⟩))
      else none := by
  unfold sourceLocalLayerSerialCellRebaseCarrierSourceAt
  rw [sourceLocalLayerSerialTrackedTransitionEdgeAtSlot?_slot]
  rfl

/-- Every edge in the four-role switch is represented by the role branch of
the finite carrier transport. -/
theorem sourceLocalLayerSerialCellRebaseCarrierSourceAt_isSome_of_mem_switch
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (targetEdge : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique (sourceLocalLayerNextOffset offset hnext)})
    (hswitch : targetEdge.1 ∈
      sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext) :
    (sourceLocalLayerSerialCellRebaseCarrierSourceAt graphData minimal caps
      coloring web corridor hunique offset hnext
      (sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal caps
        coloring web corridor hunique
        (sourceLocalLayerNextOffset offset hnext) targetEdge)).isSome := by
  rw [sourceLocalLayerSerialCellRebaseCarrierSourceAt_targetSlot]
  have hrole : ∃ role : SourceLocalLayerBoundaryRebaseRole,
      sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role =
        targetEdge.1 :=
    (mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff corridor hunique offset
      hnext targetEdge.1).1 hswitch
  simp [hrole]

/-- Executable coverage test: every active target colour slot has a source in
the bounded predecessor Cell--rebase window. -/
def SourceLocalLayerSerialCellRebaseCarrierCoverageBool
    (sourceAt : Fin 21 →
      Option SourceLocalLayerSerialCellRebaseCarrierSource)
    (targetColor : SourceLocalLayerSerialCarrierColorCode) : Bool :=
  decide (∀ slot, targetColor slot ≠ none → (sourceAt slot).isSome)

/-- Relabel the predecessor's post-Cell colour table onto the target carrier.
Named rebase roles use the successor role state because the rebase may change
their regional activity; all other slots use the predecessor carrier map. -/
def SourceLocalLayerSerialCellRebaseTransportedColorCode
    (sourceAt : Fin 21 →
      Option SourceLocalLayerSerialCellRebaseCarrierSource)
    (preRebaseColor : SourceLocalLayerSerialCarrierColorCode)
    (rebaseState : SourceLocalLayerBoundaryRebaseTrackedState) :
    SourceLocalLayerSerialCarrierColorCode :=
  fun targetSlot =>
    match sourceAt targetSlot with
    | none => none
    | some (.inl predecessorSlot) => preRebaseColor predecessorSlot
    | some (.inr role) =>
        if rebaseState.roleInRegion role then
          some (rebaseState.roleColor role).toColor
        else none

/-- On literal source data, the executable coverage test is exactly the
geometric statement that every active target-carrier edge is either a named
rebase edge or already belongs to the predecessor carrier.  This is the
precise bounded-overlap lemma needed by the remaining recurrence. -/
theorem sourceLocalLayerSerialCellRebaseCarrierCoverageBool_eq_true_iff
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color) :
    SourceLocalLayerSerialCellRebaseCarrierCoverageBool
        (sourceLocalLayerSerialCellRebaseCarrierSourceAt graphData minimal caps
          coloring web corridor hunique offset hnext)
        (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
          corridor hunique (sourceLocalLayerNextOffset offset hnext)
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
            (sourceLocalLayerNextOffset offset hnext)) color) = true ↔
      ∀ targetEdge : {edge // edge ∈
          sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
            coloring web corridor hunique
              (sourceLocalLayerNextOffset offset hnext)},
        targetEdge.1 ∈ sourceLocalLayerSerialTerminalInputRegionAt corridor
            hunique (sourceLocalLayerNextOffset offset hnext) →
          targetEdge.1 ∈ sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique
              offset hnext ∨
            targetEdge.1 ∈
              sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
                coloring web corridor hunique offset := by
  rw [SourceLocalLayerSerialCellRebaseCarrierCoverageBool,
    decide_eq_true_eq]
  constructor
  · intro hcoverage targetEdge hactive
    have htargetColor :
        sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
            corridor hunique (sourceLocalLayerNextOffset offset hnext)
            (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
              (sourceLocalLayerNextOffset offset hnext)) color
            (sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal caps
              coloring web corridor hunique
              (sourceLocalLayerNextOffset offset hnext) targetEdge) ≠ none := by
      intro hnone
      exact
        (sourceLocalLayerSerialCarrierColorCodeAt_eq_none_slot_iff graphData
          minimal caps coloring web corridor hunique
          (sourceLocalLayerNextOffset offset hnext)
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
            (sourceLocalLayerNextOffset offset hnext)) color targetEdge).1 hnone
          hactive
    have hsome := hcoverage
      (sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal caps
        coloring web corridor hunique
        (sourceLocalLayerNextOffset offset hnext) targetEdge) htargetColor
    rw [sourceLocalLayerSerialCellRebaseCarrierSourceAt_targetSlot] at hsome
    by_cases hrole : ∃ role : SourceLocalLayerBoundaryRebaseRole,
        sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role =
          targetEdge.1
    · exact Or.inl
        ((mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff corridor hunique offset
          hnext targetEdge.1).2 hrole)
    · simp only [hrole, ↓reduceDIte] at hsome
      by_cases hcurrent : targetEdge.1 ∈
          sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
            coloring web corridor hunique offset
      · exact Or.inr hcurrent
      · simp [hcurrent] at hsome
  · intro hgeometric slot htargetColor
    unfold sourceLocalLayerSerialCarrierColorCodeAt at htargetColor
    cases hdecode :
        sourceLocalLayerSerialTrackedTransitionEdgeAtSlot? graphData caps
          coloring web corridor hunique
          (sourceLocalLayerNextOffset offset hnext) slot with
    | none => simp [hdecode] at htargetColor
    | some targetEdge =>
        simp only [hdecode, Option.bind_some] at htargetColor
        split at htargetColor <;> rename_i hactive
        · have hcovered := hgeometric targetEdge hactive
          unfold sourceLocalLayerSerialCellRebaseCarrierSourceAt
          rw [hdecode]
          simp only [Option.bind_some]
          rcases hcovered with hswitch | hcurrent
          · have hrole : ∃ role : SourceLocalLayerBoundaryRebaseRole,
                sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset
                  hnext role = targetEdge.1 :=
              (mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff corridor hunique
                offset hnext targetEdge.1).1 hswitch
            rw [dif_pos hrole]
            rfl
          · by_cases hrole : ∃ role : SourceLocalLayerBoundaryRebaseRole,
                sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset
                  hnext role = targetEdge.1
            · rw [dif_pos hrole]
              rfl
            · rw [dif_neg hrole, dif_pos hcurrent]
              rfl
        · exact (htargetColor rfl).elim

/-- Coverage of the target carrier reduces to one old-prefix lookahead
statement.  Current-Cell edges are already in the predecessor carrier, and
the four presentation-changing edges are represented by the rebase roles. -/
theorem sourceLocalLayerSerialCellRebaseCarrier_covered_of_oldPrefixLookahead
    (graphData : Data G)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hlookahead : ∀ targetEdge : {edge // edge ∈
        sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
          web corridor hunique (sourceLocalLayerNextOffset offset hnext)},
      targetEdge.1 ∈ sourceLocalLayerSerialTerminalInputRegionAt corridor
          hunique offset →
      targetEdge.1 ∉ sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique
          offset hnext →
        targetEdge.1 ∈
          sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
            coloring web corridor hunique offset) :
    ∀ targetEdge : {edge // edge ∈
        sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
          web corridor hunique (sourceLocalLayerNextOffset offset hnext)},
      targetEdge.1 ∈ sourceLocalLayerSerialTerminalInputRegionAt corridor
          hunique (sourceLocalLayerNextOffset offset hnext) →
        targetEdge.1 ∈ sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique
            offset hnext ∨
          targetEdge.1 ∈
            sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
              coloring web corridor hunique offset := by
  intro targetEdge htarget
  by_cases hswitch : targetEdge.1 ∈
      sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext
  · exact Or.inl hswitch
  · apply Or.inr
    have hpre : targetEdge.1 ∈
        sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset :=
      (sourceLocalLayerSerialPreRebaseOutput_mem_iff_nextTerminalInput_of_not_mem_switch
        corridor hunique offset hnext targetEdge.1 hswitch).2 htarget
    rw [← sourceLocalLayerSerialTerminalInputRegionAt_union_cell corridor hunique
      offset] at hpre
    rcases Finset.mem_union.mp hpre with hold | hcell
    · exact hlookahead targetEdge hold hswitch
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hcell)

/-- The old-prefix lookahead atom is itself a pairwise local-overlap
statement.  Incoming crossings and the retained rung are already represented
by the current Cell carrier; only a target-carrier edge recurring in a
strictly earlier literal Cell needs geometric localization. -/
theorem sourceLocalLayerSerialCellRebaseCarrier_oldPrefixLookahead_of_pastCellOverlap
    (graphData : Data G)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hpast : ∀
      (targetEdge : {edge // edge ∈
        sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
          web corridor hunique (sourceLocalLayerNextOffset offset hnext)})
      (prior : Fin (blockLength - 3)),
      prior.val < offset.val →
      targetEdge.1 ∈ sourceLocalLayerCellRegionAt corridor hunique prior →
        targetEdge.1 ∈ sourceLocalLayerBoundaryRebaseSwitchAt corridor
            hunique offset hnext ∨
          targetEdge.1 ∈
            sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
              coloring web corridor hunique offset) :
    ∀ targetEdge : {edge // edge ∈
        sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
          web corridor hunique (sourceLocalLayerNextOffset offset hnext)},
      targetEdge.1 ∈ sourceLocalLayerSerialTerminalInputRegionAt corridor
          hunique offset →
      targetEdge.1 ∉ sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique
          offset hnext →
        targetEdge.1 ∈
          sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
            coloring web corridor hunique offset := by
  intro targetEdge hold hnotSwitch
  rw [sourceLocalLayerSerialTerminalInputRegionAt, Finset.mem_union] at hold
  rcases hold with hinput | hrung
  · rw [sourceLocalLayerSerialInputRegionAt, Finset.mem_union] at hinput
    rcases hinput with hprefix | hcrossing
    · rw [sourceLocalLayerSerialPrefixRegion, Finset.mem_biUnion] at hprefix
      rcases hprefix with ⟨prior, hprior, hedge⟩
      have hlt := (Finset.mem_filter.mp hprior).2
      rcases hpast targetEdge prior hlt hedge with hswitch | hcurrent
      · exact (hnotSwitch hswitch).elim
      · exact hcurrent
    · rcases (mem_indexedCrossingEdgeSet_iff
          (sourceLocalLayerLeftCrossingAt corridor hunique offset)
          targetEdge.1).1 hcrossing with ⟨step, hedge⟩
      rw [← hedge]
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (sourceLocalLayerCellRegionAt_leftCrossing corridor hunique offset
          step))
  · have hedge : targetEdge.1 =
        sourceLocalLayerSharedRungAt corridor hunique offset := by
      simpa using hrung
    rw [hedge]
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

/-- The finite target colour table computed from one literal predecessor
state, Cell colour, and rebase role state. -/
noncomputable def sourceLocalLayerSerialCellRebaseTransportedColorCodeAt
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcell : ∀ {edge}, edge ∈
      sourceLocalLayerCellRegionAt corridor hunique offset →
        cellColor edge ≠ 0) : SourceLocalLayerSerialCarrierColorCode :=
  let splice := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
    coloring cellColor
  let hrole : ∀ role, splice
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0 :=
    sourceLocalLayerSerialCellSplicedColorAt_boundaryRebaseEdge_ne_zero
      corridor hunique offset hnext cellColor hcell
  SourceLocalLayerSerialCellRebaseTransportedColorCode
    (sourceLocalLayerSerialCellRebaseCarrierSourceAt graphData minimal caps
      coloring web corridor hunique offset hnext)
    (SourceLocalLayerSerialFiniteSplicedColor
      (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
        corridor hunique offset
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
        coloring)
      (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
        corridor hunique offset
        (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor))
    (successorTrackedStateForColorAt corridor hunique offset hnext splice hrole)

/-- Provided the bounded carrier map covers every active target edge, its
finite relabelling computes the literal target cumulative colour table
exactly.  The hypothesis is purely geometric and colour-independent. -/
theorem sourceLocalLayerSerialCellRebaseTransportedColorCodeAt_eq_target
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcell : ∀ {edge}, edge ∈
      sourceLocalLayerCellRegionAt corridor hunique offset →
        cellColor edge ≠ 0)
    (hcoverage : ∀ targetEdge : {edge // edge ∈
        sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
          web corridor hunique (sourceLocalLayerNextOffset offset hnext)},
      targetEdge.1 ∈ sourceLocalLayerSerialTerminalInputRegionAt corridor
          hunique (sourceLocalLayerNextOffset offset hnext) →
        targetEdge.1 ∈ sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique
            offset hnext ∨
          targetEdge.1 ∈
            sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
              coloring web corridor hunique offset) :
    sourceLocalLayerSerialCellRebaseTransportedColorCodeAt graphData minimal
        caps coloring web corridor hunique offset hnext cellColor hcell =
      sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
        corridor hunique (sourceLocalLayerNextOffset offset hnext)
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext))
        (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
          coloring cellColor) := by
  classical
  funext targetSlot
  let splice := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
    coloring cellColor
  let hroleNonzero : ∀ role, splice
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0 :=
    sourceLocalLayerSerialCellSplicedColorAt_boundaryRebaseEdge_ne_zero
      corridor hunique offset hnext cellColor hcell
  cases hdecode :
      sourceLocalLayerSerialTrackedTransitionEdgeAtSlot? graphData caps coloring
        web corridor hunique (sourceLocalLayerNextOffset offset hnext)
        targetSlot with
  | none =>
      unfold sourceLocalLayerSerialCellRebaseTransportedColorCodeAt
        SourceLocalLayerSerialCellRebaseTransportedColorCode
        sourceLocalLayerSerialCellRebaseCarrierSourceAt
        sourceLocalLayerSerialCarrierColorCodeAt
      rw [hdecode]
      rfl
  | some targetEdge =>
      unfold sourceLocalLayerSerialCellRebaseTransportedColorCodeAt
        SourceLocalLayerSerialCellRebaseTransportedColorCode
        sourceLocalLayerSerialCellRebaseCarrierSourceAt
        sourceLocalLayerSerialCarrierColorCodeAt
      rw [hdecode]
      simp only [Option.bind_some]
      by_cases hrole : ∃ role : SourceLocalLayerBoundaryRebaseRole,
          sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
            role = targetEdge.1
      · rw [dif_pos hrole]
        let role := Classical.choose hrole
        have hedge := Classical.choose_spec hrole
        change (if
            (successorTrackedStateForColorAt corridor hunique offset hnext
              splice hroleNonzero).roleInRegion role then
              some ((successorTrackedStateForColorAt corridor hunique offset
                hnext splice hroleNonzero).roleColor role).toColor
            else none) = _
        unfold successorTrackedStateForColorAt
        dsimp only [SourceLocalLayerBoundaryRebaseTrackedState.roleInRegion,
          SourceLocalLayerBoundaryRebaseTrackedState.roleColor]
        have hmemIff :
            sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
                role ∈ sourceLocalLayerSerialTerminalInputRegionAt corridor
                  hunique (sourceLocalLayerNextOffset offset hnext) ↔
              targetEdge.1 ∈ sourceLocalLayerSerialTerminalInputRegionAt
                corridor hunique (sourceLocalLayerNextOffset offset hnext) := by
          rw [hedge]
        by_cases hmem : targetEdge.1 ∈
            sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
              (sourceLocalLayerNextOffset offset hnext)
        · have hmemRole := hmemIff.mpr hmem
          have hcondition :
              decide
                (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset
                  hnext role ∈
                    sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
                      (sourceLocalLayerNextOffset offset hnext)) = true := by
            simp [hmemRole]
          rw [if_pos hcondition, if_pos hmem,
            strandColorOfNonzero_toColor]
          exact congrArg some (congrArg splice hedge)
        · have hmemRole := fun h => hmem (hmemIff.mp h)
          have hmemRole' :
              sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
                  role ∉
                sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
                  (sourceLocalLayerNextOffset offset hnext) :=
            hmemRole
          have hcondition : ¬ decide
              (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset
                hnext role ∈
                  sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
                    (sourceLocalLayerNextOffset offset hnext)) = true := by
            simp [hmemRole']
          rw [if_neg hcondition, if_neg hmem]
      · rw [dif_neg hrole]
        by_cases hcurrent : targetEdge.1 ∈
            sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
              coloring web corridor hunique offset
        · rw [dif_pos hcurrent]
          change SourceLocalLayerSerialFiniteSplicedColor
              (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring
                web corridor hunique offset
                (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
                  offset) coloring)
              (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring
                web corridor hunique offset
                (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor)
              (sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal
                caps coloring web corridor hunique offset
                ⟨targetEdge.1, hcurrent⟩) =
            if targetEdge.1 ∈
                sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
                  (sourceLocalLayerNextOffset offset hnext) then
              some (sourceLocalLayerSerialCellSplicedColorAt corridor hunique
                offset coloring cellColor targetEdge.1)
            else none
          rw [sourceLocalLayerSerialFiniteSplicedColor_codeAt_slot]
          have hnotSwitch : targetEdge.1 ∉
              sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset
                hnext := by
            rw [mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff]
            exact hrole
          have hregion :=
            sourceLocalLayerSerialPreRebaseOutput_mem_iff_nextTerminalInput_of_not_mem_switch
              corridor hunique offset hnext targetEdge.1 hnotSwitch
          by_cases hcellMem : targetEdge.1 ∈
              sourceLocalLayerCellRegionAt corridor hunique offset
          · have hpre : targetEdge.1 ∈
                sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
                  offset := by
              rw [← sourceLocalLayerSerialTerminalInputRegionAt_union_cell
                corridor hunique offset]
              exact Finset.mem_union_right _ hcellMem
            have htarget := hregion.1 hpre
            simp [hcellMem, htarget,
              sourceLocalLayerSerialCellSplicedColorAt]
          · by_cases hprefixMem : targetEdge.1 ∈
                sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
                  offset
            · have hpre : targetEdge.1 ∈
                  sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
                    offset := by
                rw [← sourceLocalLayerSerialTerminalInputRegionAt_union_cell
                  corridor hunique offset]
                exact Finset.mem_union_left _ hprefixMem
              have htarget := hregion.1 hpre
              simp [hcellMem, hprefixMem, htarget,
                sourceLocalLayerSerialCellSplicedColorAt]
            · have hpre : targetEdge.1 ∉
                  sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
                    offset := by
                rw [← sourceLocalLayerSerialTerminalInputRegionAt_union_cell
                  corridor hunique offset]
                simp [hcellMem, hprefixMem]
              have htarget : targetEdge.1 ∉
                  sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
                    (sourceLocalLayerNextOffset offset hnext) :=
                fun h => hpre (hregion.2 h)
              simp [hcellMem, hprefixMem, htarget]
        · rw [dif_neg hcurrent]
          have hnotActive : targetEdge.1 ∉
              sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
                (sourceLocalLayerNextOffset offset hnext) := by
            intro hactive
            rcases hcoverage targetEdge hactive with hswitch | hcurrent'
            · exact hrole
                ((mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff corridor
                  hunique offset hnext targetEdge.1).1 hswitch)
            · exact hcurrent hcurrent'
          simp [hnotActive]

/-- The complete colour-coordinate recurrence follows from the sole
old-prefix lookahead atom.  Thus the moving twenty-one-slot ABI introduces
no second colour obligation: once literal carrier overlap is localized, the
finite transport computes the next cumulative colour field exactly. -/
theorem sourceLocalLayerSerialCellRebaseTransportedColorCodeAt_eq_target_of_oldPrefixLookahead
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcell : ∀ {edge}, edge ∈
      sourceLocalLayerCellRegionAt corridor hunique offset →
        cellColor edge ≠ 0)
    (hlookahead : ∀ targetEdge : {edge // edge ∈
        sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
          web corridor hunique (sourceLocalLayerNextOffset offset hnext)},
      targetEdge.1 ∈ sourceLocalLayerSerialTerminalInputRegionAt corridor
          hunique offset →
      targetEdge.1 ∉ sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique
          offset hnext →
        targetEdge.1 ∈
          sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
            coloring web corridor hunique offset) :
    sourceLocalLayerSerialCellRebaseTransportedColorCodeAt graphData minimal
        caps coloring web corridor hunique offset hnext cellColor hcell =
      sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
        corridor hunique (sourceLocalLayerNextOffset offset hnext)
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext))
        (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
          coloring cellColor) := by
  apply sourceLocalLayerSerialCellRebaseTransportedColorCodeAt_eq_target
  exact sourceLocalLayerSerialCellRebaseCarrier_covered_of_oldPrefixLookahead
    graphData caps coloring web corridor hunique offset hnext hlookahead

/-- The full colour-coordinate recurrence needs only the pairwise geometric
locality of strict prior Cells.  All incoming-crossing and retained-rung cases
are discharged by the literal carrier definitions. -/
theorem sourceLocalLayerSerialCellRebaseTransportedColorCodeAt_eq_target_of_pastCellOverlap
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcell : ∀ {edge}, edge ∈
      sourceLocalLayerCellRegionAt corridor hunique offset →
        cellColor edge ≠ 0)
    (hpast : ∀
      (targetEdge : {edge // edge ∈
        sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
          web corridor hunique (sourceLocalLayerNextOffset offset hnext)})
      (prior : Fin (blockLength - 3)),
      prior.val < offset.val →
      targetEdge.1 ∈ sourceLocalLayerCellRegionAt corridor hunique prior →
        targetEdge.1 ∈ sourceLocalLayerBoundaryRebaseSwitchAt corridor
            hunique offset hnext ∨
          targetEdge.1 ∈
            sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
              coloring web corridor hunique offset) :
    sourceLocalLayerSerialCellRebaseTransportedColorCodeAt graphData minimal
        caps coloring web corridor hunique offset hnext cellColor hcell =
      sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
        corridor hunique (sourceLocalLayerNextOffset offset hnext)
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext))
        (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
          coloring cellColor) := by
  apply
    sourceLocalLayerSerialCellRebaseTransportedColorCodeAt_eq_target_of_oldPrefixLookahead
  exact
    sourceLocalLayerSerialCellRebaseCarrier_oldPrefixLookahead_of_pastCellOverlap
      graphData caps coloring web corridor hunique offset hnext hpast

end

end GoertzelV24ClosedWebLocalLayerSerialCellRebaseCarrierTransport

end Mettapedia.GraphTheory.FourColor
