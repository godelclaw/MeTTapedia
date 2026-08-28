import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedRollingLocality
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedTrackedSuccessor
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedBoundaryRebaseSuccessor
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingSuccessor

/-!
# Exact rolling tracked successor for the pointwise-selected carrier

The graph-free rolling factor is independent of the geometric selector used
to name a corridor Cell.  This module instantiates it on the corrected
pointwise-selected carriers.  The locality theorem proves that every active
coordinate of the following interaction has a source in the present bounded
interaction; partial contraction therefore returns the complete canonical
tracked exterior at the following cut.

This is an exact one-step factorization on arbitrary cumulative colour
functions.  No eventual profile saturation statement is used.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedRollingTrackedSuccessor

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingSuccessor
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
open GoertzelV24ClosedWebPointwiseSelectedRootedInteractionState
open GoertzelV24ClosedWebPointwiseSelectedRollingLocality
open GoertzelV24ClosedWebPointwiseSelectedTrackedRebaseFactor
open GoertzelV24ClosedWebPointwiseSelectedTrackedSuccessor
open GoertzelV24ClosedWebPointwiseSelectedTrackedUniformRecurrence
open GoertzelV24CorridorProfile
open GoertzelV24FacialPentagonCap
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorForget
open GoertzelV24InterfaceDeletionComponentFactorForgetExterior
open GoertzelV24InterfaceExteriorSupportedPortProjection
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open GoertzelV24WindingClassification
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedRollingTrackedSuccessorEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance pointwiseSelectedRollingTrackedSuccessorOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-! ## Selected role lookup -/

/-- Locate an ambient edge in the pointwise-selected four-role rebase ABI. -/
noncomputable def pointwiseSelectedBoundaryRebaseRoleForEdge?
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) (edge : G.edgeSet) :
    Option SourceLocalLayerBoundaryRebaseRole :=
  if hrole : ∃ role,
      pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt web.toFormation
        corridor hinterior offset hnext role = edge then
    some (Classical.choose hrole)
  else none

theorem pointwiseSelectedBoundaryRebaseRoleForEdge?_eq_some_edge_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) (edge : G.edgeSet)
    (role : SourceLocalLayerBoundaryRebaseRole)
    (hrole : pointwiseSelectedBoundaryRebaseRoleForEdge? corridor hinterior
      offset hnext edge = some role) :
    pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt web.toFormation
      corridor hinterior offset hnext role = edge := by
  simp only [pointwiseSelectedBoundaryRebaseRoleForEdge?] at hrole
  split at hrole <;> rename_i hexists
  · injection hrole with hchosen
    rw [← hchosen]
    exact Classical.choose_spec hexists
  · cases hrole

theorem pointwiseSelectedBoundaryRebaseRoleForEdge?_eq_none_not_mem_switch
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) (edge : G.edgeSet)
    (hrole : pointwiseSelectedBoundaryRebaseRoleForEdge? corridor hinterior
      offset hnext edge = none) :
    edge ∉ pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt web.toFormation
      corridor hinterior offset hnext := by
  rw [mem_pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_iff]
  intro hexists
  simp only [pointwiseSelectedBoundaryRebaseRoleForEdge?] at hrole
  split at hrole <;> rename_i hfound
  · cases hrole
  · exact hfound hexists

/-! ## The literal selected rolling factor -/

/-- The finite rolling factor on two consecutive pointwise-selected
Cell--rebase positions. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialTrackedRollingFactorAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (hcellNext :
      (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior (sourceLocalLayerNextOffset offset hnext)).card ≤ 6)
    (color : G.edgeSet → Color) :
    SourceLocalLayerSerialTrackedRollingFactor := by
  classical
  let rebase :=
    pointwiseSelectedSourceLocalLayerSerialTrackedRebaseFactorAt web corridor
      hinterior offset hnext hcell hcellNext color
  let next := sourceLocalLayerNextOffset offset hnext
  let currentInteraction :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
      web.toFormation corridor hinterior offset hnext
  let target :=
    pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
      web.toFormation corridor hinterior next
  let nextInteraction :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
      web.toFormation corridor hinterior next hnextNext
  have hnextInteraction : nextInteraction.card ≤ 49 :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
      web.toFormation corridor hinterior next hnextNext hcellNext
  have hcurrentInteraction : currentInteraction.card ≤ 49 :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
      web.toFormation corridor hinterior offset hnext hcell
  exact {
    rebase := rebase
    nextInteractionCount :=
      ⟨nextInteraction.card, Nat.lt_succ_of_le hnextInteraction⟩
    nextInteractionSource :=
      finiteCarrierPartialSource currentInteraction nextInteraction
    nextInteractionActive := fun nextSlot => decide
      (((carrierCoordinate nextInteraction).symm nextSlot).1 ∈
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
          web.toFormation corridor hinterior next)
    nextColorActive := fun stableTarget =>
      if htarget : stableTarget.val < nextInteraction.card then
        decide (((carrierCoordinate nextInteraction).symm
          ⟨stableTarget.val, htarget⟩).1 ∈
            pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
              web.toFormation corridor hinterior next)
      else false
    nextColorRole := fun stableTarget =>
      if htarget : stableTarget.val < nextInteraction.card then
        pointwiseSelectedBoundaryRebaseRoleForEdge? corridor hinterior offset
          hnext ((carrierCoordinate nextInteraction).symm
            ⟨stableTarget.val, htarget⟩).1
      else none
    nextColorSource := fun stableTarget =>
      if htarget : stableTarget.val < nextInteraction.card then
        (finiteCarrierPartialSource currentInteraction nextInteraction
          ⟨stableTarget.val, htarget⟩).map (Fin.castLE hcurrentInteraction)
      else none
    nextCurrentCoordinate := fun targetSlot =>
      carrierCoordinate nextInteraction
        ⟨((carrierCoordinate target).symm targetSlot).1,
          Finset.mem_union_left _ ((carrierCoordinate target).symm
            targetSlot).2⟩ }

/-! ## Exact rolling colour receipt -/

/-- Pointwise decoder equation for the selected rolling colour ABI. -/
theorem pointwiseSelectedSourceLocalLayerSerialTrackedRollingFactorAt_nextInteractionColorCode_apply
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (hcellNext :
      (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior (sourceLocalLayerNextOffset offset hnext)).card ≤ 6)
    (color : G.edgeSet → Color)
    (preRebaseColor : SourceLocalLayerSerialTrackedInteractionColorCode)
    (roleColor : SourceLocalLayerBoundaryRebaseRole → StrandColor)
    (stable : Fin 49) :
    let currentInteraction :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
        web.toFormation corridor hinterior offset hnext
    let next := sourceLocalLayerNextOffset offset hnext
    let nextInteraction :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
        web.toFormation corridor hinterior next hnextNext
    let currentBound : currentInteraction.card ≤ 49 :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
        web.toFormation corridor hinterior offset hnext hcell
    (pointwiseSelectedSourceLocalLayerSerialTrackedRollingFactorAt web corridor
      hinterior offset hnext hnextNext hcell hcellNext color
      ).nextInteractionColorCode preRebaseColor roleColor stable =
      if htarget : stable.val < nextInteraction.card then
        let target : Fin nextInteraction.card := ⟨stable.val, htarget⟩
        let edge := ((carrierCoordinate nextInteraction).symm target).1
        if edge ∈
            pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
              web.toFormation corridor hinterior next then
          match pointwiseSelectedBoundaryRebaseRoleForEdge? corridor hinterior
              offset hnext edge with
          | some role => some (StrandColor.toColor (roleColor role))
          | none =>
              match finiteCarrierPartialSource currentInteraction nextInteraction
                  target with
              | some source => preRebaseColor (Fin.castLE currentBound source)
              | none => none
        else none
      else none := by
  classical
  dsimp only
  unfold SourceLocalLayerSerialTrackedRollingFactor.nextInteractionColorCode
  simp only [pointwiseSelectedSourceLocalLayerSerialTrackedRollingFactorAt]
  by_cases htarget : stable.val <
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
        web.toFormation corridor hinterior (sourceLocalLayerNextOffset offset hnext)
          hnextNext).card
  · simp only [htarget, dif_pos]
    let target : Fin
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
          web.toFormation corridor hinterior (sourceLocalLayerNextOffset offset hnext)
            hnextNext).card :=
      ⟨stable.val, htarget⟩
    let edge := ((carrierCoordinate
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
        web.toFormation corridor hinterior (sourceLocalLayerNextOffset offset hnext)
          hnextNext)).symm target).1
    by_cases hactive : edge ∈
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
          web.toFormation corridor hinterior
            (sourceLocalLayerNextOffset offset hnext)
    · simp [target, edge, hactive]
      cases hroleValue : pointwiseSelectedBoundaryRebaseRoleForEdge? corridor
          hinterior offset hnext edge with
      | some role => rfl
      | none =>
          cases hsource : finiteCarrierPartialSource
              (pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
                web.toFormation corridor hinterior offset hnext)
              (pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
                web.toFormation corridor hinterior (sourceLocalLayerNextOffset offset hnext)
                  hnextNext) target <;> rfl
    · simp [hactive, target, edge]
  · simp [htarget]

/-- The selected finite colour recurrence is exact: a newly exposed switch
coordinate reads the four-role receipt, and every other active coordinate is
transported from the present interaction receipt. -/
theorem pointwiseSelectedSourceLocalLayerSerialTrackedRollingNextInteractionColorCodeAt_eq
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (hcellNext :
      (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior (sourceLocalLayerNextOffset offset hnext)).card ≤ 6)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hrole : ∀ role,
      color (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt web.toFormation
        corridor hinterior offset hnext role) ≠ 0) :
    let currentInteraction :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
        web.toFormation corridor hinterior offset hnext
    let next := sourceLocalLayerNextOffset offset hnext
    let nextInteraction :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
        web.toFormation corridor hinterior next hnextNext
    let factor := pointwiseSelectedSourceLocalLayerSerialTrackedRollingFactorAt
      web corridor hinterior offset hnext hnextNext hcell hcellNext color
    factor.nextInteractionColorCode
        (sourceLocalLayerSerialTrackedInteractionColorCodeAt currentInteraction
          (pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
            web.toFormation corridor hinterior offset hnext hcell)
          (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt
            web.toFormation corridor hinterior offset) color)
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt
          web.toFormation corridor hinterior offset hnext color hrole).roleColor =
      sourceLocalLayerSerialTrackedInteractionColorCodeAt nextInteraction
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
          web.toFormation corridor hinterior next hnextNext hcellNext)
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
          web.toFormation corridor hinterior next) color := by
  classical
  dsimp only
  let currentInteraction :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
      web.toFormation corridor hinterior offset hnext
  let next := sourceLocalLayerNextOffset offset hnext
  let nextInteraction :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
      web.toFormation corridor hinterior next hnextNext
  let currentBound : currentInteraction.card ≤ 49 :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
      web.toFormation corridor hinterior offset hnext hcell
  let nextBound : nextInteraction.card ≤ 49 :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
      web.toFormation corridor hinterior next hnextNext hcellNext
  funext stable
  rw [pointwiseSelectedSourceLocalLayerSerialTrackedRollingFactorAt_nextInteractionColorCode_apply]
  by_cases hslot : stable.val < nextInteraction.card
  · let target : Fin nextInteraction.card := ⟨stable.val, hslot⟩
    let edge := ((carrierCoordinate nextInteraction).symm target).1
    rw [dif_pos hslot]
    dsimp only
    have hstable : Fin.castLE nextBound target = stable := by
      apply Fin.ext
      rfl
    have htargetCode :
        sourceLocalLayerSerialTrackedInteractionColorCodeAt nextInteraction
            nextBound
            (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
              web.toFormation corridor hinterior next) color stable =
          if edge ∈
              pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
                web.toFormation corridor hinterior next
          then some (color edge) else none := by
      rw [← hstable,
        sourceLocalLayerSerialTrackedInteractionColorCodeAt_live]
    rw [htargetCode]
    by_cases hactive : edge ∈
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
          web.toFormation corridor hinterior next
    · rw [if_pos hactive]
      cases hroleSlot : pointwiseSelectedBoundaryRebaseRoleForEdge? corridor
          hinterior offset hnext edge with
      | some role =>
          have hedge :=
            pointwiseSelectedBoundaryRebaseRoleForEdge?_eq_some_edge_eq corridor
              hinterior offset hnext edge role hroleSlot
          simp only [hactive, if_true]
          rw [pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt_roleColor_toColor]
          exact congrArg Option.some (congrArg color hedge)
      | none =>
          have hnotSwitch :=
            pointwiseSelectedBoundaryRebaseRoleForEdge?_eq_none_not_mem_switch
              corridor hinterior offset hnext edge hroleSlot
          have hpre : edge ∈
              pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt
                web.toFormation corridor hinterior offset :=
            (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutput_mem_iff_nextTerminalInput_of_not_mem_switch
              web.toFormation corridor hinterior offset hnext edge hnotSwitch).2
                hactive
          let targetEdge : {edge // edge ∈ nextInteraction} :=
            (carrierCoordinate nextInteraction).symm target
          have hcurrent : edge ∈ currentInteraction := by
            exact
              pointwiseSelectedSourceLocalLayerSerialCellRebase_activeNextInteraction_mem_currentInteraction
                graphData minimal caps coloring web corridor hinterior offset
                  hnext hnextNext targetEdge hactive
          let currentSlot : Fin currentInteraction.card :=
            carrierCoordinate currentInteraction ⟨edge, hcurrent⟩
          have hsource : finiteCarrierPartialSource currentInteraction
              nextInteraction target = some currentSlot := by
            simp only [finiteCarrierPartialSource]
            rw [dif_pos hcurrent]
          have hpreCode :
              sourceLocalLayerSerialTrackedInteractionColorCodeAt
                  currentInteraction currentBound
                  (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt
                    web.toFormation corridor hinterior offset) color
                  (Fin.castLE currentBound currentSlot) = some (color edge) := by
            rw [sourceLocalLayerSerialTrackedInteractionColorCodeAt_live]
            have hcurrentSlotEdge :
                ((carrierCoordinate currentInteraction).symm currentSlot).1 =
                  edge := by
              simp [currentSlot]
            rw [hcurrentSlotEdge, if_pos hpre]
          simp only [hactive, if_true]
          rw [hsource]
          exact hpreCode
    · rw [if_neg hactive]
      rw [if_neg hactive]
  · rw [dif_neg hslot]
    change none = if _h : stable.val < nextInteraction.card then _ else none
    rw [dif_neg hslot]

/-- The selected colour decoder is exactly the interaction-colour field of
the canonical rooted state at the next cut. -/
theorem pointwiseSelectedSourceLocalLayerSerialTrackedRollingNextInteractionColorCodeAt_eq_rooted
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (hcellNext :
      (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior (sourceLocalLayerNextOffset offset hnext)).card ≤ 6)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hrole : ∀ role,
      color (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt web.toFormation
        corridor hinterior offset hnext role) ≠ 0) :
    let currentInteraction :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
        web.toFormation corridor hinterior offset hnext
    let factor := pointwiseSelectedSourceLocalLayerSerialTrackedRollingFactorAt
      web corridor hinterior offset hnext hnextNext hcell hcellNext color
    let preRebaseColor :=
      sourceLocalLayerSerialTrackedInteractionColorCodeAt currentInteraction
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
          web.toFormation corridor hinterior offset hnext hcell)
        (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt
          web.toFormation corridor hinterior offset) color
    let rebase :=
      pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt
        web.toFormation corridor hinterior offset hnext color hrole
    factor.nextInteractionColorCode preRebaseColor rebase.roleColor =
      (pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
        web.toFormation corridor hinterior (sourceLocalLayerNextOffset offset hnext)
          hnextNext hcellNext color
          (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorCrossingNonzeroForColorAt
            web.toFormation corridor hinterior offset hnext color hrole)
      ).interactionColorCode := by
  dsimp only
  rw [pointwiseSelectedSourceLocalLayerSerialTrackedRollingNextInteractionColorCodeAt_eq
    graphData minimal caps coloring web corridor hinterior offset hnext hnextNext
      hcell hcellNext color hrole]
  rfl

/-! ## Exact rolling tracked exterior -/

/-- Rowwise exactness of selected rolling interaction contraction. -/
theorem pointwiseSelectedSourceLocalLayerSerialTrackedRollingNextInteractionStateAt_code_eq
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (hcellNext :
      (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior (sourceLocalLayerNextOffset offset hnext)).card ≤ 6)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair) :
    let preRebase :=
      pointwiseSelectedSourceLocalLayerSerialTrackedInteractionPreRebaseStateForColorAt
        web corridor hinterior offset hnext hcell color
    let factor := pointwiseSelectedSourceLocalLayerSerialTrackedRollingFactorAt
      web corridor hinterior offset hnext hnextNext hcell hcellNext color
    let nextInteraction :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
        web.toFormation corridor hinterior (sourceLocalLayerNextOffset offset hnext)
          hnextNext
    (factor.nextInteractionState preRebase (by rfl)).code pair =
      exactInterfaceExteriorCode
        (pointwiseSelectedSuccessorTrackedGraphForColorAt web.toFormation
          corridor hinterior offset hnext color pair)
        (fun slot : Fin nextInteraction.card =>
          ((carrierCoordinate nextInteraction).symm slot).1) := by
  dsimp only
  let graph := pointwiseSelectedSuccessorTrackedGraphForColorAt web.toFormation
    corridor hinterior offset hnext color pair
  let currentInteraction :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
      web.toFormation corridor hinterior offset hnext
  let currentVertex :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt web
      corridor hinterior offset hnext
  let nextInteraction :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
      web.toFormation corridor hinterior (sourceLocalLayerNextOffset offset hnext)
        hnextNext
  let nextVertex := fun slot : Fin nextInteraction.card =>
    ((carrierCoordinate nextInteraction).symm slot).1
  let retain := finiteCarrierPartialSource currentInteraction nextInteraction
  change partialContractedInterfaceExteriorCode
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedSuccessorRawCodeAt
        web corridor hinterior offset hnext color pair) retain =
    exactInterfaceExteriorCode graph nextVertex
  rw [pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedSuccessorCodeAt_exact
    web corridor hinterior offset hnext color pair]
  have hinjective : Function.Injective nextVertex := by
    intro left right heq
    apply (carrierCoordinate nextInteraction).symm.injective
    exact Subtype.ext heq
  have hsome : ∀ retained slot, retain retained = some slot →
      currentVertex slot = nextVertex retained := by
    intro retained slot hretain
    exact finiteCarrierPartialSource_eq_some_value_eq currentInteraction
      nextInteraction retained slot hretain
  have hnone : ∀ retained, retain retained = none →
      nextVertex retained ∉ graph.support := by
    intro retained hretain
    let targetEdge : {edge // edge ∈ nextInteraction} :=
      (carrierCoordinate nextInteraction).symm retained
    have hnotCurrent : targetEdge.1 ∉ currentInteraction :=
      finiteCarrierPartialSource_eq_none_not_mem currentInteraction
        nextInteraction retained hretain
    exact
      pointwiseSelectedSourceLocalLayerSerialCellRebase_nextInteraction_none_not_mem_support
        graphData minimal caps coloring web corridor hinterior offset hnext
          hnextNext color pair targetEdge hnotCurrent
  apply boundedInterfaceExteriorCode_ext_iff
  · intro left right
    change partialReindexedVertexEq left right = true ↔
      (exactInterfaceExteriorCode graph nextVertex).vertexEq left right = true
    rw [partialReindexedVertexEq_eq_true_iff nextVertex hinjective]
    simp [exactInterfaceExteriorCode]
  · intro left right
    change partialReindexedDirectAdj
        (exactInterfaceExteriorCode graph currentVertex) retain left right = true ↔
      (exactInterfaceExteriorCode graph nextVertex).directAdj left right = true
    rw [partialReindexedDirectAdj_exact_iff graph currentVertex nextVertex retain
      hsome hnone left right]
    simp [exactInterfaceExteriorCode]
  · intro left right
    change partialReindexedExteriorConnected
        (exactInterfaceExteriorCode graph currentVertex) retain left right = true ↔
      (exactInterfaceExteriorCode graph nextVertex).exteriorConnected left right =
        true
    rw [partialReindexedExteriorConnected_exact_eq_true_iff graph currentVertex
      nextVertex retain hsome hnone left right]
    simp [exactInterfaceExteriorCode]

/-- The selected finite contraction is exactly the following rooted state's
interaction-exterior field. -/
theorem pointwiseSelectedSourceLocalLayerSerialTrackedRollingNextInteractionStateAt_eq
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (hcellNext :
      (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior (sourceLocalLayerNextOffset offset hnext)).card ≤ 6)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcrossing : ∀ step,
      color (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
        corridor hinterior (sourceLocalLayerNextOffset offset hnext) step) ≠ 0) :
    let preRebase :=
      pointwiseSelectedSourceLocalLayerSerialTrackedInteractionPreRebaseStateForColorAt
        web corridor hinterior offset hnext hcell color
    let factor := pointwiseSelectedSourceLocalLayerSerialTrackedRollingFactorAt
      web corridor hinterior offset hnext hnextNext hcell hcellNext color
    factor.nextInteractionState preRebase (by rfl) =
      (pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
        web.toFormation corridor hinterior (sourceLocalLayerNextOffset offset hnext)
          hnextNext hcellNext color hcrossing).interactionExterior := by
  dsimp only
  rw [BoundedInterfaceExteriorFamilyCode.mk.injEq]
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  funext pair
  rw [pointwiseSelectedSourceLocalLayerSerialTrackedRollingNextInteractionStateAt_code_eq
    graphData minimal caps coloring web corridor hinterior offset hnext hnextNext
      hcell hcellNext color pair]
  rfl

/-- The finite rolling inclusion agrees with the following rooted state's
current-coordinate field. -/
theorem pointwiseSelectedSourceLocalLayerSerialTrackedRollingFactorAt_nextCurrentCoordinate_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (hcellNext :
      (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior (sourceLocalLayerNextOffset offset hnext)).card ≤ 6)
    (color : G.edgeSet → Color)
    (hcrossing : ∀ step,
      color (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
        corridor hinterior (sourceLocalLayerNextOffset offset hnext) step) ≠ 0) :
    (pointwiseSelectedSourceLocalLayerSerialTrackedRollingFactorAt web corridor
      hinterior offset hnext hnextNext hcell hcellNext color
      ).nextCurrentCoordinate =
      (pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
        web.toFormation corridor hinterior (sourceLocalLayerNextOffset offset hnext)
          hnextNext hcellNext color hcrossing).currentCoordinate := by
  rfl

end

end GoertzelV24ClosedWebPointwiseSelectedRollingTrackedSuccessor

end Mettapedia.GraphTheory.FourColor
