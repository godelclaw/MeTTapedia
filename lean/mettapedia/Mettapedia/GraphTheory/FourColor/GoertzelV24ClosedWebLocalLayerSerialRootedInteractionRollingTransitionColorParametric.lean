import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingTransitionExact
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPreRebaseColorParametric

/-!
# Prefix-parametric rooted rolling Cell factor

The rolling factor is constructed from an arbitrary everywhere-positive
cumulative prefix colouring and an arbitrary positive compatible literal Cell
colouring.  The ambient Tait colouring names the corridor geometry only; it is
not used as the accumulated prefix.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingTransitionColorParametric

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24BoundedCarrierBoolGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseOutputColorParametric
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseSupportColorParametric
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStableParametricCapState
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteEdgeState
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteColorCompatibility
open GoertzelV24ClosedWebLocalLayerSerialCellNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellPastOverlap
open GoertzelV24ClosedWebLocalLayerSerialCellPrefixParametricNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseCarrierTransport
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellStateFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFullSuccessorState
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetComponentCap
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCode
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetFullState
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCap
open GoertzelV24ClosedWebLocalLayerSerialCellUniformTrackedTargetCode
open GoertzelV24ClosedWebLocalLayerSerialColoredCumulativeStateForColor
open GoertzelV24ClosedWebLocalLayerSerialRootedCumulativeState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFacePreRebaseExact
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFacePreRebaseState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceRollingExact
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceRollingSuccessor
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceSuccessor
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPreRebaseColorParametric
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPreRebaseState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingProjection
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingProjectionFactor
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingSuccessor
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingTransition
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingTransitionExact
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionTrackedSuccessor
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24FramedTrail
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24InterfaceExteriorSupportedPortProjection
open GoertzelV24InterfaceExteriorLabelCapFactorUpdate
open GoertzelV24MinimalFacialPentagonCapPairLocalCellCarrier
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance rollingTransitionColorParametricEdgeSetDecidableEq :
    DecidableEq G.edgeSet := Subtype.instDecidableEq

local instance rollingTransitionColorParametricOpenedGraphDecidableRel
    {graphData : Data G}
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- Positivity of both factors makes their right-biased splice nonzero at all
four finite rebase roles. -/
theorem
    sourceLocalLayerSerialCellSplicedColorAt_boundaryRebaseEdge_ne_zero_of_prefix
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (prefixColor cellColor : G.edgeSet → Color)
    (hprefix : ∀ edge, prefixColor edge ≠ 0)
    (hcell : ∀ {edge}, edge ∈
      sourceLocalLayerCellRegionAt corridor hunique offset →
        cellColor edge ≠ 0)
    (role : SourceLocalLayerBoundaryRebaseRole) :
    sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset prefixColor
        cellColor
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
          role) ≠ 0 := by
  by_cases hedge :
      sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role ∈
        sourceLocalLayerCellRegionAt corridor hunique offset
  · rw [sourceLocalLayerSerialCellSplicedColorAt_eq_cell_of_mem corridor
      hunique offset prefixColor cellColor hedge]
    exact hcell hedge
  · rw [sourceLocalLayerSerialCellSplicedColorAt]
    simp only [if_neg hedge]
    exact hprefix _

/-- On the literal two-cap carrier, the prefix-parametric finite colour
transport computes the next cumulative colour table without an extra overlap
hypothesis. -/
theorem
    sourceLocalLayerSerialCellRebaseTransportedColorCodeForColorAt_eq_target_unconditional
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
    (prefixColor cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hrole : ∀ role,
      sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
          prefixColor cellColor
          (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
            role) ≠ 0) :
    sourceLocalLayerSerialCellRebaseTransportedColorCodeForColorAt graphData
        minimal caps coloring web corridor hunique offset hnext prefixColor
          cellColor hrole =
      sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
        corridor hunique (sourceLocalLayerNextOffset offset hnext)
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext))
        (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
          prefixColor cellColor) := by
  apply
    sourceLocalLayerSerialCellRebaseTransportedColorCodeForColorAt_eq_target
  exact
    sourceLocalLayerSerialCellRebaseCarrier_covered_of_oldPrefixLookahead
      graphData caps coloring web corridor hunique offset hnext
        (sourceLocalLayerSerialCellRebaseCarrier_oldPrefixLookahead_of_pastCellOverlap
          graphData caps coloring web corridor hunique offset hnext
            (sourceLocalLayerSerialCellRebase_pastCellOverlap graphData minimal
              caps coloring web corridor hunique offset hnext))

/-- The rebase output profile is the input profile of the canonical successor
state for an arbitrary accumulated prefix. -/
theorem
    finiteBoolSupportLetterForColorAt_output_eq_nextColoredCumulativeState_input_of_prefix
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
    (prefixColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hprefixCrossing : ∀ step,
      prefixColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcell : ∀ {edge}, edge ∈
      sourceLocalLayerCellRegionAt corridor hunique offset →
        cellColor edge ≠ 0)
    (hrole : ∀ role,
      sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
          prefixColor cellColor
          (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
            role) ≠ 0) :
    let hcross : ∀ step,
        cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
          0 := fun step => hcell
            (sourceLocalLayerCellRegionAt_rightCrossing corridor hunique offset
              step)
    let factored :=
      sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt graphData
        minimal caps coloring web corridor hunique offset prefixColor
          hprefixCrossing cellColor hcross
    let splice := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
      prefixColor cellColor
    (finiteBoolSupportLetterForColorAt corridor hunique offset hnext factored.2.1
      splice hrole).output =
      (sourceLocalLayerSerialColoredCumulativeStateForColorAt graphData minimal
        caps coloring web corridor hunique
          (sourceLocalLayerNextOffset offset hnext) splice
            (successorCrossingNonzeroForColorAt corridor hunique offset hnext
              splice hrole)).input := by
  rfl

/-- Literal finite rolling factor over an arbitrary positive cumulative
prefix. -/
noncomputable def
    sourceLocalLayerSerialRootedInteractionRollingCellFactorForColorAt
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
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (prefixColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hprefix : ∀ edge, prefixColor edge ≠ 0)
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcell : ∀ {edge}, edge ∈
      sourceLocalLayerCellRegionAt corridor hunique offset →
        cellColor edge ≠ 0) :
    SourceLocalLayerSerialRootedInteractionRollingCellFactor := by
  classical
  let hprefixCrossing : ∀ step,
      prefixColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0 := fun step =>
      hprefix ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step)
  let hcross : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0 := fun step => hcell
          (sourceLocalLayerCellRegionAt_rightCrossing corridor hunique offset
            step)
  let factored :=
    sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt graphData
      minimal caps coloring web corridor hunique offset prefixColor
        hprefixCrossing cellColor hcross
  let splice := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
    prefixColor cellColor
  let hrole : ∀ role, splice
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0 :=
    sourceLocalLayerSerialCellSplicedColorAt_boundaryRebaseEdge_ne_zero_of_prefix
      corridor hunique offset hnext prefixColor cellColor hprefix hcell
  let rebase := finiteBoolSupportLetterForColorAt corridor hunique offset hnext
    factored.2.1 splice hrole
  let trackedRolling := sourceLocalLayerSerialTrackedRollingFactorAt graphData
    minimal caps coloring web corridor hunique offset hnext hnextNext splice
  let interaction :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
      coloring web corridor hunique offset hnext
  let interactionCellColor :=
    sourceLocalLayerSerialTrackedInteractionColorCodeAt interaction
      (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
        graphData minimal caps coloring web corridor hunique offset hnext)
      (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor
  let faceRolling := sourceLocalLayerSerialFaceRollingFactorAt graphData minimal
    caps coloring web corridor hunique offset hnext hnextNext
  let next := sourceLocalLayerNextOffset offset hnext
  let trackedTarget := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
    caps coloring web corridor hunique next
  let faceTarget := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
    hunique next
  let FacePort := SourceLocalLayerSerialFaceInputPortAt corridor hunique next
  have htrackedTarget : trackedRolling.rebase.targetCount.val =
      trackedTarget.card := by rfl
  have hfaceTarget : faceRolling.rebase.targetCount.val = faceTarget.card := by
    rfl
  have houtputCount : rebase.output.faceFragmentCount.val =
      Fintype.card FacePort := by rfl
  let facePortEquiv : Fin rebase.output.faceFragmentCount.val ≃ FacePort :=
    (Fintype.equivFin (Fin rebase.output.faceFragmentCount.val)).trans
      ((finCongr
          (Fintype.card_fin rebase.output.faceFragmentCount.val)).trans
        ((finCongr houtputCount).trans
          (Fintype.equivFin FacePort).symm))
  let projection : SourceLocalLayerSerialRollingProjectionFactor
      trackedRolling.rebase.targetCount faceRolling.rebase.targetCount
        rebase.output.faceFragmentCount := {
    trackedSlot := fun slot =>
      (sourceLocalLayerSerialCellRebaseTrackedTargetSlotAt graphData caps coloring
        web corridor hunique offset hnext slot).map
          (Fin.cast htrackedTarget.symm)
    trackedPortCoordinate := fun port => Fin.cast htrackedTarget.symm
      (carrierCoordinate trackedTarget
        (sourceLocalLayerSerialCellRebaseTrackedTargetPortEdgeAt graphData caps
          coloring web corridor hunique offset hnext port))
    faceSlot := fun slot =>
      (sourceLocalLayerSerialFaceTargetDartAtSlot? graphData minimal caps coloring
        web corridor hunique offset hnext slot).map
          (Fin.cast hfaceTarget.symm)
    facePortCoordinate := fun fragment => Fin.cast hfaceTarget.symm
      (sourceLocalLayerSerialFaceTargetPortCoordinateAt corridor hunique offset
        hnext (facePortEquiv fragment))
    colorSourceAt := sourceLocalLayerSerialCellRebaseCarrierSourceAt graphData
      minimal caps coloring web corridor hunique offset hnext }
  exact {
    cellOutput := factored.2.1
    localFactor := factored.2.2
    interactionCellColor := interactionCellColor
    rebaseLetter := rebase
    trackedRolling := trackedRolling
    faceRolling := faceRolling
    projection := projection }

/-- The arbitrary-prefix literal factor passes the complete executable support
guard whenever the two positive colourings agree on their overlap. -/
theorem
    sourceLocalLayerSerialRootedInteractionRollingCellFactorForColorAt_supportsBool
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
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (prefixColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hprefix : ∀ edge, prefixColor edge ≠ 0)
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcompatible : SourceLocalLayerSerialCellColorsCompatibleAt corridor
      hunique offset prefixColor cellColor)
    (hcell : ∀ {edge}, edge ∈
      sourceLocalLayerCellRegionAt corridor hunique offset →
        cellColor edge ≠ 0) :
    let hprefixCrossing : ∀ step,
        prefixColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor
          hunique offset).crossingEdge step) ≠ 0 := fun step =>
      hprefix ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step)
    let state := sourceLocalLayerSerialRootedInteractionStateForColorAt
      graphData minimal caps coloring web corridor hunique offset hnext
        prefixColor hprefixCrossing
    let factor :=
      sourceLocalLayerSerialRootedInteractionRollingCellFactorForColorAt
        graphData minimal caps coloring web corridor hunique offset hnext
          hnextNext prefixColor hprefix cellColor hcell
    factor.supportsBool state = true := by
  classical
  dsimp only
  let hprefixCrossing : ∀ step,
      prefixColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0 := fun step =>
      hprefix ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step)
  let hcross : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0 := fun step => hcell
          (sourceLocalLayerCellRegionAt_rightCrossing corridor hunique offset
            step)
  let factored :=
    sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt graphData
      minimal caps coloring web corridor hunique offset prefixColor
        hprefixCrossing cellColor hcross
  let splice := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
    prefixColor cellColor
  let hrole : ∀ role, splice
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0 :=
    sourceLocalLayerSerialCellSplicedColorAt_boundaryRebaseEdge_ne_zero_of_prefix
      corridor hunique offset hnext prefixColor cellColor hprefix hcell
  rw [SourceLocalLayerSerialRootedInteractionRollingCellFactor.supportsBool,
    Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · let state := sourceLocalLayerSerialRootedInteractionStateForColorAt
      graphData minimal caps coloring web corridor hunique offset hnext
        prefixColor hprefixCrossing
    have hstate : state.toSourceLocalLayerSerialColoredCumulativeState =
        factored.1 := by rfl
    change SourceLocalLayerSerialCellPhysicalSupportsBool
      state.toSourceLocalLayerSerialColoredCumulativeState factored.2.1
        factored.2.2 = true
    rw [hstate]
    exact
      sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt_supports
        graphData minimal caps coloring web corridor hunique offset prefixColor
          hprefixCrossing cellColor hcompatible hcross
  · change decide
      ((finiteBoolSupportLetterForColorAt corridor hunique offset hnext
        factored.2.1 splice hrole).input = factored.2.1) = true
    simp [finiteBoolSupportLetterForColorAt]
  · simpa
      [sourceLocalLayerSerialRootedInteractionRollingCellFactorForColorAt,
        hprefixCrossing, hcross, factored, splice, hrole] using
      (finiteBoolSupportLetterForColorAt_supports corridor hunique offset hnext
        factored.2.1 splice hrole)

/-- Facial pre-rebase update factored through precisely the two local fields it
reads. -/
def sourceLocalLayerSerialRootedInteractionFacePreRebaseStateOf?
    (state : SourceLocalLayerSerialRootedInteractionState)
    (faceCode : BoundedCarrierBoolGraphFamilyCode 24 0 Bool)
    (faceEdgeState : SourceLocalLayerSerialFaceFiniteEdgeState) :
    Option SourceLocalLayerSerialFaceInteractionPrefixState :=
  if hcount : state.faceCapSix.vertexCount = faceCode.vertexCount then
    some {
      vertexCount := state.faceInteractionExterior.vertexCount
      code := fun _ => addInterfaceAdjacencyAndPresence
        (state.faceInteractionExterior.code ())
        (liftInterfaceAdjacency state.faceCurrentCoordinate
          (fun left right =>
            let cast : Fin state.faceCapSix.vertexCount.val →
                Fin faceCode.vertexCount.val :=
              Fin.cast (congrArg Fin.val hcount)
            decide (((faceCode.toGraph false) ⊔
              (faceCode.toGraph true)).Adj (cast left) (cast right))))
        (liftInterfacePresence state.faceCurrentCoordinate (fun slot =>
          faceEdgeState.cellPresent
            (Fin.castLE
              (Nat.le_of_lt_succ state.faceCapSix.vertexCount.isLt) slot))) }
  else none

/-- The original local-factor API factors definitionally through its face
graph and presence table. -/
theorem sourceLocalLayerSerialRootedInteractionFacePreRebaseState?_eq_of_fields
    {outputCount : Fin 5}
    (state : SourceLocalLayerSerialRootedInteractionState)
    (factor : SourceLocalLayerSerialCellPhysicalBoolLocalFactor outputCount) :
    sourceLocalLayerSerialRootedInteractionFacePreRebaseState? state factor =
      sourceLocalLayerSerialRootedInteractionFacePreRebaseStateOf? state
        factor.faceCode factor.faceEdgeState := by
  unfold sourceLocalLayerSerialRootedInteractionFacePreRebaseState?
    sourceLocalLayerSerialRootedInteractionFacePreRebaseStateOf?
    sourceLocalLayerSerialRootedInteractionFacePreRebaseState
    sourceLocalLayerSerialRootedInteractionFaceLocalAdjacency
    sourceLocalLayerSerialRootedInteractionFaceLocalPresence
    sourceLocalLayerSerialCellPhysicalFaceLocalAdjacency
  rfl

/-- The guarded facial pre-rebase update is insensitive to every local-factor
field except the face graph and literal Cell-presence table. -/
theorem sourceLocalLayerSerialRootedInteractionFacePreRebaseState?_congr
    {leftOutputCount rightOutputCount : Fin 5}
    (state : SourceLocalLayerSerialRootedInteractionState)
    (left : SourceLocalLayerSerialCellPhysicalBoolLocalFactor leftOutputCount)
    (right : SourceLocalLayerSerialCellPhysicalBoolLocalFactor rightOutputCount)
    (hcode : left.faceCode = right.faceCode)
    (hedge : left.faceEdgeState = right.faceEdgeState) :
    sourceLocalLayerSerialRootedInteractionFacePreRebaseState? state left =
      sourceLocalLayerSerialRootedInteractionFacePreRebaseState? state right := by
  rw [sourceLocalLayerSerialRootedInteractionFacePreRebaseState?_eq_of_fields,
    sourceLocalLayerSerialRootedInteractionFacePreRebaseState?_eq_of_fields,
    hcode, hedge]

/-- The facial pre-rebase update depends only on the local face code and
presence table, so the prefix-parametric physical package has the same exact
source reflection as the ambient specialization. -/
theorem
    sourceLocalLayerSerialRootedInteractionFacePreRebaseStateForColor?_at
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
    (prefixColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hprefixCrossing : ∀ step,
      prefixColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcellCrossing : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0) :
    let state := sourceLocalLayerSerialRootedInteractionStateForColorAt
      graphData minimal caps coloring web corridor hunique offset hnext
        prefixColor hprefixCrossing
    let factor :=
      (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt graphData
        minimal caps coloring web corridor hunique offset prefixColor
          hprefixCrossing cellColor hcellCrossing).2.2
    sourceLocalLayerSerialRootedInteractionFacePreRebaseState? state factor =
      some (sourceLocalLayerSerialFaceInteractionPreRebaseStateAt graphData
        minimal caps coloring web corridor hunique offset hnext) := by
  classical
  let state := sourceLocalLayerSerialRootedInteractionStateForColorAt graphData
    minimal caps coloring web corridor hunique offset hnext prefixColor
      hprefixCrossing
  let factor :=
    (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt graphData
      minimal caps coloring web corridor hunique offset prefixColor
        hprefixCrossing cellColor hcellCrossing).2.2
  let ambientFactor :=
    (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt graphData minimal
      caps coloring web corridor hunique offset cellColor hcellCrossing).2.2
  let expected := sourceLocalLayerSerialFaceInteractionPreRebaseStateAt
    graphData minimal caps coloring web corridor hunique offset hnext
  change sourceLocalLayerSerialRootedInteractionFacePreRebaseState? state factor =
    some expected
  rw [sourceLocalLayerSerialRootedInteractionFacePreRebaseState?_congr state
    factor ambientFactor (by rfl) (by rfl)]
  exact sourceLocalLayerSerialRootedInteractionFacePreRebaseState?_at graphData
    minimal caps coloring web corridor hunique offset hnext prefixColor
      hprefixCrossing cellColor hcellCrossing

set_option maxHeartbeats 800000 in
/-- Applying the prefix-parametric finite rolling factor returns the canonical
rooted interaction state of the spliced colouring at the following cut. -/
theorem
    sourceLocalLayerSerialRootedInteractionRollingCellFactorForColorAt_successor_exact
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
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (prefixColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hprefix : ∀ edge, prefixColor edge ≠ 0)
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcompatible : SourceLocalLayerSerialCellColorsCompatibleAt corridor
      hunique offset prefixColor cellColor)
    (hcell : ∀ {edge}, edge ∈
      sourceLocalLayerCellRegionAt corridor hunique offset →
        cellColor edge ≠ 0) :
    let hprefixCrossing : ∀ step,
        prefixColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor
          hunique offset).crossingEdge step) ≠ 0 := fun step =>
      hprefix ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step)
    let state := sourceLocalLayerSerialRootedInteractionStateForColorAt
      graphData minimal caps coloring web corridor hunique offset hnext
        prefixColor hprefixCrossing
    let factor :=
      sourceLocalLayerSerialRootedInteractionRollingCellFactorForColorAt
        graphData minimal caps coloring web corridor hunique offset hnext
          hnextNext prefixColor hprefix cellColor hcell
    let splice := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
      prefixColor cellColor
    let hrole : ∀ role, splice
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
          role) ≠ 0 :=
      sourceLocalLayerSerialCellSplicedColorAt_boundaryRebaseEdge_ne_zero_of_prefix
        corridor hunique offset hnext prefixColor cellColor hprefix hcell
    let hnextCrossing := successorCrossingNonzeroForColorAt corridor hunique
      offset hnext splice hrole
    factor.successor? state = some
      (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
        caps coloring web corridor hunique
          (sourceLocalLayerNextOffset offset hnext) hnextNext splice
            hnextCrossing) := by
  classical
  dsimp only
  let hprefixCrossing : ∀ step,
      prefixColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0 := fun step =>
    hprefix ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
      offset).crossingEdge step)
  let hcross : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0 := fun step => hcell
          (sourceLocalLayerCellRegionAt_rightCrossing corridor hunique offset
            step)
  let splice := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
    prefixColor cellColor
  let hrole : ∀ role, splice
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0 :=
    sourceLocalLayerSerialCellSplicedColorAt_boundaryRebaseEdge_ne_zero_of_prefix
      corridor hunique offset hnext prefixColor cellColor hprefix hcell
  let hnextCrossing := successorCrossingNonzeroForColorAt corridor hunique
    offset hnext splice hrole
  rw [SourceLocalLayerSerialRootedInteractionRollingCellFactor.successor?]
  rw [sourceLocalLayerSerialRootedInteractionRollingCellFactorForColorAt_supportsBool
    graphData minimal caps coloring web corridor hunique offset hnext hnextNext
      prefixColor hprefix cellColor hcompatible hcell]
  simp only [if_true]
  simp only [sourceLocalLayerSerialRootedInteractionRollingCellFactorForColorAt]
  rw [sourceLocalLayerSerialRootedInteractionPreRebaseStateForColor?_at graphData
    minimal caps coloring web corridor hunique offset hnext prefixColor
      hprefixCrossing cellColor hcompatible hcross]
  simp only [Option.bind_some]
  rw [sourceLocalLayerSerialRootedInteractionFacePreRebaseStateForColor?_at
    graphData
    minimal caps coloring web corridor hunique offset hnext prefixColor
      hprefixCrossing cellColor hcross]
  simp only [Option.bind_some]
  split
  · split
    · congr 1
      apply rootedInteractionState_ext
      · apply rootedCumulativeState_ext
        · apply coloredCumulativeState_ext
          · simpa [splice, hrole, hnextCrossing] using
              (finiteBoolSupportLetterForColorAt_output_eq_nextColoredCumulativeState_input_of_prefix
                graphData minimal caps coloring web corridor hunique offset
                  hnext prefixColor hprefixCrossing cellColor hcell hrole)
          · have htargetCount :=
              sourceLocalLayerSerialTrackedRebaseFactorAt_targetCount graphData
                minimal caps coloring web corridor hunique offset hnext splice
            cases htargetCount
            dsimp only
            calc
              _ = sourceLocalLayerSerialCellRebaseUniformTrackedTargetStateAt
                    graphData caps coloring web corridor hunique offset hnext
                      splice := by
                unfold SourceLocalLayerSerialRollingProjectionFactor.trackedState
                  trackedCumulativeStateOfCode
                unfold sourceLocalLayerSerialTrackedRollingFactorAt
                funext pair
                rw [sourceLocalLayerSerialTrackedRebaseTargetStateAt_code_eq
                  graphData minimal caps coloring web corridor hunique offset
                    hnext splice pair]
                unfold sourceLocalLayerSerialCellRebaseUniformTrackedTargetStateAt
                dsimp only
                congr 1
                funext slot
                cases hslot :
                    sourceLocalLayerSerialCellRebaseTrackedTargetSlotAt graphData
                      caps coloring web corridor hunique offset hnext slot with
                | none =>
                    rfl
                | some targetSlot =>
                    simp only [Option.map_some]
                    congr 1
              _ = _ := by
                simpa [splice, hrole, hnextCrossing,
                  sourceLocalLayerSerialColoredCumulativeStateForColorAt] using
                    (sourceLocalLayerSerialCellRebaseUniformTrackedTargetStateAt_exact
                      graphData minimal caps coloring web corridor hunique offset
                        hnext splice)
          · have htargetCount :=
              sourceLocalLayerSerialFaceRebaseFactorAt_targetCount graphData
                minimal caps coloring web corridor hunique offset hnext
            cases htargetCount
            let factored :=
              sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt
                graphData minimal caps coloring web corridor hunique offset
                  prefixColor hprefixCrossing cellColor hcross
            let rebase := finiteBoolSupportLetterForColorAt corridor hunique
              offset hnext factored.2.1 splice hrole
            let next := sourceLocalLayerNextOffset offset hnext
            let FacePort := SourceLocalLayerSerialFaceInputPortAt corridor hunique
              next
            have houtputCount : rebase.output.faceFragmentCount.val =
                Fintype.card FacePort := by
              rfl
            let facePortEquiv :
                Fin rebase.output.faceFragmentCount.val ≃ FacePort :=
              (Fintype.equivFin
                  (Fin rebase.output.faceFragmentCount.val)).trans
                ((finCongr (Fintype.card_fin
                    rebase.output.faceFragmentCount.val)).trans
                  ((finCongr houtputCount).trans
                    (Fintype.equivFin FacePort).symm))
            let hfin : Fintype.card
                (Fin rebase.output.faceFragmentCount.val) ≤ 4 := by
              simpa using Nat.le_of_lt_succ
                rebase.output.faceFragmentCount.isLt
            have hportDecode : ∀ slot,
                (boundedFiniteSlot? hfin slot).map facePortEquiv =
                  sourceLocalLayerSerialFaceInputPortAtSlot? corridor hunique
                    next slot := by
              intro slot
              unfold sourceLocalLayerSerialFaceInputPortAtSlot?
              unfold boundedFiniteSlot?
              have hiff :
                  slot.val < Fintype.card
                      (Fin rebase.output.faceFragmentCount.val) ↔
                    slot.val < Fintype.card FacePort := by
                simp [houtputCount]
              split <;> rename_i hleft
              · split <;> rename_i hright
                · simp only [Option.map_some, Option.some.injEq]
                  dsimp [facePortEquiv]
                  change (Fintype.equivFin FacePort).symm _ =
                    (Fintype.equivFin FacePort).symm _
                  apply (Fintype.equivFin FacePort).injective
                  simp only [Equiv.apply_symm_apply]
                  apply Fin.ext
                  simp only [finCongr_apply, Fin.val_cast]
                · exact False.elim (hright (hiff.mp hleft))
              · split <;> rename_i hright
                · exact False.elim (hleft (hiff.mpr hright))
                · rfl
            dsimp only
            calc
              _ = sourceLocalLayerSerialCellRebaseUniformFaceTargetFullStateAt
                    graphData minimal caps coloring web corridor hunique offset
                      hnext := by
                unfold SourceLocalLayerSerialRollingProjectionFactor.faceState
                  facialCumulativeStateOfCode
                unfold sourceLocalLayerSerialFaceRollingFactorAt
                rw [sourceLocalLayerSerialFaceRebaseTargetStateAt_code_eq
                  graphData minimal caps coloring web corridor hunique offset
                    hnext]
                unfold sourceLocalLayerSerialCellRebaseUniformFaceTargetFullStateAt
                apply facePrefixAttachmentState_ext
                · unfold
                    sourceLocalLayerSerialCellRebaseUniformFaceTargetSupportedStateAt
                  dsimp only
                  rw [
                    sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_connectivity]
                  convert (pad_projectSupportedPortResidualCode_equiv
                      (sourceLocalLayerSerialCellRebaseUniformFaceTargetRawCodeAt
                        corridor hunique offset hnext)
                      (sourceLocalLayerSerialFaceTargetDartAtSlot? graphData
                        minimal caps coloring web corridor hunique offset hnext)
                      facePortEquiv (boundedFiniteSlot? hfin)
                      (sourceLocalLayerSerialFaceInputPortAtSlot? corridor
                        hunique next) hportDecode
                      (sourceLocalLayerSerialFaceTargetPortCoordinateAt corridor
                        hunique offset hnext)) using 1
                  congr 1
                  congr 1
                  funext slot
                  cases hslot :
                      sourceLocalLayerSerialFaceTargetDartAtSlot? graphData
                        minimal caps coloring web corridor hunique offset hnext
                          slot with
                  | none => rfl
                  | some targetSlot =>
                      congr 1
                · unfold
                    sourceLocalLayerSerialCellRebaseUniformFaceTargetPresentStateAt
                  dsimp only
                  funext slot
                  unfold sourceLocalLayerSerialFaceTargetDartAtSlot?
                  cases hslot :
                      sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor
                        hunique next
                        (sourceLocalLayerCellRegionAt_card_le_six graphData
                          minimal caps coloring web corridor hunique next) slot with
                  | none => rfl
                  | some dart =>
                      simp only [Option.map_some]
                      congr 1
                · unfold
                    sourceLocalLayerSerialCellRebaseUniformFaceTargetComponentCapStateAt
                  dsimp only
                  funext slot
                  unfold sourceLocalLayerSerialFaceTargetDartAtSlot?
                  cases hslot :
                      sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor
                        hunique next
                        (sourceLocalLayerCellRegionAt_card_le_six graphData
                          minimal caps coloring web corridor hunique next) slot with
                  | none => rfl
                  | some dart =>
                      simp only [Option.map_some]
                      unfold facialTargetComponentCap
                        sourceLocalLayerSerialCellRebaseUniformFaceTargetComponentCapAt
                      congr 1
              _ = _ := by
                simpa [splice, hrole, hnextCrossing,
                  sourceLocalLayerSerialColoredCumulativeStateForColorAt] using
                    (sourceLocalLayerSerialCellRebaseUniformFaceTargetFullStateAt_exact
                      graphData minimal caps coloring web corridor hunique offset
                        hnext)
          · change
              sourceLocalLayerSerialCellRebaseTransportedColorCodeForColorAt
                  graphData minimal caps coloring web corridor hunique offset
                    hnext prefixColor cellColor hrole = _
            simpa [splice, hrole, hnextCrossing,
              sourceLocalLayerSerialColoredCumulativeStateForColorAt] using
                (sourceLocalLayerSerialCellRebaseTransportedColorCodeForColorAt_eq_target_unconditional
                  graphData minimal caps coloring web corridor hunique offset
                    hnext prefixColor cellColor hrole)
          · simpa [splice, hrole, hnextCrossing,
              sourceLocalLayerSerialFaceRollingFactorAt,
              sourceLocalLayerSerialColoredCumulativeStateForColorAt] using
                (sourceLocalLayerSerialFaceRebaseTargetStateAt_eq graphData
                  minimal caps coloring web corridor hunique offset hnext)
        · simpa [splice, hrole, hnextCrossing,
            sourceLocalLayerSerialTrackedRollingFactorAt] using
              (sourceLocalLayerSerialTrackedRebaseTargetStateAt_eq graphData
                minimal caps coloring web corridor hunique offset hnext splice)
      · simpa [splice, hrole, hnextCrossing] using
          (sourceLocalLayerSerialTrackedRollingNextInteractionStateAt_eq
            graphData minimal caps coloring web corridor hunique offset hnext
              hnextNext splice hnextCrossing)
      · let interaction :=
          sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData
            caps coloring web corridor hunique offset hnext
        let next := sourceLocalLayerNextOffset offset hnext
        let nextInteraction :=
          sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData
            caps coloring web corridor hunique next hnextNext
        change
          (sourceLocalLayerSerialTrackedRollingFactorAt graphData minimal caps
              coloring web corridor hunique offset hnext hnextNext splice
            ).nextInteractionColorCode
              (sourceLocalLayerSerialTrackedInteractionColorCodeSplice
                (sourceLocalLayerSerialTrackedInteractionColorCodeAt interaction
                  (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
                    graphData minimal caps coloring web corridor hunique offset
                      hnext)
                  (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
                    offset) prefixColor)
                (sourceLocalLayerSerialTrackedInteractionColorCodeAt interaction
                  (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
                    graphData minimal caps coloring web corridor hunique offset
                      hnext)
                  (sourceLocalLayerCellRegionAt corridor hunique offset)
                  cellColor))
              (successorTrackedStateForColorAt corridor hunique offset hnext
                splice hrole).roleColor =
            sourceLocalLayerSerialTrackedInteractionColorCodeAt nextInteraction
              (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
                graphData minimal caps coloring web corridor hunique next
                  hnextNext)
              (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique next)
              splice
        rw [sourceLocalLayerSerialTrackedInteractionColorCodeSpliceAt_eq
          corridor hunique offset interaction
            (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
              graphData minimal caps coloring web corridor hunique offset hnext)
          prefixColor cellColor]
        exact
          sourceLocalLayerSerialTrackedRollingNextInteractionColorCodeAt_eq
            graphData minimal caps coloring web corridor hunique offset hnext
              hnextNext splice hrole
      · apply heq_of_eq
        simpa [splice, hrole, hnextCrossing,
          SourceLocalLayerSerialTrackedRebaseFactor.targetState,
          SourceLocalLayerSerialTrackedRollingFactor.nextInteractionState] using
          (sourceLocalLayerSerialTrackedRollingFactorAt_nextCurrentCoordinate_eq
            graphData minimal caps coloring web corridor hunique offset hnext
              hnextNext splice hnextCrossing)
      · simpa [splice, hrole, hnextCrossing] using
          (sourceLocalLayerSerialFaceRollingNextInteractionStateAt_eq graphData
            minimal caps coloring web corridor hunique offset hnext hnextNext
              splice hnextCrossing)
      · apply heq_of_eq
        simpa [splice, hrole, hnextCrossing,
          SourceLocalLayerSerialFaceRebaseFactor.targetState,
          SourceLocalLayerSerialFaceRollingFactor.nextInteractionState] using
          (sourceLocalLayerSerialFaceRollingFactorAt_nextCurrentCoordinate_eq
            graphData minimal caps coloring web corridor hunique offset hnext
              hnextNext splice hnextCrossing)
    · rename_i hface
      exfalso
      apply hface
      rfl
  · rename_i htracked
    exfalso
    apply htracked
    rfl

end

end GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingTransitionColorParametric

end Mettapedia.GraphTheory.FourColor
