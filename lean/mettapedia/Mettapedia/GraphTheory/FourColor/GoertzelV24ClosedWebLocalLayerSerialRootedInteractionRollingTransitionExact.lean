import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingTransition
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseSupportColorParametric
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformFullSuccessorState

/-!
# Source exactness of the rooted rolling Cell transition

This file constructs the single finite rolling factor associated to a literal
positive Cell and its following boundary rebase.  The construction uses two
consecutive interior rebase positions because the output state already carries
the bounded lookahead root for the following transition.

All changes of representation are explicit finite coordinate maps.  The main
exactness theorem identifies application of this graph-free factor with the
canonical rooted interaction state of the spliced colouring at the next cut.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingTransitionExact

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseSupportColorParametric
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseOutputColorParametric
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStableParametricCapState
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteColorCompatibility
open GoertzelV24ClosedWebLocalLayerSerialCellNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellPastOverlap
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseCarrierTransport
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellStateFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFullSuccessorState
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetFullState
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetComponentCap
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCode
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCap
open GoertzelV24ClosedWebLocalLayerSerialCellUniformTrackedTargetCode
open GoertzelV24ClosedWebLocalLayerSerialColoredCumulativeStateForColor
open GoertzelV24ClosedWebLocalLayerSerialRootedCumulativeState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFacePreRebaseExact
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFacePreRebaseState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceRollingExact
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceRollingSuccessor
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceSuccessor
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPreRebaseState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingProjection
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingProjectionFactor
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingSuccessor
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingTransition
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionTrackedSuccessor
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24FramedTrail
open GoertzelV24InterfaceExteriorSupportedPortProjection
open GoertzelV24MinimalFacialPentagonCapPairLocalCellCarrier
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance rollingTransitionExactEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance rollingTransitionExactOpenedGraphDecidableRel
    {graphData : Data G}
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

private theorem cumulativeState_ext
    (left right : SourceLocalLayerSerialCumulativeState)
    (hinput : left.input = right.input)
    (htracked : left.tracked = right.tracked)
    (hface : left.face = right.face) :
    left = right := by
  cases left
  cases right
  simp_all

private theorem coloredCumulativeState_ext
    (left right : SourceLocalLayerSerialColoredCumulativeState)
    (hinput : left.input = right.input)
    (htracked : left.tracked = right.tracked)
    (hface : left.face = right.face)
    (hcolor : left.colorCode = right.colorCode)
    (hcap : left.faceCapSix = right.faceCapSix) :
    left = right := by
  cases left with
  | mk leftCumulative leftColor leftCap =>
    cases right with
    | mk rightCumulative rightColor rightCap =>
      have hcumulative : leftCumulative = rightCumulative :=
        cumulativeState_ext leftCumulative rightCumulative hinput htracked hface
      subst rightCumulative
      simp_all

private theorem rootedCumulativeState_ext
    (left right : SourceLocalLayerSerialRootedCumulativeState)
    (hcolored :
      left.toSourceLocalLayerSerialColoredCumulativeState =
        right.toSourceLocalLayerSerialColoredCumulativeState)
    (htracked : left.trackedExterior = right.trackedExterior) :
    left = right := by
  cases left
  cases right
  simp_all

private theorem facePrefixAttachmentState_ext
    (left right : SourceLocalLayerSerialFacePrefixAttachmentState)
    (hsupported : left.toBoundedSupportedPortResidualCode =
      right.toBoundedSupportedPortResidualCode)
    (hpresent : left.interfacePresent = right.interfacePresent)
    (hcap : left.componentCap = right.componentCap) :
    left = right := by
  cases left
  cases right
  simp_all

private theorem rootedInteractionState_ext
    (left right : SourceLocalLayerSerialRootedInteractionState)
    (hrooted : left.toSourceLocalLayerSerialRootedCumulativeState =
      right.toSourceLocalLayerSerialRootedCumulativeState)
    (hinteraction : left.interactionExterior = right.interactionExterior)
    (hcurrent : HEq left.currentCoordinate right.currentCoordinate)
    (hfaceInteraction :
      left.faceInteractionExterior = right.faceInteractionExterior)
    (hfaceCurrent : HEq left.faceCurrentCoordinate right.faceCurrentCoordinate) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Projecting and then padding persistent ports is invariant under a finite
change of port coordinates, provided the two partial stable decoders agree. -/
private theorem pad_projectSupportedPortResidualCode_equiv
    {Full Port EncodedPort Stable StablePort : Type*}
    [Fintype Full] [Fintype Port] [Fintype EncodedPort]
    (code :
      GoertzelV24InterfaceDeletionComponentFactor.BoundedInterfaceExteriorCode
        Full)
    (decode : Stable → Option Full)
    (portEquiv : EncodedPort ≃ Port)
    (decodeEncoded : StablePort → Option EncodedPort)
    (decodePort : StablePort → Option Port)
    (hdecode : ∀ slot, (decodeEncoded slot).map portEquiv = decodePort slot)
    (portCoordinate : Port → Full) :
    padSupportedPortResidualCodePorts decodeEncoded
        (projectSupportedPortResidualCode code decode
          (fun port => portCoordinate (portEquiv port))) =
      padSupportedPortResidualCodePorts decodePort
        (projectSupportedPortResidualCode code decode portCoordinate) := by
  classical
  apply boundedSupportedPortResidualCode_ext
  · funext stable port
    dsimp only [padSupportedPortResidualCodePorts]
    rw [← hdecode port]
    cases decodeEncoded port <;> rfl
  · funext left right
    dsimp only [padSupportedPortResidualCodePorts,
      projectSupportedPortResidualCode]
    cases hleft : decode left <;> cases hright : decode right
    · rfl
    · rfl
    · rfl
    · apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨hreach, hports⟩
        refine ⟨hreach, fun port => ?_⟩
        simpa using hports (portEquiv.symm port)
      · rintro ⟨hreach, hports⟩
        refine ⟨hreach, fun port => ?_⟩
        exact hports (portEquiv port)
  · rfl
  · funext port
    dsimp only [padSupportedPortResidualCodePorts]
    rw [← hdecode port]
    cases decodeEncoded port <;> rfl

/-- The literal finite factor for a compatible positive Cell, its boundary
rebase, and the one-step rolling lookahead needed by the output root. -/
noncomputable def sourceLocalLayerSerialRootedInteractionRollingCellFactorAt
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
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcell : ∀ {edge}, edge ∈
      sourceLocalLayerCellRegionAt corridor hunique offset →
        cellColor edge ≠ 0) :
    SourceLocalLayerSerialRootedInteractionRollingCellFactor := by
  classical
  let hcross : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0 := fun step => hcell
          (sourceLocalLayerCellRegionAt_rightCrossing corridor hunique offset
            step)
  let factored := sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
    graphData minimal caps coloring web corridor hunique offset cellColor hcross
  let splice := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
    coloring cellColor
  let hrole : ∀ role, splice
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0 :=
    sourceLocalLayerSerialCellSplicedColorAt_boundaryRebaseEdge_ne_zero
      corridor hunique offset hnext cellColor hcell
  let rebase := finiteBoolSupportLetterForColorAt corridor hunique offset hnext
    factored.2.1 splice hrole
  let trackedRolling := sourceLocalLayerSerialTrackedRollingFactorAt graphData
    minimal caps coloring web corridor hunique offset hnext hnextNext splice
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
    rebaseLetter := rebase
    trackedRolling := trackedRolling
    faceRolling := faceRolling
    projection := projection }

/-- A compatible literal source Cell makes the endpoint-support guard of its
finite rolling factor true. -/
theorem sourceLocalLayerSerialRootedInteractionRollingCellFactorAt_supportsBool
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
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcompatible : SourceLocalLayerSerialCellColorsCompatibleAt corridor
      hunique offset coloring cellColor)
    (hcell : ∀ {edge}, edge ∈
      sourceLocalLayerCellRegionAt corridor hunique offset →
        cellColor edge ≠ 0) :
    let state := sourceLocalLayerSerialRootedInteractionStateForColorAt
      graphData minimal caps coloring web corridor hunique offset hnext coloring
        (fun _ => web.tait _)
    let factor := sourceLocalLayerSerialRootedInteractionRollingCellFactorAt
      graphData minimal caps coloring web corridor hunique offset hnext
        hnextNext cellColor hcell
    factor.supportsBool state = true := by
  classical
  dsimp only
  let hcross : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0 := fun step => hcell
          (sourceLocalLayerCellRegionAt_rightCrossing corridor hunique offset
            step)
  let factored := sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
    graphData minimal caps coloring web corridor hunique offset cellColor hcross
  let splice := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
    coloring cellColor
  let hrole : ∀ role, splice
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0 :=
    sourceLocalLayerSerialCellSplicedColorAt_boundaryRebaseEdge_ne_zero
      corridor hunique offset hnext cellColor hcell
  rw [SourceLocalLayerSerialRootedInteractionRollingCellFactor.supportsBool,
    Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · let state := sourceLocalLayerSerialRootedInteractionStateForColorAt
      graphData minimal caps coloring web corridor hunique offset hnext coloring
        (fun _ => web.tait _)
    have hstate : state.toSourceLocalLayerSerialColoredCumulativeState =
        factored.1 := by
      calc
        _ = (sourceLocalLayerSerialRootedCumulativeStateForColorAt graphData
              minimal caps coloring web corridor hunique offset coloring
                (fun _ => web.tait _)
            ).toSourceLocalLayerSerialColoredCumulativeState := by
              rw [sourceLocalLayerSerialRootedInteractionStateForColorAt_toRooted]
        _ = factored.1 :=
          sourceLocalLayerSerialRootedCumulativeStateForColorAt_ambient_eq_factored_input
            graphData minimal caps coloring web corridor hunique offset
              cellColor hcross
    change SourceLocalLayerSerialCellPhysicalSupportsBool
      state.toSourceLocalLayerSerialColoredCumulativeState factored.2.1
        factored.2.2 = true
    rw [hstate]
    exact
      (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt_supports graphData
        minimal caps coloring web corridor hunique offset cellColor hcompatible
          hcross)
  · change decide
      ((finiteBoolSupportLetterForColorAt corridor hunique offset hnext
        factored.2.1 splice hrole).input = factored.2.1) = true
    simp [finiteBoolSupportLetterForColorAt]
  · simpa [sourceLocalLayerSerialRootedInteractionRollingCellFactorAt, hcross,
      factored, splice, hrole] using
      (finiteBoolSupportLetterForColorAt_supports corridor hunique offset hnext
        factored.2.1 splice hrole)

set_option maxHeartbeats 800000 in
/-- Applying the literal finite rolling factor returns the canonical rooted
interaction state of the spliced colouring at the following cut. -/
theorem sourceLocalLayerSerialRootedInteractionRollingCellFactorAt_successor_exact
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
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcompatible : SourceLocalLayerSerialCellColorsCompatibleAt corridor
      hunique offset coloring cellColor)
    (hcell : ∀ {edge}, edge ∈
      sourceLocalLayerCellRegionAt corridor hunique offset →
        cellColor edge ≠ 0) :
    let state := sourceLocalLayerSerialRootedInteractionStateForColorAt
      graphData minimal caps coloring web corridor hunique offset hnext coloring
        (fun _ => web.tait _)
    let factor := sourceLocalLayerSerialRootedInteractionRollingCellFactorAt
      graphData minimal caps coloring web corridor hunique offset hnext
        hnextNext cellColor hcell
    let splice := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
      coloring cellColor
    let hrole : ∀ role, splice
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
          role) ≠ 0 :=
      sourceLocalLayerSerialCellSplicedColorAt_boundaryRebaseEdge_ne_zero
        corridor hunique offset hnext cellColor hcell
    let hnextCrossing := successorCrossingNonzeroForColorAt corridor hunique
      offset hnext splice hrole
    factor.successor? state = some
      (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
        caps coloring web corridor hunique
          (sourceLocalLayerNextOffset offset hnext) hnextNext splice
            hnextCrossing) := by
  classical
  dsimp only
  let hcross : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0 := fun step => hcell
          (sourceLocalLayerCellRegionAt_rightCrossing corridor hunique offset
            step)
  let splice := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
    coloring cellColor
  let hrole : ∀ role, splice
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0 :=
    sourceLocalLayerSerialCellSplicedColorAt_boundaryRebaseEdge_ne_zero
      corridor hunique offset hnext cellColor hcell
  let hnextCrossing := successorCrossingNonzeroForColorAt corridor hunique
    offset hnext splice hrole
  rw [SourceLocalLayerSerialRootedInteractionRollingCellFactor.successor?]
  rw [sourceLocalLayerSerialRootedInteractionRollingCellFactorAt_supportsBool
    graphData minimal caps coloring web corridor hunique offset hnext hnextNext
      cellColor hcompatible hcell]
  simp only [if_true]
  simp only [sourceLocalLayerSerialRootedInteractionRollingCellFactorAt]
  rw [sourceLocalLayerSerialRootedInteractionPreRebaseState?_at graphData
    minimal caps coloring web corridor hunique offset hnext cellColor
      hcompatible hcross]
  simp only [Option.bind_some]
  rw [sourceLocalLayerSerialRootedInteractionFacePreRebaseState?_at graphData
    minimal caps coloring web corridor hunique offset hnext coloring
      (fun _ => web.tait _) cellColor hcross]
  simp only [Option.bind_some]
  split
  · split
    · congr 1
      apply rootedInteractionState_ext
      · apply rootedCumulativeState_ext
        · apply coloredCumulativeState_ext
          · simpa [splice, hrole, hnextCrossing,
              sourceLocalLayerSerialCellRebaseNextColoredCumulativeStateAt]
              using
                (finiteBoolSupportLetterForColorAt_output_eq_nextColoredCumulativeState_input
                  graphData minimal caps coloring web corridor hunique offset
                    hnext cellColor hcell)
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
                  sourceLocalLayerSerialCellRebaseNextColoredCumulativeStateAt,
                  sourceLocalLayerSerialColoredCumulativeStateForColorAt] using
                    (sourceLocalLayerSerialCellRebaseUniformTrackedTargetStateAt_exact
                      graphData minimal caps coloring web corridor hunique offset
                        hnext splice)
          · have htargetCount :=
              sourceLocalLayerSerialFaceRebaseFactorAt_targetCount graphData
                minimal caps coloring web corridor hunique offset hnext
            cases htargetCount
            let factored := sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
              graphData minimal caps coloring web corridor hunique offset
                cellColor hcross
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
                  sourceLocalLayerSerialCellRebaseNextColoredCumulativeStateAt,
                  sourceLocalLayerSerialColoredCumulativeStateForColorAt] using
                    (sourceLocalLayerSerialCellRebaseUniformFaceTargetFullStateAt_exact
                      graphData minimal caps coloring web corridor hunique offset
                        hnext)
          · change
              sourceLocalLayerSerialCellRebaseTransportedColorCodeAt graphData
                  minimal caps coloring web corridor hunique offset hnext
                    cellColor hcell = _
            simpa [splice, hrole, hnextCrossing,
              sourceLocalLayerSerialCellRebaseNextColoredCumulativeStateAt,
              sourceLocalLayerSerialColoredCumulativeStateForColorAt] using
                (sourceLocalLayerSerialCellRebaseTransportedColorCodeAt_eq_target_unconditional
                  graphData minimal caps coloring web corridor hunique offset
                    hnext cellColor hcell)
          · simpa [splice, hrole, hnextCrossing,
              sourceLocalLayerSerialFaceRollingFactorAt,
              sourceLocalLayerSerialCellRebaseNextColoredCumulativeStateAt,
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

end GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingTransitionExact

end Mettapedia.GraphTheory.FourColor
