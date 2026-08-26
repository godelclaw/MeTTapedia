import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetComponentCap

/-!
# Package the complete rolling facial successor state

The exact rolling target code already supplies the supported residual fields
on the canonical twenty-four-slot carrier.  Its literal-presence bit and its
full-component cap are indexed first by the actual target carrier, so this
file transports those two fields through the same canonical slot decoder.
The resulting finite value is exactly the next cumulative facial state.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetFullState

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCap
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCode
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetComponentCap
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24FramedTrail
open GoertzelV24MinimalFacialPentagonCapPairLocalCellCarrier
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance uniformFaceTargetFullStateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance uniformFaceTargetFullStateOpenedGraphDecidableRel
    {graphData : Data G}
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

private theorem cappedState_ext
    {Interface Port : Type*}
    (left right : BoundedCappedSupportedPortResidualCode Interface Port)
    (hsupported : left.toBoundedSupportedPortResidualCode =
      right.toBoundedSupportedPortResidualCode)
    (hpresent : left.interfacePresent = right.interfacePresent)
    (hcap : left.componentCap = right.componentCap) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Pad literal target presence from the actual rolling carrier onto the
canonical twenty-four facial slots. -/
noncomputable def sourceLocalLayerSerialCellRebaseUniformFaceTargetPresentStateAt
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
    Fin 24 → Bool :=
  let next := sourceLocalLayerNextOffset offset hnext
  let hcell := sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps
    coloring web corridor hunique next
  let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    next
  let code :=
    sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt
      graphData minimal caps coloring web corridor hunique offset hnext
  fun slot =>
    match sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor hunique next
        hcell slot with
    | none => false
    | some dart => code.interfacePresent (carrierCoordinate target dart)

/-- Pad exact target full-component caps onto the canonical twenty-four
facial slots. -/
noncomputable def sourceLocalLayerSerialCellRebaseUniformFaceTargetComponentCapStateAt
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
    Fin 24 → Fin 6 :=
  let next := sourceLocalLayerNextOffset offset hnext
  let hcell := sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps
    coloring web corridor hunique next
  let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    next
  fun slot =>
    match sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor hunique next
        hcell slot with
    | none => 0
    | some dart =>
        sourceLocalLayerSerialCellRebaseUniformFaceTargetComponentCapAt
          graphData minimal caps coloring web corridor hunique offset hnext
            (carrierCoordinate target dart)

/-- The padded presence field is exactly the next source state's literal
presence field. -/
theorem sourceLocalLayerSerialCellRebaseUniformFaceTargetPresentStateAt_exact
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
    let next := sourceLocalLayerNextOffset offset hnext
    let hcell := sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps
      coloring web corridor hunique next
    sourceLocalLayerSerialCellRebaseUniformFaceTargetPresentStateAt graphData
        minimal caps coloring web corridor hunique offset hnext =
      (sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor hunique next
        hcell).interfacePresent := by
  classical
  dsimp only
  let next := sourceLocalLayerNextOffset offset hnext
  let hcell := sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps
    coloring web corridor hunique next
  let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    next
  let decode := sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor hunique
    next hcell
  funext slot
  change (match decode slot with
    | none => false
    | some dart =>
        (sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt
          graphData minimal caps coloring web corridor hunique offset hnext
          ).interfacePresent (carrierCoordinate target dart)) = _
  cases hdecode : decode slot with
  | none =>
      have hdecode' :
          sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor hunique next
              hcell slot = none := by
        simpa [decode] using hdecode
      have hdecode'' :
          sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor hunique
              (sourceLocalLayerNextOffset offset hnext)
              (sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps
                coloring web corridor hunique
                  (sourceLocalLayerNextOffset offset hnext)) slot = none := by
        simpa [next, hcell] using hdecode'
      simp [sourceLocalLayerSerialFacePrefixAttachmentStateAt,
        padCappedSupportedPortResidualCodePorts,
        padCappedSupportedPortResidualCode, hdecode'']
  | some dart =>
      have hdecode' :
          sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor hunique next
              hcell slot = some dart := by
        simpa [decode] using hdecode
      have hslot :=
        (sourceLocalLayerSerialFaceTransitionDartAtSlot?_eq_some_iff corridor
          hunique next hcell slot dart).1 hdecode'
      subst slot
      rw [sourceLocalLayerSerialFacePrefixAttachmentStateAt_interfacePresent]
      apply Bool.eq_iff_iff.mpr
      rw [sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_interfacePresent_iff]
      simp [target, next]

/-- The padded cap field is exactly the next source state's cap-at-five field. -/
theorem sourceLocalLayerSerialCellRebaseUniformFaceTargetComponentCapStateAt_exact
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
    let next := sourceLocalLayerNextOffset offset hnext
    let hcell := sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps
      coloring web corridor hunique next
    sourceLocalLayerSerialCellRebaseUniformFaceTargetComponentCapStateAt
        graphData minimal caps coloring web corridor hunique offset hnext =
      (sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor hunique next
        hcell).componentCap := by
  classical
  dsimp only
  let next := sourceLocalLayerNextOffset offset hnext
  let hcell := sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps
    coloring web corridor hunique next
  let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    next
  let decode := sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor hunique
    next hcell
  funext slot
  change (match decode slot with
    | none => 0
    | some dart =>
        sourceLocalLayerSerialCellRebaseUniformFaceTargetComponentCapAt
          graphData minimal caps coloring web corridor hunique offset hnext
            (carrierCoordinate target dart)) = _
  cases hdecode : decode slot with
  | none =>
      have hdecode' :
          sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor hunique next
              hcell slot = none := by
        simpa [decode] using hdecode
      have hdecode'' :
          sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor hunique
              (sourceLocalLayerNextOffset offset hnext)
              (sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps
                coloring web corridor hunique
                  (sourceLocalLayerNextOffset offset hnext)) slot = none := by
        simpa [next, hcell] using hdecode'
      simp [sourceLocalLayerSerialFacePrefixAttachmentStateAt,
        padCappedSupportedPortResidualCodePorts,
        padCappedSupportedPortResidualCode, hdecode'']
  | some dart =>
      have hdecode' :
          sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor hunique next
              hcell slot = some dart := by
        simpa [decode] using hdecode
      have hslot :=
        (sourceLocalLayerSerialFaceTransitionDartAtSlot?_eq_some_iff corridor
          hunique next hcell slot dart).1 hdecode'
      subst slot
      have hcap :=
        sourceLocalLayerSerialCellRebaseUniformFaceTargetComponentCapAt_exact
          graphData minimal caps coloring web corridor hunique offset hnext
            (carrierCoordinate target dart)
      rw [sourceLocalLayerSerialFacePrefixAttachmentStateAt_componentCap]
      simpa [target, next] using hcap

/-- Complete graph-free facial output of one literal Cell rebase. -/
noncomputable def sourceLocalLayerSerialCellRebaseUniformFaceTargetFullStateAt
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
    SourceLocalLayerSerialFacePrefixAttachmentState where
  toBoundedSupportedPortResidualCode :=
    sourceLocalLayerSerialCellRebaseUniformFaceTargetSupportedStateAt graphData
      minimal caps coloring web corridor hunique offset hnext
  interfacePresent :=
    sourceLocalLayerSerialCellRebaseUniformFaceTargetPresentStateAt graphData
      minimal caps coloring web corridor hunique offset hnext
  componentCap :=
    sourceLocalLayerSerialCellRebaseUniformFaceTargetComponentCapStateAt
      graphData minimal caps coloring web corridor hunique offset hnext

/-- The complete finite facial output is exactly the canonical next
cumulative facial state. -/
theorem sourceLocalLayerSerialCellRebaseUniformFaceTargetFullStateAt_exact
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
    let next := sourceLocalLayerNextOffset offset hnext
    let hcell := sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps
      coloring web corridor hunique next
    sourceLocalLayerSerialCellRebaseUniformFaceTargetFullStateAt graphData minimal
        caps coloring web corridor hunique offset hnext =
      sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor hunique next
        hcell := by
  dsimp only
  let result := sourceLocalLayerSerialCellRebaseUniformFaceTargetFullStateAt
    graphData minimal caps coloring web corridor hunique offset hnext
  let expected := sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor
    hunique (sourceLocalLayerNextOffset offset hnext)
      (sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps coloring
        web corridor hunique (sourceLocalLayerNextOffset offset hnext))
  change result = expected
  have hsupported : result.toBoundedSupportedPortResidualCode =
      expected.toBoundedSupportedPortResidualCode := by
    exact
      sourceLocalLayerSerialCellRebaseUniformFaceTargetSupportedStateAt_exact
        graphData minimal caps coloring web corridor hunique offset hnext
  have hpresent : result.interfacePresent = expected.interfacePresent := by
    exact
      sourceLocalLayerSerialCellRebaseUniformFaceTargetPresentStateAt_exact
        graphData minimal caps coloring web corridor hunique offset hnext
  have hcap : result.componentCap = expected.componentCap := by
    exact
      sourceLocalLayerSerialCellRebaseUniformFaceTargetComponentCapStateAt_exact
        graphData minimal caps coloring web corridor hunique offset hnext
  exact cappedState_ext result expected hsupported hpresent hcap

end

end GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetFullState

end Mettapedia.GraphTheory.FourColor
