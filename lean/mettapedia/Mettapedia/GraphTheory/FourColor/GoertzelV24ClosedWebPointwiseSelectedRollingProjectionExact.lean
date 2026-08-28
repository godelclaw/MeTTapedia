import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedCarrierTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedCellNativeFactorization
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedCellRebaseFiniteTransition
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedBoundaryRebaseFiniteReceipt
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedRollingTrackedSuccessor
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFaceRollingExact
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedTrackedTargetCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedTrackedPrefixAttachmentState
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFaceTargetCapExact
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFacePrefixAttachmentState
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingProjectionFactor
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceExteriorLabelCapFullComponent

/-!
# Exact fixed-slot projection for the selected rolling transition

The selected rolling recurrences compute their target codes on literal
dependent carriers.  The cumulative machine instead uses fixed twenty-one
edge slots, twenty-four dart slots, and four facial-fragment slots.  This file
constructs the finite coordinate receipt between those presentations and
proves its three projections exact.

The receipt contains only finite functions.  Source geometry occurs here only
to prove that the literal receipt is one of its finitely many inhabitants and
that applying it recovers the canonical next cumulative state.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedRollingProjectionExact

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStableParametricCapState
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputCap
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteColorCompatibility
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteTrackedColorCode
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseCarrierTransport
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingProjection
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingProjectionFactor
open GoertzelV24ClosedWebPointwiseSelectedCarrierTransport
open GoertzelV24ClosedWebPointwiseSelectedCellNativeFactorization
open GoertzelV24ClosedWebPointwiseSelectedCellRebaseFiniteTransition
open GoertzelV24ClosedWebPointwiseSelectedFaceRollingSuccessor
open GoertzelV24ClosedWebPointwiseSelectedFaceSuccessor
open GoertzelV24ClosedWebPointwiseSelectedFaceTargetCap
open GoertzelV24ClosedWebPointwiseSelectedFaceTargetCapExact
open GoertzelV24ClosedWebPointwiseSelectedFaceTargetCode
open GoertzelV24ClosedWebPointwiseSelectedFaceUniformRecurrence
open GoertzelV24ClosedWebPointwiseSelectedRollingTrackedSuccessor
open GoertzelV24ClosedWebPointwiseSelectedTrackedUniformRecurrence
open GoertzelV24ClosedWebPointwiseSelectedTrackedRebaseFactor
open GoertzelV24ClosedWebPointwiseSelectedTrackedTargetCode
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceDualConnectedness
open GoertzelV24FacialPentagonCap
open GoertzelV24FramedTrail
open GoertzelV24GraphDerivedTerminalProfile
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24InterfaceExteriorSupportedPortProjection
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24InterfaceExteriorLabelCapFullComponent
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open GoertzelV24MinimalFacialPentagonCapPairPointwiseSelectedLocalCellCarrier
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceRegionalDartCarrier
open GoertzelV24RotationFaceRegionalDartGraph
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationFaceInterfaceExteriorLabelCap
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedRollingProjectionOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

local instance pointwiseSelectedRollingProjectionIncidenceLinearOrder
    {n : Nat} : LinearOrder (Fin n × Bool) :=
  LinearOrder.lift' (fun incidence : Fin n × Bool ↦ toLex incidence)
    toLex.injective

/-! ## Literal next-port coordinates -/

/-- A persistent tracked port, represented on the literal next carrier. -/
noncomputable def
    pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedTargetPortEdgeAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (port : CorridorPort 2 1) :
    {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)} := by
  let next := sourceLocalLayerNextOffset offset hnext
  rcases port with crossing | terminal
  · refine ⟨pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
      corridor hinterior next crossing, ?_⟩
    exact Finset.mem_union_left _ <| Finset.mem_union_left _ <|
      pointwiseSelectedSourceLocalLayerCellRegionAt_leftCrossing web.toFormation
        corridor hinterior next crossing
  · refine ⟨pointwiseSelectedSourceLocalLayerSharedRungAt web.toFormation
      corridor hinterior next, ?_⟩
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

@[simp]
theorem
    pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedTargetPortEdgeAt_val
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (port : CorridorPort 2 1) :
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedTargetPortEdgeAt
      web corridor hinterior offset hnext port).1 =
      (pointwiseSelectedSourceLocalLayerSerialTerminalInputCutDataAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)).portEdge port := by
  rcases port with crossing | terminal <;> rfl

set_option maxHeartbeats 800000 in
/-- The distinguished occurrence of a next input fragment lies in the next
facial transition carrier. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceTargetPortDartAt_mem
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (port : PointwiseSelectedSourceLocalLayerSerialFaceInputPortAt
      web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext)) :
    (boundaryRegionalFragmentDartOccurrence web.annular.RS
        (indexedCrossingEdgeSet
          (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
            corridor hinterior (sourceLocalLayerNextOffset offset hnext)))
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
          web.toFormation corridor hinterior
            (sourceLocalLayerNextOffset offset hnext)) port).1 ∈
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext) := by
  let next := sourceLocalLayerNextOffset offset hnext
  let dart := boundaryRegionalFragmentDartOccurrence web.annular.RS
    (indexedCrossingEdgeSet
      (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation corridor
        hinterior next))
    (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
      web.toFormation corridor hinterior next) port
  apply Finset.mem_union_left _
  apply (mem_dartsOnEdges_iff web.annular.RS _ dart.1).2
  rcases (mem_indexedCrossingEdgeSet_iff
      (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation corridor
        hinterior next) (web.annular.RS.edgeOf dart.1)).1 dart.2 with
    ⟨step, hstep⟩
  rw [← hstep]
  exact pointwiseSelectedSourceLocalLayerCellRegionAt_leftCrossing
    web.toFormation corridor hinterior next step

/-- An actual next input-fragment port as a target-carrier dart. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialFaceTargetPortDartAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (port : PointwiseSelectedSourceLocalLayerSerialFaceInputPortAt
      web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext)) :
    {dart // dart ∈
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)} :=
  ⟨(boundaryRegionalFragmentDartOccurrence web.annular.RS
      (indexedCrossingEdgeSet
        (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
          corridor hinterior (sourceLocalLayerNextOffset offset hnext)))
      (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)) port).1,
    pointwiseSelectedSourceLocalLayerSerialFaceTargetPortDartAt_mem web corridor
      hinterior offset hnext port⟩

/-- Coordinate of an actual next input-fragment port. -/
noncomputable def
    pointwiseSelectedSourceLocalLayerSerialFaceTargetPortCoordinateAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    PointwiseSelectedSourceLocalLayerSerialFaceInputPortAt web.toFormation
        corridor hinterior (sourceLocalLayerNextOffset offset hnext) →
      Fin (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)).card :=
  fun port => carrierCoordinate
    (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
      web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext))
    (pointwiseSelectedSourceLocalLayerSerialFaceTargetPortDartAt web corridor
      hinterior offset hnext port)

/-! ## The finite selected projection receipt -/

/-- Literal finite fixed-slot projection for one selected Cell--rebase--roll
step. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialRollingProjectionFactorAt
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
    (prefixColor : PointwiseSelectedPositiveColorFunction
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet)
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt
        web.toFormation corridor hinterior offset) :
    let factored :=
      pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
        web corridor hinterior offset hnext hcell prefixColor.1
          (fun step => prefixColor.2
            (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
              corridor hinterior offset step)) cellColoring
    let cellColor :=
      pointwiseSelectedSourceLocalLayerCellLiteralColorAt web.toFormation
        corridor hinterior offset cellColoring
    let splice :=
      pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt web.toFormation
        corridor hinterior offset prefixColor.1 cellColor
    let hrole : ∀ role, splice
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt web.toFormation
          corridor hinterior offset hnext role) ≠ 0 :=
      pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_boundaryRebaseEdge_ne_zero
        web.toFormation corridor hinterior offset hnext prefixColor.1
          prefixColor.2 cellColoring
    let rebase :=
      pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedSupportLetterForColorAt
        web.toFormation corridor hinterior offset hnext factored.2.1 splice
          hrole
    let next := sourceLocalLayerNextOffset offset hnext
    let hcellNext :=
      pointwiseSelectedSourceLocalLayerCellRegionAt_card_le_six graphData minimal
        caps coloring web corridor hinterior next
    let trackedRolling :=
      pointwiseSelectedSourceLocalLayerSerialTrackedRollingFactorAt web corridor
        hinterior offset hnext hnextNext hcell hcellNext splice
    let faceRolling :=
      pointwiseSelectedSourceLocalLayerSerialFaceRollingFactorAt graphData
        minimal caps coloring web corridor hinterior offset hnext hnextNext
    SourceLocalLayerSerialRollingProjectionFactor
      trackedRolling.rebase.targetCount faceRolling.rebase.targetCount
        rebase.output.faceFragmentCount := by
  classical
  dsimp only
  let factored :=
    pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt web
      corridor hinterior offset hnext hcell prefixColor.1
        (fun step => prefixColor.2
          (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
            corridor hinterior offset step)) cellColoring
  let cellColor :=
    pointwiseSelectedSourceLocalLayerCellLiteralColorAt web.toFormation corridor
      hinterior offset cellColoring
  let splice :=
    pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt web.toFormation
      corridor hinterior offset prefixColor.1 cellColor
  let hrole : ∀ role, splice
      (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt web.toFormation
        corridor hinterior offset hnext role) ≠ 0 :=
    pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_boundaryRebaseEdge_ne_zero
      web.toFormation corridor hinterior offset hnext prefixColor.1
        prefixColor.2 cellColoring
  let rebase :=
    pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedSupportLetterForColorAt
      web.toFormation corridor hinterior offset hnext factored.2.1 splice hrole
  let next := sourceLocalLayerNextOffset offset hnext
  let hcellNext :=
    pointwiseSelectedSourceLocalLayerCellRegionAt_card_le_six graphData minimal
      caps coloring web corridor hinterior next
  let trackedRolling :=
    pointwiseSelectedSourceLocalLayerSerialTrackedRollingFactorAt web corridor
      hinterior offset hnext hnextNext hcell hcellNext splice
  let faceRolling :=
    pointwiseSelectedSourceLocalLayerSerialFaceRollingFactorAt graphData minimal
      caps coloring web corridor hinterior offset hnext hnextNext
  let trackedTarget :=
    pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
      web.toFormation corridor hinterior next
  let faceTarget :=
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
      web.toFormation corridor hinterior next
  let FacePort := PointwiseSelectedSourceLocalLayerSerialFaceInputPortAt
    web.toFormation corridor hinterior next
  have htrackedTarget : trackedRolling.rebase.targetCount.val =
      trackedTarget.card := by rfl
  have hfaceTarget : faceRolling.rebase.targetCount.val = faceTarget.card := by
    rfl
  have houtputCount : rebase.output.faceFragmentCount.val =
      Fintype.card FacePort := by rfl
  let facePortEquiv : Fin rebase.output.faceFragmentCount.val ≃ FacePort :=
    (Fintype.equivFin (Fin rebase.output.faceFragmentCount.val)).trans
      ((finCongr (Fintype.card_fin rebase.output.faceFragmentCount.val)).trans
        ((finCongr houtputCount).trans (Fintype.equivFin FacePort).symm))
  exact {
    trackedSlot := fun slot =>
      (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionEdgeAtSlot?
        web.toFormation corridor hinterior next slot).map fun edge =>
          Fin.cast htrackedTarget.symm (carrierCoordinate trackedTarget edge)
    trackedPortCoordinate := fun port => Fin.cast htrackedTarget.symm
      (carrierCoordinate trackedTarget
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedTargetPortEdgeAt
          web corridor hinterior offset hnext port))
    faceSlot := fun slot =>
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionDartAtSlot?
        web.toFormation corridor hinterior next hcellNext slot).map fun dart =>
          Fin.cast hfaceTarget.symm (carrierCoordinate faceTarget dart)
    facePortCoordinate := fun fragment => Fin.cast hfaceTarget.symm
      (pointwiseSelectedSourceLocalLayerSerialFaceTargetPortCoordinateAt web
        corridor hinterior offset hnext (facePortEquiv fragment))
    colorSourceAt :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseCarrierSourceAt web
        corridor hinterior offset hnext hcell }

/-! ## Exact projection equations -/

@[simp]
theorem
    pointwiseSelectedSourceLocalLayerSerialTrackedRollingFactorAt_preRebaseCount
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
    (hcellNext : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior (sourceLocalLayerNextOffset offset hnext)).card ≤ 6)
    (color : G.edgeSet → Color) :
    (pointwiseSelectedSourceLocalLayerSerialTrackedInteractionPreRebaseStateForColorAt
        web corridor hinterior offset hnext hcell color).vertexCount =
      (pointwiseSelectedSourceLocalLayerSerialTrackedRollingFactorAt web corridor
        hinterior offset hnext hnextNext hcell hcellNext color).rebase.interactionCount := by
  rfl

@[simp]
theorem
    pointwiseSelectedSourceLocalLayerSerialTrackedRollingFactorAt_targetCount
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
    (hcellNext : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior (sourceLocalLayerNextOffset offset hnext)).card ≤ 6)
    (color : G.edgeSet → Color) :
    (pointwiseSelectedSourceLocalLayerSerialTrackedRollingFactorAt web corridor
      hinterior offset hnext hnextNext hcell hcellNext color).rebase.targetCount.val =
      (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)).card := by
  rfl

@[simp]
theorem
    pointwiseSelectedSourceLocalLayerSerialFaceRollingFactorAt_preRebaseCount
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
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3) :
    let hcell :=
      pointwiseSelectedSourceLocalLayerCellRegionAt_card_le_six graphData minimal
        caps coloring web corridor hinterior offset
    (pointwiseSelectedSourceLocalLayerSerialFaceInteractionPreRebaseStateAt
        web.toFormation corridor hinterior offset hnext hcell).vertexCount =
      (pointwiseSelectedSourceLocalLayerSerialFaceRollingFactorAt graphData
        minimal caps coloring web corridor hinterior offset hnext hnextNext
        ).rebase.interactionCount := by
  rfl

@[simp]
theorem
    pointwiseSelectedSourceLocalLayerSerialFaceRollingFactorAt_targetCount
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
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3) :
    (pointwiseSelectedSourceLocalLayerSerialFaceRollingFactorAt graphData
      minimal caps coloring web corridor hinterior offset hnext hnextNext
      ).rebase.targetCount.val =
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)).card := by
  rfl

private theorem selectedFacePrefixAttachmentState_ext
    (left right : SourceLocalLayerSerialFacePrefixAttachmentState)
    (hsupported : left.toBoundedSupportedPortResidualCode =
      right.toBoundedSupportedPortResidualCode)
    (hpresent : left.interfacePresent = right.interfacePresent)
    (hcap : left.componentCap = right.componentCap) :
    left = right := by
  cases left
  cases right
  simp_all

private theorem facialCumulativeStateOfCode_interfacePresent_of_decode
    {n : Nat}
    (code : BoundedInterfaceExteriorLabelCapCode (Fin n)
      (Fin n × Bool) 6)
    (decode : Fin 24 → Option (Fin n))
    (outputCount : Fin 5)
    (portCoordinate : Fin outputCount.val → Fin n)
    (slot : Fin 24) (targetSlot : Fin n)
    (hdecode : decode slot = some targetSlot) :
    (facialCumulativeStateOfCode code decode outputCount portCoordinate
      ).interfacePresent slot = code.interfacePresent targetSlot := by
  simp [facialCumulativeStateOfCode, hdecode]

private theorem facialCumulativeStateOfCode_supportedState
    {n : Nat}
    (code : BoundedInterfaceExteriorLabelCapCode (Fin n)
      (Fin n × Bool) 6)
    (decode : Fin 24 → Option (Fin n))
    (outputCount : Fin 5)
    (portCoordinate : Fin outputCount.val → Fin n)
    (hports : Fintype.card (Fin outputCount.val) ≤ 4) :
    (facialCumulativeStateOfCode code decode outputCount portCoordinate
      ).toBoundedSupportedPortResidualCode =
      padSupportedPortResidualCodePorts (boundedFiniteSlot? hports)
        (projectSupportedPortResidualCode code.connectivity decode
          portCoordinate) := by
  rfl

private theorem facialCumulativeStateOfCode_interfacePresent_of_decode_none
    {n : Nat}
    (code : BoundedInterfaceExteriorLabelCapCode (Fin n)
      (Fin n × Bool) 6)
    (decode : Fin 24 → Option (Fin n))
    (outputCount : Fin 5)
    (portCoordinate : Fin outputCount.val → Fin n)
    (slot : Fin 24) (hdecode : decode slot = none) :
    (facialCumulativeStateOfCode code decode outputCount portCoordinate
      ).interfacePresent slot = false := by
  simp [facialCumulativeStateOfCode, hdecode]

private theorem facialCumulativeStateOfCode_componentCap_of_decode
    {n : Nat}
    (code : BoundedInterfaceExteriorLabelCapCode (Fin n)
      (Fin n × Bool) 6)
    (decode : Fin 24 → Option (Fin n))
    (outputCount : Fin 5)
    (portCoordinate : Fin outputCount.val → Fin n)
    (slot : Fin 24) (targetSlot : Fin n)
    (hdecode : decode slot = some targetSlot) :
    (facialCumulativeStateOfCode code decode outputCount portCoordinate
      ).componentCap slot = facialTargetComponentCap code targetSlot := by
  simp [facialCumulativeStateOfCode, hdecode]

/-- Pointwise comparison of the facial projection with a canonically padded
interface code.  Keeping the large concrete facial code abstract here avoids
forcing the final exactness theorem to unfold the whole rolling carrier merely
to reduce the two identical decoder matches. -/
private theorem facialCumulativeStateOfCode_interfacePresent_eq_padCapped
    {n : Nat} {Interface Port : Type*}
    (code : BoundedInterfaceExteriorLabelCapCode (Fin n)
      (Fin n × Bool) 6)
    (coordinate : Interface ≃ Fin n)
    (decode : Fin 24 → Option Interface)
    (outputCount : Fin 5)
    (portCoordinate : Fin outputCount.val → Fin n)
    (prefixCode : BoundedCappedSupportedPortResidualCode Interface Port)
    (slot : Fin 24)
    (hpresent : ∀ interface,
      code.interfacePresent (coordinate interface) =
        prefixCode.interfacePresent interface) :
    (facialCumulativeStateOfCode code
      (fun stable => (decode stable).map coordinate) outputCount portCoordinate
      ).interfacePresent slot =
    (padCappedSupportedPortResidualCode decode prefixCode
      ).interfacePresent slot := by
  cases hdecode : decode slot with
  | none =>
      simp [facialCumulativeStateOfCode, padCappedSupportedPortResidualCode,
        hdecode]
  | some interface =>
      simpa [facialCumulativeStateOfCode, padCappedSupportedPortResidualCode,
        hdecode] using hpresent interface

/-- Component-cap counterpart of
`facialCumulativeStateOfCode_interfacePresent_eq_padCapped`. -/
private theorem facialCumulativeStateOfCode_componentCap_eq_padCapped
    {n : Nat} {Interface Port : Type*}
    (code : BoundedInterfaceExteriorLabelCapCode (Fin n)
      (Fin n × Bool) 6)
    (coordinate : Interface ≃ Fin n)
    (decode : Fin 24 → Option Interface)
    (outputCount : Fin 5)
    (portCoordinate : Fin outputCount.val → Fin n)
    (prefixCode : BoundedCappedSupportedPortResidualCode Interface Port)
    (slot : Fin 24)
    (hcap : ∀ interface,
      facialTargetComponentCap code (coordinate interface) =
        prefixCode.componentCap interface) :
    (facialCumulativeStateOfCode code
      (fun stable => (decode stable).map coordinate) outputCount portCoordinate
      ).componentCap slot =
    (padCappedSupportedPortResidualCode decode prefixCode
      ).componentCap slot := by
  cases hdecode : decode slot with
  | none =>
      simp [facialCumulativeStateOfCode, padCappedSupportedPortResidualCode,
        hdecode]
  | some interface =>
      simpa [facialCumulativeStateOfCode, padCappedSupportedPortResidualCode,
        hdecode] using hcap interface

private theorem facialCumulativeStateOfCode_componentCap_of_decode_none
    {n : Nat}
    (code : BoundedInterfaceExteriorLabelCapCode (Fin n)
      (Fin n × Bool) 6)
    (decode : Fin 24 → Option (Fin n))
    (outputCount : Fin 5)
    (portCoordinate : Fin outputCount.val → Fin n)
    (slot : Fin 24) (hdecode : decode slot = none) :
    (facialCumulativeStateOfCode code decode outputCount portCoordinate
      ).componentCap slot = 0 := by
  simp [facialCumulativeStateOfCode, hdecode]

/-- Padding occurrence-sensitive ports is natural under the finite
equivalence carried by the selected boundary-rebase receipt. -/
private theorem selectedPadProjectedPortResidualCode_equiv
    {Full Port EncodedPort Stable StablePort : Type*}
    [Fintype Full] [Fintype Port] [Fintype EncodedPort]
    (code : BoundedInterfaceExteriorCode Full)
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

set_option maxHeartbeats 800000 in
/-- The tracked target projection is exactly the canonical selected prefix
attachment state at the following cut. -/
theorem
    pointwiseSelectedSourceLocalLayerSerialRollingProjectionFactorAt_tracked_exact
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
    (prefixColor : PointwiseSelectedPositiveColorFunction
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet)
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt
        web.toFormation corridor hinterior offset) :
    let cellColor :=
      pointwiseSelectedSourceLocalLayerCellLiteralColorAt web.toFormation
        corridor hinterior offset cellColoring
    let splice :=
      pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt web.toFormation
        corridor hinterior offset prefixColor.1 cellColor
    let next := sourceLocalLayerNextOffset offset hnext
    let hcellNext :=
      pointwiseSelectedSourceLocalLayerCellRegionAt_card_le_six graphData minimal
        caps coloring web corridor hinterior next
    let trackedRolling :=
      pointwiseSelectedSourceLocalLayerSerialTrackedRollingFactorAt web corridor
        hinterior offset hnext hnextNext hcell hcellNext splice
    let preRebase :=
      pointwiseSelectedSourceLocalLayerSerialTrackedInteractionPreRebaseStateForColorAt
        web corridor hinterior offset hnext hcell splice
    let hpreCount :=
      pointwiseSelectedSourceLocalLayerSerialTrackedRollingFactorAt_preRebaseCount
        web corridor hinterior offset hnext hnextNext hcell hcellNext splice
    let projection :=
      pointwiseSelectedSourceLocalLayerSerialRollingProjectionFactorAt graphData
        minimal caps coloring web corridor hinterior offset hnext hnextNext
          hcell prefixColor cellColoring
    projection.trackedState
        (trackedRolling.rebase.targetState preRebase hpreCount).code =
      pointwiseSelectedSourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt
        web corridor hinterior (sourceLocalLayerNextOffset offset hnext)
          splice := by
  classical
  dsimp only
  let cellColor :=
    pointwiseSelectedSourceLocalLayerCellLiteralColorAt web.toFormation corridor
      hinterior offset cellColoring
  let splice :=
    pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt web.toFormation
      corridor hinterior offset prefixColor.1 cellColor
  let next := sourceLocalLayerNextOffset offset hnext
  let hcellNext :=
    pointwiseSelectedSourceLocalLayerCellRegionAt_card_le_six graphData minimal
      caps coloring web corridor hinterior next
  let projection :=
    pointwiseSelectedSourceLocalLayerSerialRollingProjectionFactorAt graphData
      minimal caps coloring web corridor hinterior offset hnext hnextNext hcell
        prefixColor cellColoring
  let trackedRolling :=
    pointwiseSelectedSourceLocalLayerSerialTrackedRollingFactorAt web corridor
      hinterior offset hnext hnextNext hcell hcellNext splice
  let preRebase :=
    pointwiseSelectedSourceLocalLayerSerialTrackedInteractionPreRebaseStateForColorAt
      web corridor hinterior offset hnext hcell splice
  let hpreCount :=
    pointwiseSelectedSourceLocalLayerSerialTrackedRollingFactorAt_preRebaseCount
      web corridor hinterior offset hnext hnextNext hcell hcellNext splice
  let target :=
    pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
      web.toFormation corridor hinterior next
  let graph :=
    pointwiseSelectedSuccessorTrackedGraphForColorAt web.toFormation corridor
      hinterior offset hnext splice
  let decoder :=
    pointwiseSelectedSourceLocalLayerSerialTrackedTransitionEdgeAtSlot?
      web.toFormation corridor hinterior next
  let port :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedTargetPortEdgeAt web
      corridor hinterior offset hnext
  let coordinate : {edge // edge ∈ target} ≃
      Fin trackedRolling.rebase.targetCount.val :=
    carrierCoordinate target
  let targetVertex := fun slot : Fin trackedRolling.rebase.targetCount.val =>
    (coordinate.symm slot).1
  have htrackedSlot : projection.trackedSlot = fun slot =>
      (decoder slot).map coordinate := by
    rfl
  have htrackedPort : projection.trackedPortCoordinate = fun targetPort =>
      coordinate (port targetPort) := by
    rfl
  change trackedCumulativeStateOfCode _ projection.trackedSlot
      projection.trackedPortCoordinate = _
  rw [htrackedSlot, htrackedPort]
  funext pair
  unfold trackedCumulativeStateOfCode
  have hcode :
      (trackedRolling.rebase.targetState preRebase hpreCount).code pair =
        exactInterfaceExteriorCode (graph pair) targetVertex := by
    convert
      (pointwiseSelectedSourceLocalLayerSerialTrackedRebaseFactorAt_targetState_code_exact
        graphData minimal caps coloring web corridor hinterior offset hnext
          hcell hcellNext splice pair) using 1 <;>
      simp [trackedRolling,
        pointwiseSelectedSourceLocalLayerSerialTrackedRollingFactorAt,
        preRebase, targetVertex, coordinate, target, next, graph]
    constructor <;> intro h
    · convert h using 1 <;> rfl
    · convert h using 1 <;> rfl
  rw [hcode]
  have hinjective : Function.Injective targetVertex := by
    intro left right heq
    apply coordinate.symm.injective
    exact Subtype.ext heq
  rw [projectSupportedPortResidualCode_exact_eq_pad _ targetVertex hinjective]
  simpa [pointwiseSelectedSourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt,
    pointwiseSelectedSuccessorTrackedGraphForColorAt, targetVertex, target,
      decoder, port, graph] using
    (pad_exactSupportedPortResidualCode_equiv
      (graph pair) (fun edge : {edge // edge ∈ target} => edge.1) coordinate
        decoder port)

set_option maxHeartbeats 800000 in
/-- On the exact selected successor code, forgetting the whole facial
interface computes precisely the cap at five of the distinct primal edges in
the live regional component. -/
private theorem pointwiseSelectedExactFaceTargetComponentCap_eq
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
    (slot : Fin
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)).card) :
    let next := sourceLocalLayerNextOffset offset hnext
    let region :=
      pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
        web.toFormation corridor hinterior next
    let target :=
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
        web.toFormation corridor hinterior next
    let targetDartAt := fun targetSlot : Fin target.card =>
      ((carrierCoordinate target).symm targetSlot).1
    facialTargetComponentCap
        (exactFaceInterfaceExteriorLabelCapCode web.annular.RS region
          targetDartAt 6) slot =
      ⟨min (sourceLocalLayerBoundaryRebaseFaceComponentEdges web.annular.RS
          region (targetDartAt slot)).card 5,
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ := by
  classical
  dsimp only
  let next := sourceLocalLayerNextOffset offset hnext
  let region :=
    pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
      web.toFormation corridor hinterior next
  let graph := faceRegionalDartGraph web.annular.RS region
  let target :=
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
      web.toFormation corridor hinterior next
  let targetDartAt := fun targetSlot : Fin target.card =>
    ((carrierCoordinate target).symm targetSlot).1
  let code := exactFaceInterfaceExteriorLabelCapCode web.annular.RS region
    targetDartAt 6
  unfold facialTargetComponentCap
  change (if code.interfacePresent slot then
      (⟨min (interfaceExteriorLabelCapFullComponent code Prod.fst slot).val 5,
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ : Fin 6)
    else (0 : Fin 6)) =
      ⟨min (sourceLocalLayerBoundaryRebaseFaceComponentEdges web.annular.RS
          region (targetDartAt slot)).card 5,
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  by_cases hpresent : web.annular.RS.edgeOf (targetDartAt slot) ∈ region
  · have hcodePresent : code.interfacePresent slot = true := by
      unfold code
      exact (exactFaceInterfaceExteriorLabelCapCode_interfacePresent_iff
        web.annular.RS region targetDartAt slot 6).2 hpresent
    simp only [hcodePresent, if_true]
    have htargetInternal : dartOrbitFace web.annular.RS
          (targetDartAt slot) ∈ web.annular.cellulation.interiorFaces := by
      exact
        pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetDartAt_face_internal
          graphData minimal caps coloring web corridor hinterior offset hnext
            slot (by simpa [next, region, target, targetDartAt] using hpresent)
    have hlabelInjective : Set.InjOn web.annular.RS.edgeOf
        {vertex | graph.Reachable (targetDartAt slot) vertex} := by
      intro left hleft right hright hedge
      have hleftFace : dartOrbitFace web.annular.RS (targetDartAt slot) =
          dartOrbitFace web.annular.RS left :=
        faceRegionalDartGraph_reachable_dartOrbitFace_eq web.annular.RS region
          hleft
      have hrightFace : dartOrbitFace web.annular.RS (targetDartAt slot) =
          dartOrbitFace web.annular.RS right :=
        faceRegionalDartGraph_reachable_dartOrbitFace_eq web.annular.RS region
          hright
      have hinjective : Set.InjOn web.annular.RS.edgeOf
          (orbitFaceDarts web.annular.RS
            (dartOrbitFace web.annular.RS (targetDartAt slot))) := by
        apply Finset.card_image_iff.mp
        exact InteriorFace.boundary_card_eq_darts_card web (targetDartAt slot)
          htargetInternal
      exact hinjective
        ((mem_orbitFaceDarts_iff web.annular.RS
          (dartOrbitFace web.annular.RS (targetDartAt slot)) left).2
            hleftFace.symm)
        ((mem_orbitFaceDarts_iff web.annular.RS
          (dartOrbitFace web.annular.RS (targetDartAt slot)) right).2
            hrightFace.symm)
        hedge
    have hfull :
        (interfaceExteriorLabelCapFullComponent code Prod.fst slot).val =
          min (fullComponentLabelSupport graph targetDartAt
            web.annular.RS.edgeOf slot).card 6 := by
      unfold code exactFaceInterfaceExteriorLabelCapCode
      apply interfaceExteriorLabelCapFullComponent_exact
      · intro targetSlot hsupport
        rcases hsupport with ⟨other, hadj⟩
        exact (faceRegionalDartGraph_adj web.annular.RS region _ _).1
          hadj |>.2.2.1
      · intro targetSlot outside houtside hadj
        rcases exists_faceInterfaceIncidence_of_adj_outside web.annular.RS
            region targetDartAt targetSlot outside hadj houtside with
          ⟨direction, hvertex, _⟩
        exact ⟨(targetSlot, direction), rfl, hvertex⟩
      · exact hpresent
      · intro left right heq
        apply (carrierCoordinate target).symm.injective
        exact Subtype.ext heq
      · exact hlabelInjective
    have hsupport : fullComponentLabelSupport graph targetDartAt
          web.annular.RS.edgeOf slot =
        sourceLocalLayerBoundaryRebaseFaceComponentEdges web.annular.RS region
          (targetDartAt slot) := by
      letI : DecidablePred (graph.Reachable (targetDartAt slot)) :=
        Classical.decPred _
      ext edge
      rw [mem_sourceLocalLayerBoundaryRebaseFaceComponentEdges_iff]
      constructor
      · intro hedge
        rw [fullComponentLabelSupport] at hedge
        rcases Finset.mem_image.mp hedge with ⟨dart, hdart, hedgeOf⟩
        rw [Finset.mem_filter] at hdart
        have hedgeRegion : web.annular.RS.edgeOf dart ∈ region := by
          by_cases heq : dart = targetDartAt slot
          · simpa [heq] using hpresent
          · have hsupport : dart ∈ graph.support :=
              SimpleGraph.mem_support_of_reachable heq hdart.2.symm
            rw [SimpleGraph.mem_support] at hsupport
            rcases hsupport with ⟨neighbor, hadj⟩
            exact (faceRegionalDartGraph_adj web.annular.RS region _ _).1
              (by simpa [graph] using hadj) |>.2.2.1
        exact ⟨hedgeOf ▸ hedgeRegion,
          ⟨⟨dart, web.annular.RS.mem_dartsOn.2 hedgeOf⟩, hdart.2⟩⟩
      · rintro ⟨hedgeRegion, dart, hreachable⟩
        rw [fullComponentLabelSupport]
        apply Finset.mem_image.mpr
        exact ⟨dart.1, by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, by simpa [graph] using hreachable⟩,
          web.annular.RS.mem_dartsOn.1 dart.2⟩
    apply Fin.ext
    simp only
    rw [hfull, hsupport]
    omega
  · have hcodePresent : code.interfacePresent slot = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      exact hpresent
        ((exactFaceInterfaceExteriorLabelCapCode_interfacePresent_iff
          web.annular.RS region targetDartAt slot 6).1 (by
            simpa [code] using htrue))
    simp [hcodePresent]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro edge hedge
    rw [mem_sourceLocalLayerBoundaryRebaseFaceComponentEdges_iff] at hedge
    rcases hedge with ⟨hedgeRegion, dart, hreachable⟩
    by_cases heq : dart.1 = targetDartAt slot
    · have hedgeOf : web.annular.RS.edgeOf dart.1 = edge :=
        web.annular.RS.mem_dartsOn.1 dart.2
      rw [← hedgeOf, heq] at hedgeRegion
      exact hpresent hedgeRegion
    · have hsupport : targetDartAt slot ∈ graph.support :=
        SimpleGraph.mem_support_of_reachable (Ne.symm heq) hreachable
      rw [SimpleGraph.mem_support] at hsupport
      rcases hsupport with ⟨neighbor, hadj⟩
      exact hpresent ((faceRegionalDartGraph_adj web.annular.RS region _ _).1
        (by simpa [graph] using hadj) |>.2.2.1)

private theorem
    pointwiseSelectedFacePrefixAttachmentCode_interfacePresent
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (dart : {dart // dart ∈
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior offset}) :
    (pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentCodeAt
      formation corridor hinterior offset).interfacePresent dart =
      decide (formation.annular.RS.edgeOf dart.1 ∈
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
          corridor hinterior offset) := by
  rfl

private theorem pointwiseSelectedFacePrefixAttachmentCode_componentCap
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (dart : {dart // dart ∈
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior offset}) :
    (pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentCodeAt
      formation corridor hinterior offset).componentCap dart =
      ⟨min (sourceLocalLayerBoundaryRebaseFaceComponentEdges
          formation.annular.RS
          (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
            formation corridor hinterior offset) dart.1).card 5,
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ := by
  rfl

private theorem exactFaceInterfaceExteriorLabelCapCode_interfacePresent_eq_decide
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (region : Finset E)
    (interfaceVertex : Interface → RS.D) (slot : Interface)
    (cap : Nat) :
    (exactFaceInterfaceExteriorLabelCapCode RS region interfaceVertex cap
      ).interfacePresent slot =
        decide (RS.edgeOf (interfaceVertex slot) ∈ region) := by
  rfl

private theorem exactFaceInterfaceExteriorLabelCapCode_interfacePresent_coordinate
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (region : Finset E)
    {target : Finset RS.D}
    (coordinate : {dart // dart ∈ target} ≃ Fin target.card)
    (dart : {dart // dart ∈ target}) :
    (exactFaceInterfaceExteriorLabelCapCode RS region
      (fun slot => (coordinate.symm slot).1) 6).interfacePresent
        (coordinate dart) =
      decide (RS.edgeOf dart.1 ∈ region) := by
  change decide (RS.edgeOf (coordinate.symm (coordinate dart)).1 ∈ region) =
    decide (RS.edgeOf dart.1 ∈ region)
  rw [Equiv.symm_apply_apply]

set_option maxHeartbeats 4000000 in
/-- The facial target projection is exactly the canonical selected facial
prefix state at the following cut. -/
theorem
    pointwiseSelectedSourceLocalLayerSerialRollingProjectionFactorAt_face_exact
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
    (prefixColor : PointwiseSelectedPositiveColorFunction
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet)
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt
        web.toFormation corridor hinterior offset) :
    let next := sourceLocalLayerNextOffset offset hnext
    let hcellCurrent :=
      pointwiseSelectedSourceLocalLayerCellRegionAt_card_le_six graphData minimal
        caps coloring web corridor hinterior offset
    let hcellNext :=
      pointwiseSelectedSourceLocalLayerCellRegionAt_card_le_six graphData minimal
        caps coloring web corridor hinterior next
    let faceRolling :=
      pointwiseSelectedSourceLocalLayerSerialFaceRollingFactorAt graphData
        minimal caps coloring web corridor hinterior offset hnext hnextNext
    let preRebase :=
      pointwiseSelectedSourceLocalLayerSerialFaceInteractionPreRebaseStateAt
        web.toFormation corridor hinterior offset hnext hcellCurrent
    let hpreCount :=
      pointwiseSelectedSourceLocalLayerSerialFaceRollingFactorAt_preRebaseCount
        graphData minimal caps coloring web corridor hinterior offset hnext
          hnextNext
    let projection :=
      pointwiseSelectedSourceLocalLayerSerialRollingProjectionFactorAt graphData
        minimal caps coloring web corridor hinterior offset hnext hnextNext
          hcell prefixColor cellColoring
    projection.faceState
        ((faceRolling.rebase.targetState preRebase hpreCount).code ()) =
      pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt
        web.toFormation corridor hinterior next hcellNext := by
  classical
  dsimp only
  let next := sourceLocalLayerNextOffset offset hnext
  let hcellCurrent :=
    pointwiseSelectedSourceLocalLayerCellRegionAt_card_le_six graphData minimal
      caps coloring web corridor hinterior offset
  let hcellNext :=
    pointwiseSelectedSourceLocalLayerCellRegionAt_card_le_six graphData minimal
      caps coloring web corridor hinterior next
  let faceRolling :=
    pointwiseSelectedSourceLocalLayerSerialFaceRollingFactorAt graphData minimal
      caps coloring web corridor hinterior offset hnext hnextNext
  let preRebase :=
    pointwiseSelectedSourceLocalLayerSerialFaceInteractionPreRebaseStateAt
      web.toFormation corridor hinterior offset hnext hcellCurrent
  let hpreCount :=
    pointwiseSelectedSourceLocalLayerSerialFaceRollingFactorAt_preRebaseCount
      graphData minimal caps coloring web corridor hinterior offset hnext
        hnextNext
  let projection :=
    pointwiseSelectedSourceLocalLayerSerialRollingProjectionFactorAt graphData
      minimal caps coloring web corridor hinterior offset hnext hnextNext hcell
        prefixColor cellColoring
  let factored :=
    pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt web
      corridor hinterior offset hnext hcell prefixColor.1
        (fun step => prefixColor.2
          (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
            corridor hinterior offset step)) cellColoring
  let cellColor :=
    pointwiseSelectedSourceLocalLayerCellLiteralColorAt web.toFormation corridor
      hinterior offset cellColoring
  let splice :=
    pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt web.toFormation
      corridor hinterior offset prefixColor.1 cellColor
  let hrole : ∀ role, splice
      (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt web.toFormation
        corridor hinterior offset hnext role) ≠ 0 :=
    pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_boundaryRebaseEdge_ne_zero
      web.toFormation corridor hinterior offset hnext prefixColor.1
        prefixColor.2 cellColoring
  let rebase :=
    pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedSupportLetterForColorAt
      web.toFormation corridor hinterior offset hnext factored.2.1 splice hrole
  let target :=
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
      web.toFormation corridor hinterior next
  let FacePort := PointwiseSelectedSourceLocalLayerSerialFaceInputPortAt
    web.toFormation corridor hinterior next
  have houtputCount : rebase.output.faceFragmentCount.val =
      Fintype.card FacePort := by
    rfl
  let facePortEquiv : Fin rebase.output.faceFragmentCount.val ≃ FacePort :=
    (Fintype.equivFin (Fin rebase.output.faceFragmentCount.val)).trans
      ((finCongr (Fintype.card_fin rebase.output.faceFragmentCount.val)).trans
        ((finCongr houtputCount).trans (Fintype.equivFin FacePort).symm))
  let coordinate : {dart // dart ∈ target} ≃
      Fin faceRolling.rebase.targetCount.val :=
    carrierCoordinate target
  let targetDart := fun slot : Fin faceRolling.rebase.targetCount.val =>
    (coordinate.symm slot).1
  let decoder :=
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionDartAtSlot?
      web.toFormation corridor hinterior next hcellNext
  let prefixCode :=
    pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentCodeAt
      web.toFormation corridor hinterior next
  let actualPortDecoder :=
    pointwiseSelectedSourceLocalLayerSerialFaceInputPortAtSlot?
      web.toFormation corridor hinterior next
  let targetPort :=
    pointwiseSelectedSourceLocalLayerSerialFaceTargetPortDartAt web corridor
      hinterior offset hnext
  have hfaceSlot : projection.faceSlot = fun slot =>
      (decoder slot).map coordinate := by
    rfl
  have hfacePort : projection.facePortCoordinate = fun fragment =>
      coordinate (targetPort (facePortEquiv fragment)) := by
    rfl
  have hfin : Fintype.card (Fin rebase.output.faceFragmentCount.val) ≤ 4 := by
    simpa using Nat.le_of_lt_succ rebase.output.faceFragmentCount.isLt
  have hportDecode : ∀ slot,
      (boundedFiniteSlot? hfin slot).map facePortEquiv =
        pointwiseSelectedSourceLocalLayerSerialFaceInputPortAtSlot?
          web.toFormation corridor hinterior next slot := by
    intro slot
    unfold pointwiseSelectedSourceLocalLayerSerialFaceInputPortAtSlot?
      boundedFiniteSlot?
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
  have hcode :
      (faceRolling.rebase.targetState preRebase hpreCount).code () =
        exactFaceInterfaceExteriorLabelCapCode web.annular.RS
          (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
            web.toFormation corridor hinterior next) targetDart 6 := by
    calc
      _ =
          pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt
            graphData minimal caps coloring web corridor hinterior offset
              hnext := by
        convert
          (pointwiseSelectedSourceLocalLayerSerialFaceRebaseTargetStateAt_code_eq
            graphData minimal caps coloring web corridor hinterior offset hnext
              hcellCurrent) using 1 <;>
          simp [faceRolling,
            pointwiseSelectedSourceLocalLayerSerialFaceRollingFactorAt,
            preRebase]
        constructor <;> intro h
        · convert h using 1 <;> rfl
        · convert h using 1 <;> rfl
      _ = _ := by
        convert
          (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_exact
            graphData minimal caps coloring web corridor hinterior offset hnext)
          using 1 <;> rfl
  have hprefixState :
      pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt
          web.toFormation corridor hinterior next hcellNext =
        padCappedSupportedPortResidualCodePorts actualPortDecoder
          (padCappedSupportedPortResidualCode decoder prefixCode) := by
    rfl
  have htargetPresent (dart : {dart // dart ∈ target}) :
      (exactFaceInterfaceExteriorLabelCapCode web.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
          web.toFormation corridor hinterior next) targetDart 6
        ).interfacePresent (coordinate dart) =
      decide (web.annular.RS.edgeOf dart.1 ∈
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
          web.toFormation corridor hinterior next) := by
    exact
      exactFaceInterfaceExteriorLabelCapCode_interfacePresent_coordinate
        web.annular.RS
          (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
            web.toFormation corridor hinterior next)
          coordinate dart
  change facialCumulativeStateOfCode _ projection.faceSlot _
      projection.facePortCoordinate = _
  rw [hfaceSlot, hfacePort, hcode, hprefixState]
  apply selectedFacePrefixAttachmentState_ext
  ·
    let graph := faceRegionalDartGraph web.annular.RS
      (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
        web.toFormation corridor hinterior next)
    let portDart := fun port : FacePort => targetPort port
    rw [facialCumulativeStateOfCode_supportedState _ _ _ _ hfin]
    change padSupportedPortResidualCodePorts (boundedFiniteSlot? hfin)
        (projectSupportedPortResidualCode
          (exactInterfaceExteriorCode graph targetDart)
          (fun slot => (decoder slot).map coordinate)
          (fun fragment => coordinate (portDart (facePortEquiv fragment)))) =
      padSupportedPortResidualCodePorts
        (pointwiseSelectedSourceLocalLayerSerialFaceInputPortAtSlot?
          web.toFormation corridor hinterior next)
        (padSupportedPortResidualCode decoder
          (exactSupportedPortResidualCode graph
            (fun dart : {dart // dart ∈ target} => dart.1)
            (fun port => (portDart port).1)))
    calc
      _ = padSupportedPortResidualCodePorts
          (pointwiseSelectedSourceLocalLayerSerialFaceInputPortAtSlot?
            web.toFormation corridor hinterior next)
          (projectSupportedPortResidualCode
            (exactInterfaceExteriorCode graph targetDart)
            (fun slot => (decoder slot).map coordinate)
            (fun port => coordinate (portDart port))) := by
        exact selectedPadProjectedPortResidualCode_equiv
          (exactInterfaceExteriorCode graph targetDart)
          (fun slot => (decoder slot).map coordinate) facePortEquiv
          (boundedFiniteSlot? hfin)
          (pointwiseSelectedSourceLocalLayerSerialFaceInputPortAtSlot?
            web.toFormation corridor hinterior next) hportDecode
          (fun port => coordinate (portDart port))
      _ = _ := by
        congr 1
        have hinjective : Function.Injective targetDart := by
          intro left right heq
          apply coordinate.symm.injective
          exact Subtype.ext heq
        rw [projectSupportedPortResidualCode_exact_eq_pad _ _ hinjective]
        have hpad := pad_exactSupportedPortResidualCode_equiv graph
          (fun dart : {dart // dart ∈ target} => dart.1) coordinate decoder
            portDart
        simpa only [targetDart, Equiv.symm_apply_apply] using hpad
  · funext slot
    let region :=
      pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
        web.toFormation corridor hinterior next
    rw [padCappedSupportedPortResidualCodePorts_interfacePresent]
    apply facialCumulativeStateOfCode_interfacePresent_eq_padCapped
    intro dart
    have hstate := pointwiseSelectedFacePrefixAttachmentCode_interfacePresent
      web.toFormation corridor hinterior next dart
    exact (htargetPresent dart).trans hstate.symm
  · funext slot
    rw [padCappedSupportedPortResidualCodePorts_componentCap]
    apply facialCumulativeStateOfCode_componentCap_eq_padCapped
    intro dart
    have hstate := pointwiseSelectedFacePrefixAttachmentCode_componentCap
      web.toFormation corridor hinterior next dart
    rw [hstate]
    have hraw :=
      pointwiseSelectedExactFaceTargetComponentCap_eq graphData minimal
        caps coloring web corridor hinterior offset hnext
          ((carrierCoordinate target) dart)
    dsimp only at hraw
    apply Fin.ext
    have hrawVal := congrArg Fin.val hraw
    dsimp only [next, target, targetDart, coordinate] at hrawVal ⊢
    simp only [Equiv.symm_apply_apply] at hrawVal
    convert hrawVal using 1 <;> rfl

end

end GoertzelV24ClosedWebPointwiseSelectedRollingProjectionExact

end Mettapedia.GraphTheory.FourColor
