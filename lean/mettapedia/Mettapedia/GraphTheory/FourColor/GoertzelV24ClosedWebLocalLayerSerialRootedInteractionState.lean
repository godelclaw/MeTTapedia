import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedPreRebaseState
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformInterface
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceRecurrence

/-!
# A bounded lookahead root for one complete Cell--rebase step

The current tracked and facial cuts have at most twenty-one edge coordinates
and twenty-four dart coordinates.  A following boundary rebase can promote an
edge or dart which is outside those current interfaces, so the current exterior
codes alone cannot determine how the promoted object splits an exterior
component.

The structural Cell--rebase interface theorem bounds the union of the current
carrier and the complete rebase collar by forty-nine edges and forty-eight
darts, independently of the corridor length.  This file records the prefix's
exact deletion-stable exterior codes on both uniform interaction carriers.  It
also stores the finite inclusions of the current coordinates into the
interaction coordinates.

This is still a source-independent finite state type.  The source constructor
below proves exactness for arbitrary compatible prefix colours; it does not
claim that every finite inhabitant is realizable or measure a reachable
closure.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24ClosedWebLocalLayerSerialRootedCumulativeState
open GoertzelV24CorridorProfile
open GoertzelV24DeletionSensitivePortResidualFactorContraction
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24RotationFaceInterfaceExteriorLabelCap
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance rootedInteractionOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The deletion-stable prefix code on the complete bounded tracked
interaction carrier. -/
abbrev SourceLocalLayerSerialTrackedInteractionPrefixState :=
  BoundedInterfaceExteriorFamilyCode 49 TrackedColorPair

/-- The cap-six facial prefix code on the complete bounded dart interaction
carrier. -/
abbrev SourceLocalLayerSerialFaceInteractionPrefixState :=
  BoundedInterfaceExteriorLabelCapFamilyCode 48 Unit 6

/-- A rooted cumulative state with enough bounded lookahead to perform the
following tracked and facial boundary rebase without promoting an unknown
exterior vertex. -/
structure SourceLocalLayerSerialRootedInteractionState extends
    SourceLocalLayerSerialRootedCumulativeState where
  interactionExterior : SourceLocalLayerSerialTrackedInteractionPrefixState
  currentCoordinate :
    Fin trackedExterior.vertexCount.val →
      Fin interactionExterior.vertexCount.val
  faceInteractionExterior : SourceLocalLayerSerialFaceInteractionPrefixState
  faceCurrentCoordinate :
    Fin faceCapSix.vertexCount.val →
      Fin faceInteractionExterior.vertexCount.val

noncomputable instance :
    DecidableEq SourceLocalLayerSerialRootedInteractionState :=
  Classical.decEq _

private def sourceLocalLayerSerialRootedInteractionStateEquiv :
    SourceLocalLayerSerialRootedInteractionState ≃
      Σ rooted : SourceLocalLayerSerialRootedCumulativeState,
        Σ interactionExterior :
            SourceLocalLayerSerialTrackedInteractionPrefixState,
          (Fin rooted.trackedExterior.vertexCount.val →
              Fin interactionExterior.vertexCount.val) ×
            (Σ faceInteractionExterior :
                SourceLocalLayerSerialFaceInteractionPrefixState,
              Fin rooted.faceCapSix.vertexCount.val →
                Fin faceInteractionExterior.vertexCount.val) where
  toFun state :=
    ⟨state.toSourceLocalLayerSerialRootedCumulativeState,
      state.interactionExterior, state.currentCoordinate,
      state.faceInteractionExterior, state.faceCurrentCoordinate⟩
  invFun data := {
    toSourceLocalLayerSerialRootedCumulativeState := data.1
    interactionExterior := data.2.1
    currentCoordinate := data.2.2.1
    faceInteractionExterior := data.2.2.2.1
    faceCurrentCoordinate := data.2.2.2.2 }
  left_inv state := by cases state; rfl
  right_inv data := by
    rcases data with ⟨rooted, interaction, coordinate, faceInteraction,
      faceCoordinate⟩
    rfl

noncomputable instance :
    Fintype SourceLocalLayerSerialRootedInteractionState :=
  Fintype.ofEquiv _ sourceLocalLayerSerialRootedInteractionStateEquiv.symm

/-- Extract the complete finite lookahead root of an arbitrary compatible
prefix colour function at an interior Cell position. -/
noncomputable def sourceLocalLayerSerialRootedInteractionStateForColorAt
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
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcrossing : ∀ step,
      color ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0) :
    SourceLocalLayerSerialRootedInteractionState := by
  let current := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
    caps coloring web corridor hunique offset
  let interaction :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
      coloring web corridor hunique offset hnext
  let faceCurrent := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
    hunique offset
  let faceInteraction :=
    sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
      offset hnext
  let rooted := sourceLocalLayerSerialRootedCumulativeStateForColorAt graphData
    minimal caps coloring web corridor hunique offset color hcrossing
  let interactionExterior := boundedInterfaceExteriorFamilyCode interaction 49
    (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
      graphData minimal caps coloring web corridor hunique offset hnext)
    (fun pair => regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
      color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2)
  let faceInteractionExterior :
      SourceLocalLayerSerialFaceInteractionPrefixState := {
    vertexCount := ⟨faceInteraction.card, Nat.lt_succ_of_le
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt_card_le_fortyEight
        graphData minimal caps coloring web corridor hunique offset hnext)⟩
    code := fun _ => exactFaceInterfaceExteriorLabelCapCode web.annular.RS
      (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
      (fun slot : Fin faceInteraction.card ↦
        ((carrierCoordinate faceInteraction).symm slot).1) 6 }
  exact {
    toSourceLocalLayerSerialRootedCumulativeState := rooted
    interactionExterior := interactionExterior
    currentCoordinate := fun slot =>
      carrierCoordinate interaction
        ⟨((carrierCoordinate current).symm slot).1,
          Finset.mem_union_left _ ((carrierCoordinate current).symm slot).2⟩
    faceInteractionExterior := faceInteractionExterior
    faceCurrentCoordinate := fun slot ↦
      carrierCoordinate faceInteraction
        ⟨((carrierCoordinate faceCurrent).symm slot).1,
          Finset.mem_union_left _ ((carrierCoordinate faceCurrent).symm slot).2⟩ }

@[simp]
theorem sourceLocalLayerSerialRootedInteractionStateForColorAt_toRooted
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
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcrossing : ∀ step,
      color ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0) :
    (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
      caps coloring web corridor hunique offset hnext color hcrossing
      ).toSourceLocalLayerSerialRootedCumulativeState =
      sourceLocalLayerSerialRootedCumulativeStateForColorAt graphData minimal
        caps coloring web corridor hunique offset color hcrossing := by
  rfl

/-- The lookahead code stores the literal cardinality of the uniform
interaction carrier. -/
@[simp]
theorem sourceLocalLayerSerialRootedInteractionStateForColorAt_interactionCount
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
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcrossing : ∀ step,
      color ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0) :
    (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
      caps coloring web corridor hunique offset hnext color hcrossing
      ).interactionExterior.vertexCount.val =
      (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique offset hnext).card := by
  rfl

/-- The facial lookahead code stores the literal cardinality of the uniform
dart interaction carrier. -/
@[simp]
theorem
    sourceLocalLayerSerialRootedInteractionStateForColorAt_faceInteractionCount
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
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcrossing : ∀ step,
      color ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0) :
    (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
      caps coloring web corridor hunique offset hnext color hcrossing
      ).faceInteractionExterior.vertexCount.val =
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        offset hnext).card := by
  rfl

/-- The facial lookahead row is the exact cap-six factor of the arbitrary
compatible prefix on the complete dart interaction carrier. -/
theorem sourceLocalLayerSerialRootedInteractionStateForColorAt_faceCode_eq
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
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcrossing : ∀ step,
      color ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0) :
    let interaction :=
      sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        offset hnext
    let dartAt := fun slot : Fin interaction.card ↦
      ((carrierCoordinate interaction).symm slot).1
    (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
      caps coloring web corridor hunique offset hnext color hcrossing
      ).faceInteractionExterior.code () =
      exactFaceInterfaceExteriorLabelCapCode web.annular.RS
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
        dartAt 6 := by
  rfl

/-- The stored facial current-coordinate inclusion names exactly the same
ambient dart in the enlarged interaction carrier. -/
theorem
    sourceLocalLayerSerialRootedInteractionStateForColorAt_faceCurrentDart
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
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcrossing : ∀ step,
      color ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (slot : Fin
      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
        ).card) :
    let state := sourceLocalLayerSerialRootedInteractionStateForColorAt
      graphData minimal caps coloring web corridor hunique offset hnext color
        hcrossing
    let current := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
      hunique offset
    let interaction :=
      sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        offset hnext
    ((carrierCoordinate interaction).symm
        (state.faceCurrentCoordinate slot)).1 =
      ((carrierCoordinate current).symm slot).1 := by
  dsimp only [sourceLocalLayerSerialRootedInteractionStateForColorAt]
  rw [Equiv.symm_apply_apply]

/-- The stored current-coordinate inclusion names exactly the same literal
edge in the interaction carrier. -/
theorem sourceLocalLayerSerialRootedInteractionStateForColorAt_currentEdge
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
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcrossing : ∀ step,
      color ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (slot : Fin
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset).card) :
    let state := sourceLocalLayerSerialRootedInteractionStateForColorAt
      graphData minimal caps coloring web corridor hunique offset hnext color
        hcrossing
    let current := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
      caps coloring web corridor hunique offset
    let interaction :=
      sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique offset hnext
    ((carrierCoordinate interaction).symm (state.currentCoordinate slot)).1 =
      ((carrierCoordinate current).symm slot).1 := by
  dsimp only [sourceLocalLayerSerialRootedInteractionStateForColorAt]
  rw [Equiv.symm_apply_apply]

/-- The source current-coordinate inclusion has no aliases. -/
theorem
    sourceLocalLayerSerialRootedInteractionStateForColorAt_currentCoordinate_injective
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
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcrossing : ∀ step,
      color ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0) :
    Function.Injective
      (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
        caps coloring web corridor hunique offset hnext color hcrossing
        ).currentCoordinate := by
  intro left right heq
  let state := sourceLocalLayerSerialRootedInteractionStateForColorAt graphData
    minimal caps coloring web corridor hunique offset hnext color hcrossing
  let current := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
    caps coloring web corridor hunique offset
  let interaction :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
      coloring web corridor hunique offset hnext
  apply (carrierCoordinate current).symm.injective
  apply Subtype.ext
  calc
    ((carrierCoordinate current).symm left).1 =
        ((carrierCoordinate interaction).symm
          (state.currentCoordinate left)).1 := by
      exact (sourceLocalLayerSerialRootedInteractionStateForColorAt_currentEdge
        graphData minimal caps coloring web corridor hunique offset hnext color
          hcrossing left).symm
    _ = ((carrierCoordinate interaction).symm
          (state.currentCoordinate right)).1 := by rw [heq]
    _ = ((carrierCoordinate current).symm right).1 := by
      exact sourceLocalLayerSerialRootedInteractionStateForColorAt_currentEdge
        graphData minimal caps coloring web corridor hunique offset hnext color
          hcrossing right

/-- On source data, every interaction row reconstructs exact prefix
reachability after every deletion mask on the complete 49-edge carrier. -/
theorem sourceLocalLayerSerialRootedInteractionStateForColorAt_reachable_iff
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
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcrossing : ∀ step,
      color ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (pair : TrackedColorPair)
    (removed : Fin
      (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique offset hnext).card → Bool)
    (left right : SurvivingInterfaceSlot
      (fun slot : Fin
          (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData
            caps coloring web corridor hunique offset hnext).card =>
        ((carrierCoordinate
          (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData
            caps coloring web corridor hunique offset hnext)).symm slot).1)
      removed) :
    let interaction :=
      sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique offset hnext
    let graph := regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
      color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
    let edgeAt := fun slot : Fin interaction.card =>
      ((carrierCoordinate interaction).symm slot).1
    (restrictedByMask graph edgeAt removed).Reachable
        (edgeAt left.1) (edgeAt right.1) ↔
      Relation.ReflTransGen
        (fun first second : SurvivingInterfaceSlot edgeAt removed =>
          InterfaceExteriorFactoredStep
            ((sourceLocalLayerSerialRootedInteractionStateForColorAt graphData
              minimal caps coloring web corridor hunique offset hnext color
                hcrossing).interactionExterior.code pair)
            first.1 second.1)
        left right := by
  simpa [sourceLocalLayerSerialRootedInteractionStateForColorAt] using
    (boundedInterfaceExteriorFamilyCode_reachable_iff
      (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique offset hnext)
      49
      (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
        graphData minimal caps coloring web corridor hunique offset hnext)
      (fun trackedPair => regionalTrackedEdgeGraph web.annular.RS
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
        color (trackedColorPairColors trackedPair).1
          (trackedColorPairColors trackedPair).2)
      pair removed left right)

end

end GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState

end Mettapedia.GraphTheory.FourColor
