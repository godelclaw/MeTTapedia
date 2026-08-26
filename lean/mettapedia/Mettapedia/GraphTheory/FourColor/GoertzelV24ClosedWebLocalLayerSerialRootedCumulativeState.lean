import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialColoredCumulativeStateForColor
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePrefixState

/-!
# A deletion-stable rooted cumulative Cell state

The source profile of one cumulative corridor prefix must survive the deletion
performed by the following Cell boundary rebase.  A component partition on the
current twenty-one-slot carrier is not enough: deleting a carrier edge can
split a component in ways which that partition no longer distinguishes.

This file conservatively extends the already verified coloured cumulative
state with the bounded interface-exterior family code which reconstructs
prefix reachability after every carrier mask.  The extension is finite and
projects definitionally to the former state, so the existing positive-`Count`
factorization remains unchanged.  At literal source data its new field is the
exact deletion-stable prefix code.

This is the rooted object on which the later relational Cell--rebase
transition acts.  It does not claim that every arbitrary finite state is
source-realizable, and it does not compute a reachable closure.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialRootedCumulativeState

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePrefixState
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24ClosedWebLocalLayerSerialColoredCumulativeStateForColor
open GoertzelV24CorridorProfile
open GoertzelV24DeletionSensitivePortResidualFactorContraction
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance rootedCumulativeStateOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- A finite cumulative Cell state together with the deletion-stable tracked
exterior connectivity of its rooted prefix. -/
structure SourceLocalLayerSerialRootedCumulativeState extends
    SourceLocalLayerSerialColoredCumulativeState where
  trackedExterior : SourceLocalLayerSerialTrackedDeletionStablePrefixState

noncomputable instance :
    DecidableEq SourceLocalLayerSerialRootedCumulativeState :=
  Classical.decEq _

private def sourceLocalLayerSerialRootedCumulativeStateEquiv :
    SourceLocalLayerSerialRootedCumulativeState ≃
      SourceLocalLayerSerialColoredCumulativeState ×
        SourceLocalLayerSerialTrackedDeletionStablePrefixState where
  toFun state :=
    ⟨state.toSourceLocalLayerSerialColoredCumulativeState,
      state.trackedExterior⟩
  invFun data := {
    toSourceLocalLayerSerialColoredCumulativeState := data.1
    trackedExterior := data.2 }
  left_inv state := by cases state; rfl
  right_inv data := by cases data; rfl

noncomputable instance :
    Fintype SourceLocalLayerSerialRootedCumulativeState :=
  Fintype.ofEquiv _ sourceLocalLayerSerialRootedCumulativeStateEquiv.symm

/-- Extract the complete finite rooted state of an arbitrary compatible
prefix colouring at one terminal-aware cut. -/
noncomputable def sourceLocalLayerSerialRootedCumulativeStateForColorAt
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
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcrossing : ∀ step,
      color ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0) :
    SourceLocalLayerSerialRootedCumulativeState where
  toSourceLocalLayerSerialColoredCumulativeState :=
    sourceLocalLayerSerialColoredCumulativeStateForColorAt graphData minimal
      caps coloring web corridor hunique offset color hcrossing
  trackedExterior :=
    sourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt graphData
      minimal caps coloring web corridor hunique offset color

@[simp]
theorem sourceLocalLayerSerialRootedCumulativeStateForColorAt_toColored
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
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcrossing : ∀ step,
      color ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0) :
    (sourceLocalLayerSerialRootedCumulativeStateForColorAt graphData minimal
      caps coloring web corridor hunique offset color hcrossing
      ).toSourceLocalLayerSerialColoredCumulativeState =
      sourceLocalLayerSerialColoredCumulativeStateForColorAt graphData minimal
        caps coloring web corridor hunique offset color hcrossing := by
  rfl

@[simp]
theorem sourceLocalLayerSerialRootedCumulativeStateForColorAt_trackedExterior
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
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcrossing : ∀ step,
      color ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0) :
    (sourceLocalLayerSerialRootedCumulativeStateForColorAt graphData minimal
      caps coloring web corridor hunique offset color hcrossing
      ).trackedExterior =
      sourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt graphData
        minimal caps coloring web corridor hunique offset color := by
  rfl

/-- The rooted exterior code and the stable Cell carrier have the same literal
number of active coordinates. -/
theorem sourceLocalLayerSerialRootedCumulativeStateForColorAt_vertexCount
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
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcrossing : ∀ step,
      color ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0) :
    (sourceLocalLayerSerialRootedCumulativeStateForColorAt graphData minimal
      caps coloring web corridor hunique offset color hcrossing
      ).trackedExterior.vertexCount.val =
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset).card := by
  exact
    sourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt_vertexCount
      graphData minimal caps coloring web corridor hunique offset color

/-- The rooted state's exterior field exactly reconstructs literal prefix
reachability after every deletion mask on the common Cell carrier. -/
theorem sourceLocalLayerSerialRootedCumulativeStateForColorAt_reachable_iff
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
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcrossing : ∀ step,
      color ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (pair : TrackedColorPair)
    (removed : Fin
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset).card → Bool)
    (left right : SurvivingInterfaceSlot
      (fun slot : Fin
          (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
            coloring web corridor hunique offset).card =>
        ((carrierCoordinate
          (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
            coloring web corridor hunique offset)).symm slot).1)
      removed) :
    let carrier := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
      caps coloring web corridor hunique offset
    let graph := regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
      color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
    let edgeAt := fun slot : Fin carrier.card =>
      ((carrierCoordinate carrier).symm slot).1
    (restrictedByMask graph edgeAt removed).Reachable
        (edgeAt left.1) (edgeAt right.1) ↔
      Relation.ReflTransGen
        (fun first second : SurvivingInterfaceSlot edgeAt removed =>
          InterfaceExteriorFactoredStep
            ((sourceLocalLayerSerialRootedCumulativeStateForColorAt graphData
              minimal caps coloring web corridor hunique offset color hcrossing
              ).trackedExterior.code pair)
            first.1 second.1)
        left right := by
  simpa [sourceLocalLayerSerialRootedCumulativeStateForColorAt] using
    (sourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt_reachable_iff
      graphData minimal caps coloring web corridor hunique offset color pair
        removed left right)

/-- At the ambient prefix colouring the old-state projection is exactly the
input state of the already verified physical Cell factorization. -/
theorem sourceLocalLayerSerialRootedCumulativeStateForColorAt_ambient_eq_factored_input
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
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcellColor : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0) :
    (sourceLocalLayerSerialRootedCumulativeStateForColorAt graphData minimal
      caps coloring web corridor hunique offset coloring (fun _ => web.tait _)
      ).toSourceLocalLayerSerialColoredCumulativeState =
      (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt graphData minimal
        caps coloring web corridor hunique offset cellColor hcellColor).1 := by
  exact
    sourceLocalLayerSerialColoredCumulativeStateForColorAt_ambient_eq_factored_input
      graphData minimal caps coloring web corridor hunique offset cellColor
        hcellColor

end

end GoertzelV24ClosedWebLocalLayerSerialRootedCumulativeState

end Mettapedia.GraphTheory.FourColor
