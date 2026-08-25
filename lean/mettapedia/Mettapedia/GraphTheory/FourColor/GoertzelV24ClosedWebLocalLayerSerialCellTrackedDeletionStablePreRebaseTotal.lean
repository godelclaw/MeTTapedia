import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePreRebaseState
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactorTotal

/-!
# Total masked reachability of the cumulative pre-rebase state

The deletion-stable Cell state reconstructs the masked graph on surviving
carrier coordinates.  Boundary ports may nevertheless be named across the
switch even when one of their literal edges is removed.  The generic total
interface theorem retains exactly the missing reflexive case: arbitrary
coordinates are connected when their ambient edges are equal, or when both
survive and the finite closure connects them.

This file instantiates that theorem for the cumulative pre-rebase tracked
state and records the two outgoing crossings as literal coordinates of its
twenty-one-edge carrier.  It does not yet identify the four independently
named rebase roles with a mask on this carrier; that presentation comparison
is a separate geometric obligation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePreRebaseTotal

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePrefixState
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePreRebaseState
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24CorridorProfile
open GoertzelV24DeletionSensitivePortResidualFactorContraction
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorTotal
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance trackedDeletionStablePreRebaseTotalOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The updated finite state computes the total masked reachability relation
on all literal coordinates of the current Cell carrier. -/
theorem
    sourceLocalLayerSerialTrackedDeletionStablePreRebaseStateForColorAt_total_iff
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
    (pair : TrackedColorPair)
    (removed : Fin
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset).card → Bool)
    (left right : Fin
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset).card) :
    let carrier := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
      caps coloring web corridor hunique offset
    let graph := regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
    let edgeAt := fun slot : Fin carrier.card =>
      ((carrierCoordinate carrier).symm slot).1
    InterfaceExteriorTotalFactoredReachability
        ((sourceLocalLayerSerialTrackedDeletionStablePreRebaseStateForColorAt
          graphData minimal caps coloring web corridor hunique offset color
          ).code pair)
        edgeAt removed left right ↔
      (restrictedByMask graph edgeAt removed).Reachable
        (edgeAt left) (edgeAt right) := by
  dsimp only
  rw [restrictedByMask_reachable_iff_totalInterfaceExteriorClosure]
  unfold InterfaceExteriorTotalFactoredReachability
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨hleft, hright, hclosure⟩
    exact ⟨hleft, hright, hclosure.mono fun first second hstep =>
      (sourceLocalLayerSerialTrackedDeletionStablePreRebaseStateForColorAt_step_iff
        graphData minimal caps coloring web corridor hunique offset color pair
        first.1 second.1).1 hstep⟩
  · rintro ⟨hleft, hright, hclosure⟩
    exact ⟨hleft, hright, hclosure.mono fun first second hstep =>
      (sourceLocalLayerSerialTrackedDeletionStablePreRebaseStateForColorAt_step_iff
        graphData minimal caps coloring web corridor hunique offset color pair
        first.1 second.1).2 hstep⟩

/-- One outgoing crossing as an actual, unpadded coordinate of the common
Cell carrier. -/
noncomputable def sourceLocalLayerSerialTrackedRightCrossingCoordinateAt
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
    (offset : Fin (blockLength - 3)) (port : Fin 2) :
    Fin (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
      coloring web corridor hunique offset).card :=
  carrierCoordinate
    (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
      web corridor hunique offset)
    ⟨sourceLocalLayerRightCrossingAt corridor hunique offset port,
      Finset.mem_union_left _ (Finset.mem_union_left _
        (sourceLocalLayerCellRegionAt_rightCrossing corridor hunique offset
          port))⟩

@[simp]
theorem sourceLocalLayerSerialTrackedRightCrossingCoordinateAt_edge
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
    (offset : Fin (blockLength - 3)) (port : Fin 2) :
    let carrier := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
      caps coloring web corridor hunique offset
    ((carrierCoordinate carrier).symm
      (sourceLocalLayerSerialTrackedRightCrossingCoordinateAt graphData caps
        coloring web corridor hunique offset port)).1 =
      sourceLocalLayerRightCrossingAt corridor hunique offset port := by
  dsimp only
  simp [sourceLocalLayerSerialTrackedRightCrossingCoordinateAt]

/-- In particular, every masked connectivity query between the two old output
ports is computed by the updated finite cumulative state, including aliases
or a port removed by the mask. -/
theorem
    sourceLocalLayerSerialTrackedDeletionStablePreRebaseStateForColorAt_rightCrossing_iff
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
    (pair : TrackedColorPair)
    (removed : Fin
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset).card → Bool)
    (left right : Fin 2) :
    let carrier := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
      caps coloring web corridor hunique offset
    let graph := regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
    let edgeAt := fun slot : Fin carrier.card =>
      ((carrierCoordinate carrier).symm slot).1
    InterfaceExteriorTotalFactoredReachability
        ((sourceLocalLayerSerialTrackedDeletionStablePreRebaseStateForColorAt
          graphData minimal caps coloring web corridor hunique offset color
          ).code pair)
        edgeAt removed
        (sourceLocalLayerSerialTrackedRightCrossingCoordinateAt graphData caps
          coloring web corridor hunique offset left)
        (sourceLocalLayerSerialTrackedRightCrossingCoordinateAt graphData caps
          coloring web corridor hunique offset right) ↔
      (restrictedByMask graph edgeAt removed).Reachable
        (sourceLocalLayerRightCrossingAt corridor hunique offset left)
        (sourceLocalLayerRightCrossingAt corridor hunique offset right) := by
  dsimp only
  simpa using
    (sourceLocalLayerSerialTrackedDeletionStablePreRebaseStateForColorAt_total_iff
      graphData minimal caps coloring web corridor hunique offset color pair
      removed
      (sourceLocalLayerSerialTrackedRightCrossingCoordinateAt graphData caps
        coloring web corridor hunique offset left)
      (sourceLocalLayerSerialTrackedRightCrossingCoordinateAt graphData caps
        coloring web corridor hunique offset right))

end

end GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePreRebaseTotal

end Mettapedia.GraphTheory.FourColor
