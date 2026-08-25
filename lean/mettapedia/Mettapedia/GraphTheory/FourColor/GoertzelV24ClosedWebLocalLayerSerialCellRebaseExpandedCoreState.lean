import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedInterface
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactorTotalGraph

/-!
# Decode the expanded Cell interface into the tracked rebase core

The exact expanded interface records all predecessor Cell coordinates and all
four semantic rebase roles.  This file turns its total masked component
relation into the finite `SourceLocalLayerBoundaryRebaseTrackedCoreState`
already consumed by the successor recurrence.

The construction is graph-free after receiving the expanded code: it builds a
finite component graph on the named interface, uses the two old output
crossings as persistent ports, and extracts the existing supported residual
factor.  For the canonical source code, Lean proves that the decoded state is
exactly the literal unchanged core.  Thus the deletion-safe state reaches the
old core-plus-local recurrence without an active-role coverage assumption.

This is still a factorization interface.  A later theorem must update the
expanded code from the cumulative state and the literal rebase receipt before
any reachable-state closure is measured.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedCoreState

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseTrackedColorParametric
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedInterface
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePreRebaseTotal
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorTotalGraph
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cellRebaseExpandedCoreStateOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- Interpret one expanded interface code as a finite tracked core state.  The
two persistent ports are coordinates in the predecessor Cell carrier; the
four semantic roles occupy the right summand independently of aliases. -/
noncomputable def trackedCoreStateOfExpandedInterfaceCode
    {E : Type*} [Fintype E] [DecidableEq E]
    (carrier : Finset E)
    (roleAt : SourceLocalLayerBoundaryRebaseRole → E)
    (code : TrackedColorPair →
      BoundedInterfaceExteriorCode
        (SourceLocalLayerSerialCellRebaseExpandedInterface carrier))
    (portCoordinate : Fin 2 → Fin carrier.card) :
    SourceLocalLayerBoundaryRebaseTrackedCoreState where
  corePortConnected := fun pair left right => by
    classical
    exact decide
      ((totalFactoredComponentGraph (code pair)
        (expandedInterfaceEdgeAt carrier roleAt)
        (expandedInterfaceRoleMask carrier)).Reachable
        (.inl (portCoordinate left)) (.inl (portCoordinate right)))
  coreResidual := fun pair =>
    exactSupportedPortResidualCode
      (totalFactoredComponentGraph (code pair)
        (expandedInterfaceEdgeAt carrier roleAt)
        (expandedInterfaceRoleMask carrier))
      (fun role => Sum.inr role)
      (fun port => Sum.inl (portCoordinate port))

/-- The decoded core state presents exactly the connected components of the
finite total-reachability graph on the four semantic roles. -/
theorem trackedCoreStateOfExpandedInterfaceCode_connected_iff
    {E : Type*} [Fintype E] [DecidableEq E]
    (carrier : Finset E)
    (roleAt : SourceLocalLayerBoundaryRebaseRole → E)
    (code : TrackedColorPair →
      BoundedInterfaceExteriorCode
        (SourceLocalLayerSerialCellRebaseExpandedInterface carrier))
    (portCoordinate : Fin 2 → Fin carrier.card)
    (pair : TrackedColorPair)
    (left right : SourceLocalLayerBoundaryRebaseRole) :
    (trackedCoreStateOfExpandedInterfaceCode carrier roleAt code
      portCoordinate).connected pair left right ↔
      (totalFactoredComponentGraph (code pair)
        (expandedInterfaceEdgeAt carrier roleAt)
        (expandedInterfaceRoleMask carrier)).Reachable
        (.inr left) (.inr right) := by
  let graph := totalFactoredComponentGraph (code pair)
    (expandedInterfaceEdgeAt carrier roleAt)
    (expandedInterfaceRoleMask carrier)
  let roleVertex := fun role : SourceLocalLayerBoundaryRebaseRole =>
    (Sum.inr role : SourceLocalLayerSerialCellRebaseExpandedInterface carrier)
  let portVertex := fun port : Fin 2 =>
    (Sum.inl (portCoordinate port) :
      SourceLocalLayerSerialCellRebaseExpandedInterface carrier)
  let portConnected := fun first second : Fin 2 =>
    (trackedCoreStateOfExpandedInterfaceCode carrier roleAt code
      portCoordinate).corePortConnected pair first second = true
  have hportSound : ∀ first second,
      portConnected first second →
        graph.Reachable (portVertex first) (portVertex second) := by
    intro first second hconnected
    simpa [portConnected, trackedCoreStateOfExpandedInterfaceCode, graph,
      portVertex] using hconnected
  have hportComplete : ∀ first second,
      portVertex first ∈ graph.support →
      portVertex second ∈ graph.support →
      graph.Reachable (portVertex first) (portVertex second) →
        portConnected first second := by
    intro first second _ _ hconnected
    simpa [portConnected, trackedCoreStateOfExpandedInterfaceCode, graph,
      portVertex] using hconnected
  have hexact := reachable_iff_exactSupportedPortResidualFactoredReachability
    graph roleVertex portVertex portConnected hportSound hportComplete
      left right
  exact hexact.symm

/-- Decode the literal pre-rebase tracked graphs, one per tracked color pair,
through their exact expanded interface codes. -/
noncomputable def sourceLocalLayerSerialCellRebaseExpandedCoreStateAt
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
    (hnext : offset.val + 1 < blockLength - 3) :
    SourceLocalLayerBoundaryRebaseTrackedCoreState :=
  let carrier := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
    caps coloring web corridor hunique offset
  let roleAt := sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset
    hnext
  let edgeAt := expandedInterfaceEdgeAt carrier roleAt
  trackedCoreStateOfExpandedInterfaceCode carrier roleAt
    (fun pair => exactInterfaceExteriorCode
      (regionalTrackedEdgeGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        coloring (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2)
      edgeAt)
    (sourceLocalLayerSerialTrackedRightCrossingCoordinateAt graphData caps
      coloring web corridor hunique offset)

/-- The decoded source state is exactly the literal unchanged tracked core on
all four semantic roles. -/
theorem sourceLocalLayerSerialCellRebaseExpandedCoreStateAt_connected_iff
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
    (pair : TrackedColorPair)
    (left right : SourceLocalLayerBoundaryRebaseRole) :
    (sourceLocalLayerSerialCellRebaseExpandedCoreStateAt graphData caps coloring
      web corridor hunique offset hnext).connected pair left right ↔
      (coreTrackedGraphForColorAt corridor hunique offset hnext coloring pair
        ).Reachable
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext left)
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
          right) := by
  let carrier := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
    caps coloring web corridor hunique offset
  let graph := regionalTrackedEdgeGraph web.annular.RS
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    coloring (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2
  let roleAt := sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset
    hnext
  let edgeAt := expandedInterfaceEdgeAt carrier roleAt
  let code := fun trackedPair : TrackedColorPair => exactInterfaceExteriorCode
    (regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      coloring (trackedColorPairColors trackedPair).1
        (trackedColorPairColors trackedPair).2)
    edgeAt
  let portCoordinate :=
    sourceLocalLayerSerialTrackedRightCrossingCoordinateAt graphData caps
      coloring web corridor hunique offset
  rw [show sourceLocalLayerSerialCellRebaseExpandedCoreStateAt graphData caps
      coloring web corridor hunique offset hnext =
        trackedCoreStateOfExpandedInterfaceCode carrier roleAt code
          portCoordinate by rfl]
  rw [trackedCoreStateOfExpandedInterfaceCode_connected_iff carrier roleAt code
    portCoordinate pair left right]
  rw [show code pair = exactInterfaceExteriorCode graph edgeAt by rfl]
  rw [exactInterfaceExteriorCode_totalFactoredComponentGraph_reachable_iff]
  rw [restrictedPreRebaseTrackedGraph_expandedRoleMask_eq_core graphData caps
    coloring web corridor hunique offset hnext coloring pair]
  rfl

end

end GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedCoreState

end Mettapedia.GraphTheory.FourColor
