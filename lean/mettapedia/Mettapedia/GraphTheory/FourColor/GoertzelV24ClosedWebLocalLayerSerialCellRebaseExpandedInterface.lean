import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseDeletionSensitiveTrackedCore
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePreRebaseTotal

/-!
# An exact expanded interface for the Cell boundary rebase

The cumulative tracked state is indexed by the literal at-most-twenty-one-edge
Cell carrier.  The following boundary switch is instead named by four semantic
roles.  A successor role need not be a predecessor-carrier coordinate, and an
ambient edge may also occur under both presentations.  Therefore forcing the
four roles into a mask on the old carrier would require a false freshness or
coverage assumption.

This file uses the exact finite presentation: old carrier coordinates are the
left summand and the four semantic roles are the right summand.  The removal
mask selects the right summand.  Lean proves unconditionally that its selected
ambient vertices are exactly the literal boundary-rebase switch, including all
aliases, and hence that the restricted graph is the already proved tracked
core.  The total interface closure therefore computes every old-output-port
query after the rebase deletion.

This is a representation bridge.  The next recurrence must construct its
expanded interface code from the finite cumulative state and rebase receipt;
no reachable-state count is asserted here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedInterface

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseDeletionSensitiveTrackedCore
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseTrackedColorParametric
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePreRebaseTotal
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

local instance cellRebaseExpandedInterfaceOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The exact interface used during a boundary rebase: all predecessor Cell
coordinates plus four semantic role occurrences.  The sum deliberately keeps
aliases as distinct names for the same ambient edge. -/
abbrev SourceLocalLayerSerialCellRebaseExpandedInterface
    {E : Type*} (carrier : Finset E) :=
  Fin carrier.card ⊕ SourceLocalLayerBoundaryRebaseRole

/-- Interpret the expanded interface in the ambient edge graph. -/
noncomputable def expandedInterfaceEdgeAt
    {E : Type*} [Fintype E] [DecidableEq E] (carrier : Finset E)
    (roleAt : SourceLocalLayerBoundaryRebaseRole → E) :
    SourceLocalLayerSerialCellRebaseExpandedInterface carrier → E
  | .inl slot => ((carrierCoordinate carrier).symm slot).1
  | .inr role => roleAt role

/-- The boundary rebase removes every semantic-role occurrence and no old
coordinate occurrence.  Aliases are still removed because masks select
ambient vertices, not coordinate names. -/
def expandedInterfaceRoleMask
    {E : Type*} (carrier : Finset E) :
    SourceLocalLayerSerialCellRebaseExpandedInterface carrier → Bool
  | .inl _ => false
  | .inr _ => true

/-- The expanded mask selects exactly the ambient vertices named by the
semantic roles. -/
theorem removedBy_expandedInterfaceRoleMask_iff
    {E : Type*} [Fintype E] [DecidableEq E] (carrier : Finset E)
    (roleAt : SourceLocalLayerBoundaryRebaseRole → E) (vertex : E) :
    RemovedByInterfaceMask
        (expandedInterfaceEdgeAt carrier roleAt)
        (expandedInterfaceRoleMask carrier) vertex ↔
      ∃ role, vertex = roleAt role := by
  constructor
  · rintro ⟨slot, hremoved, heq⟩
    cases slot with
    | inl slot => simp [expandedInterfaceRoleMask] at hremoved
    | inr role =>
        exact ⟨role, by simpa [expandedInterfaceEdgeAt] using heq⟩
  · rintro ⟨role, heq⟩
    exact ⟨Sum.inr role, rfl, by simpa [expandedInterfaceEdgeAt] using heq⟩

/-- On the literal source Cell, deleting the right summand of the expanded
interface is exactly deleting the four-role switch.  No role freshness,
injectivity, or predecessor-carrier coverage is required. -/
theorem restrictedPreRebaseTrackedGraph_expandedRoleMask_eq_core
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
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair) :
    let carrier := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
      caps coloring web corridor hunique offset
    let graph := regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
    let roleAt := sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset
      hnext
    restrictedByMask graph (expandedInterfaceEdgeAt carrier roleAt)
        (expandedInterfaceRoleMask carrier) =
      coreTrackedGraphForColorAt corridor hunique offset hnext color pair := by
  dsimp only
  let carrier := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
    coloring web corridor hunique offset
  let graph := regionalTrackedEdgeGraph web.annular.RS
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
  let roleAt := sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset
    hnext
  have hpresentations :
      restrictedByMask graph (expandedInterfaceEdgeAt carrier roleAt)
          (expandedInterfaceRoleMask carrier) =
        restrictedByMask graph roleAt allBoundaryRebaseRolesRemoved := by
    apply restrictedByMask_eq_of_removedByInterfaceMask_iff_on_support
    intro vertex _hvertex
    rw [removedBy_expandedInterfaceRoleMask_iff]
    constructor
    · rintro ⟨role, heq⟩
      exact ⟨role, rfl, heq⟩
    · rintro ⟨role, _hremoved, heq⟩
      exact ⟨role, heq⟩
  rw [hpresentations]
  exact restrictedPreRebaseTrackedGraph_eq_coreTrackedGraphForColorAt corridor
    hunique offset hnext color pair

/-- The exact expanded interface code computes the tracked core connectivity
between arbitrary predecessor coordinates after the semantic-role deletion. -/
theorem exactExpandedInterface_totalFactoredReachability_iff_core
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
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair)
    (left right : Fin
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset).card) :
    let carrier := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
      caps coloring web corridor hunique offset
    let graph := regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
    let roleAt := sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset
      hnext
    let edgeAt := expandedInterfaceEdgeAt carrier roleAt
    InterfaceExteriorTotalFactoredReachability
        (exactInterfaceExteriorCode graph edgeAt)
        edgeAt (expandedInterfaceRoleMask carrier)
        (.inl left) (.inl right) ↔
      (coreTrackedGraphForColorAt corridor hunique offset hnext color pair
        ).Reachable
        (((carrierCoordinate carrier).symm left).1)
        (((carrierCoordinate carrier).symm right).1) := by
  dsimp only
  rw [exactInterfaceExteriorCode_totalFactoredReachability_iff]
  rw [restrictedPreRebaseTrackedGraph_expandedRoleMask_eq_core graphData caps
    coloring web corridor hunique offset hnext color pair]
  rfl

/-- In particular, the exact expanded code computes the rebase core relation
on the two literal old output crossings. -/
theorem exactExpandedInterface_rightCrossing_iff_core
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
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair) (left right : Fin 2) :
    let carrier := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
      caps coloring web corridor hunique offset
    let graph := regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
    let roleAt := sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset
      hnext
    let edgeAt := expandedInterfaceEdgeAt carrier roleAt
    InterfaceExteriorTotalFactoredReachability
        (exactInterfaceExteriorCode graph edgeAt)
        edgeAt (expandedInterfaceRoleMask carrier)
        (.inl (sourceLocalLayerSerialTrackedRightCrossingCoordinateAt graphData
          caps coloring web corridor hunique offset left))
        (.inl (sourceLocalLayerSerialTrackedRightCrossingCoordinateAt graphData
          caps coloring web corridor hunique offset right)) ↔
      (coreTrackedGraphForColorAt corridor hunique offset hnext color pair
        ).Reachable
        (sourceLocalLayerRightCrossingAt corridor hunique offset left)
        (sourceLocalLayerRightCrossingAt corridor hunique offset right) := by
  dsimp only
  simpa using
    (exactExpandedInterface_totalFactoredReachability_iff_core graphData caps
      coloring web corridor hunique offset hnext color pair
      (sourceLocalLayerSerialTrackedRightCrossingCoordinateAt graphData caps
        coloring web corridor hunique offset left)
      (sourceLocalLayerSerialTrackedRightCrossingCoordinateAt graphData caps
        coloring web corridor hunique offset right))

end

end GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedInterface

end Mettapedia.GraphTheory.FourColor
