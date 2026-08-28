import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedBoundaryRebase
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseSuccessorTrackedProfile

/-!
# Exact selected successor of one boundary rebase

This file identifies the successor terminal-aware cut of a pointwise-selected
Cell and extracts its exact four-role tracked state at an arbitrary positive
colour function.  It is the semantic endpoint which a finite rebase receipt
must decode.

Only the selected annular-interior geometry is used.  The graph-free state and
successor-port role map are deliberately shared with the established finite
rebase ABI.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24HexCorridorFiniteColorTransition
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open GoertzelV24WindingClassification
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedBoundaryRebaseSuccessorEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Formation

open Instance.LocalLayerFormation

/-- The literal successor cut following one pointwise-selected rebase. -/
noncomputable def pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorCutDataAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :=
  pointwiseSelectedSourceLocalLayerSerialTerminalInputCutDataAt formation
    corridor hinterior (sourceLocalLayerNextOffset offset hnext)

/-- The stable successor port role denotes exactly the corresponding selected
successor-cut edge. -/
@[simp]
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt_successorPortRole
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (port : CorridorPort 2 1) :
    pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation corridor
        hinterior offset hnext
        (sourceLocalLayerBoundaryRebaseSuccessorPortRole port) =
      (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorCutDataAt
        formation corridor hinterior offset hnext).portEdge port := by
  rcases port with crossing | terminal
  · rfl
  · exact Fin.eq_zero terminal ▸ rfl

/-- Positivity on all four rebase roles supplies positivity on the two
successor crossing edges. -/
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorCrossingNonzeroForColorAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color)
    (hrole : ∀ role,
      color (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation
        corridor hinterior offset hnext role) ≠ 0) :
    ∀ step,
      color (pointwiseSelectedSourceLocalLayerLeftCrossingAt formation corridor
        hinterior (sourceLocalLayerNextOffset offset hnext) step) ≠ 0 := by
  intro step
  exact hrole (.inr (.inl step))

/-- The exact selected successor profile at an arbitrary positive role
colouring. -/
noncomputable def pointwiseSelectedSourceLocalLayerBoundaryRebaseOutputForColorAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color)
    (hrole : ∀ role,
      color (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation
        corridor hinterior offset hnext role) ≠ 0) :
    BoundedCorridorCutProfile 2 1 4 :=
  pointwiseSelectedSourceLocalLayerSerialTerminalInputBoundedProfileAt formation
    corridor hinterior (sourceLocalLayerNextOffset offset hnext) color
      (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorCrossingNonzeroForColorAt
        formation corridor hinterior offset hnext color hrole)

/-- Exact finite tracked data of the selected successor, expressed on all four
stable rebase roles. -/
noncomputable def pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color)
    (hrole : ∀ role,
      color (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation
        corridor hinterior offset hnext role) ≠ 0) :
    SourceLocalLayerBoundaryRebaseTrackedState where
  roleColor := fun role =>
    strandColorOfNonzero
      (color (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation
        corridor hinterior offset hnext role)) (hrole role)
  roleInRegion := fun role => decide
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation corridor
        hinterior offset hnext role ∈
      pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
        corridor hinterior (sourceLocalLayerNextOffset offset hnext))
  trackedResidual := fun pair =>
    exactSupportedPortResidualCode
      (regionalTrackedEdgeGraph formation.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
          corridor hinterior (sourceLocalLayerNextOffset offset hnext))
        color (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2)
      (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation corridor
        hinterior offset hnext)
      Empty.elim

@[simp]
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt_roleColor_toColor
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color)
    (hrole : ∀ role,
      color (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation
        corridor hinterior offset hnext role) ≠ 0)
    (role : SourceLocalLayerBoundaryRebaseRole) :
    ((pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt
      formation corridor hinterior offset hnext color hrole).roleColor
        role).toColor =
      color (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation
        corridor hinterior offset hnext role) := by
  simp [pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt]

/-- The selected successor state decodes exactly to regional tracked
connectivity on all four stable roles. -/
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt_connected_iff
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color)
    (hrole : ∀ role,
      color (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation
        corridor hinterior offset hnext role) ≠ 0)
    (pair : TrackedColorPair)
    (left right : SourceLocalLayerBoundaryRebaseRole) :
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt
        formation corridor hinterior offset hnext color hrole).connected pair
          left right ↔
      regionalTrackedConnectivity formation.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
          corridor hinterior (sourceLocalLayerNextOffset offset hnext))
        color pair
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation corridor
          hinterior offset hnext left)
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation corridor
          hinterior offset hnext right) = true := by
  let graph := regionalTrackedEdgeGraph formation.annular.RS
    (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
      corridor hinterior (sourceLocalLayerNextOffset offset hnext))
    color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
  let edgeAt := pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation
    corridor hinterior offset hnext
  have hreachable :
      graph.Reachable (edgeAt left) (edgeAt right) ↔
        SupportedPortResidualFactoredReachability
          (exactSupportedPortResidualCode graph edgeAt Empty.elim)
          (fun _ _ : Empty => False) left right := by
    apply reachable_iff_exactSupportedPortResidualFactoredReachability
    · intro port
      exact port.elim
    · intro port
      exact port.elim
  rw [regionalTrackedConnectivity_eq_true_iff]
  simp only [SourceLocalLayerBoundaryRebaseTrackedState.connected,
    pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt]
  change (_ ∧ _ ∧ _ ∧ _ ∧
      SupportedPortResidualFactoredReachability
        (exactSupportedPortResidualCode graph edgeAt Empty.elim)
        (fun _ _ : Empty => False) left right) ↔
    _ ∧ _ ∧ _ ∧ _ ∧ graph.Reachable (edgeAt left) (edgeAt right)
  rw [hreachable]
  simp

/-- The selected successor state supplies exactly the successor crossing
colours. -/
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt_edgeColor_output
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color)
    (hrole : ∀ role,
      color (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation
        corridor hinterior offset hnext role) ≠ 0)
    (crossing : Fin 2) :
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt
      formation corridor hinterior offset hnext color hrole).roleColor
        (sourceLocalLayerBoundaryRebaseSuccessorPortRole (.inl crossing)) =
      (pointwiseSelectedSourceLocalLayerBoundaryRebaseOutputForColorAt formation
        corridor hinterior offset hnext color hrole).profile.edgeColor
          crossing := by
  apply StrandColor.toColor_injective
  rw [pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt_roleColor_toColor,
    pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt_successorPortRole]
  exact
    ((pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorCutDataAt
      formation corridor hinterior offset hnext).regionalProfile_edgeColor_toColor
        color
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorCrossingNonzeroForColorAt
          formation corridor hinterior offset hnext color hrole)
        crossing).symm

/-- The selected successor state supplies exactly every tracked-connectivity
bit of the successor profile, including the terminal rung. -/
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt_connected_output
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color)
    (hrole : ∀ role,
      color (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation
        corridor hinterior offset hnext role) ≠ 0)
    (pair : TrackedColorPair) (left right : CorridorPort 2 1) :
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt
      formation corridor hinterior offset hnext color hrole).connected pair
        (sourceLocalLayerBoundaryRebaseSuccessorPortRole left)
        (sourceLocalLayerBoundaryRebaseSuccessorPortRole right) ↔
      (pointwiseSelectedSourceLocalLayerBoundaryRebaseOutputForColorAt formation
        corridor hinterior offset hnext color hrole).profile.strandConnected
          pair left right = true := by
  rw [pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorTrackedStateForColorAt_connected_iff]
  change _ ↔
    ((pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorCutDataAt formation
      corridor hinterior offset hnext).regionalProfile color
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorCrossingNonzeroForColorAt
          formation corridor hinterior offset hnext color hrole)
      ).strandConnected pair left right = true
  rw [(pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorCutDataAt formation
    corridor hinterior offset hnext).regionalProfile_strandConnected_eq_true_iff]
  simp only [pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt_successorPortRole,
    pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorCutDataAt,
    pointwiseSelectedSourceLocalLayerSerialTerminalInputCutDataAt_regionEdges]
  rw [regionalTrackedConnectivity_eq_true_iff]

end Formation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
