import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteFaceReceiptProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseTrackedState

/-!
# Exact finite tracked state on the successor side of a source rebase

The earlier tracked receipt describes the pre-rebase cumulative region,
whereas the finite facial receipt describes the next terminal-aware input.
Those times must not be silently mixed.  This file extracts the same finite
tracked state from the successor region and proves that its crossing colours
and tracked-connectivity relation are exactly the corresponding fields of the
literal successor profile.

This is still relational source evidence.  It does not claim that the
predecessor tracked state determines the successor state.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexCorridorFiniteColorTransition
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open GoertzelV24WindingClassification
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialBoundaryRebaseSuccessorTrackedProfileEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The rebase role occupied by one port of the next terminal-aware input. -/
def sourceLocalLayerBoundaryRebaseSuccessorPortRole :
    CorridorPort 2 1 → SourceLocalLayerBoundaryRebaseRole
  | .inl step => .inr (.inl step)
  | .inr _ => .inr (.inr (0 : Fin 1))

/-- The port-role map denotes the literal edge used by the successor cut. -/
@[simp]
theorem sourceLocalLayerBoundaryRebaseEdgeAt_successorPortRole
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (port : CorridorPort 2 1) :
    sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
        (sourceLocalLayerBoundaryRebaseSuccessorPortRole port) =
      (sourceLocalLayerBoundaryRebaseSuccessorCutDataAt corridor hunique offset
        hnext).portEdge port := by
  rcases port with crossing | terminal
  · rfl
  · exact Fin.eq_zero terminal ▸ rfl

/-- Exact finite tracked data of the next terminal-aware input, expressed on
the four stable rebase roles. -/
noncomputable def sourceLocalLayerBoundaryRebaseSuccessorTrackedStateAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    SourceLocalLayerBoundaryRebaseTrackedState where
  roleColor := fun role =>
    strandColorOfNonzero
      (coloring (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique
        offset hnext role))
      (web.tait _)
  roleInRegion := fun role => decide
    (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role ∈
      sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext))
  trackedResidual := fun pair =>
    exactSupportedPortResidualCode
      (regionalTrackedEdgeGraph web.annular.RS
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext))
        coloring (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2)
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext)
      Empty.elim

@[simp]
theorem sourceLocalLayerBoundaryRebaseSuccessorTrackedStateAt_roleColor_toColor
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (role : SourceLocalLayerBoundaryRebaseRole) :
    ((sourceLocalLayerBoundaryRebaseSuccessorTrackedStateAt corridor hunique
      offset hnext).roleColor role).toColor =
      coloring (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset
        hnext role) := by
  simp [sourceLocalLayerBoundaryRebaseSuccessorTrackedStateAt]

/-- The successor state decodes exactly to the successor regional tracked
graph on all four stable roles. -/
theorem sourceLocalLayerBoundaryRebaseSuccessorTrackedStateAt_connected_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (pair : TrackedColorPair)
    (left right : SourceLocalLayerBoundaryRebaseRole) :
    (sourceLocalLayerBoundaryRebaseSuccessorTrackedStateAt corridor hunique
        offset hnext).connected pair left right ↔
      regionalTrackedConnectivity web.annular.RS
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext))
        coloring pair
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext left)
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext right) =
          true := by
  let graph := regionalTrackedEdgeGraph web.annular.RS
    (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
      (sourceLocalLayerNextOffset offset hnext))
    coloring (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2
  let edgeAt := sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
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
    sourceLocalLayerBoundaryRebaseSuccessorTrackedStateAt]
  change (_ ∧ _ ∧ _ ∧ _ ∧
      SupportedPortResidualFactoredReachability
        (exactSupportedPortResidualCode graph edgeAt Empty.elim)
        (fun _ _ : Empty => False) left right) ↔
    _ ∧ _ ∧ _ ∧ _ ∧ graph.Reachable (edgeAt left) (edgeAt right)
  rw [hreachable]
  simp

/-- The successor tracked state supplies exactly the crossing-colour field of
the literal successor profile. -/
theorem sourceLocalLayerBoundaryRebaseSuccessorTrackedStateAt_edgeColor_profile
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (crossing : Fin 2) :
    (sourceLocalLayerBoundaryRebaseSuccessorTrackedStateAt corridor hunique
      offset hnext).roleColor
        (sourceLocalLayerBoundaryRebaseSuccessorPortRole (.inl crossing)) =
      (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).profile.edgeColor crossing := by
  apply StrandColor.toColor_injective
  rw [sourceLocalLayerBoundaryRebaseSuccessorTrackedStateAt_roleColor_toColor,
    sourceLocalLayerBoundaryRebaseEdgeAt_successorPortRole]
  exact (sourceLocalLayerBoundaryRebaseSuccessorCutDataAt corridor hunique
    offset hnext).regionalProfile_edgeColor_toColor coloring
      (fun _ => web.tait _) crossing |>.symm

/-- The successor tracked state supplies exactly every tracked-connectivity
bit of the literal successor profile, including the seam terminal. -/
theorem sourceLocalLayerBoundaryRebaseSuccessorTrackedStateAt_connected_profile
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (pair : TrackedColorPair) (left right : CorridorPort 2 1) :
    (sourceLocalLayerBoundaryRebaseSuccessorTrackedStateAt corridor hunique
      offset hnext).connected pair
        (sourceLocalLayerBoundaryRebaseSuccessorPortRole left)
        (sourceLocalLayerBoundaryRebaseSuccessorPortRole right) ↔
      (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).profile.strandConnected
          pair left right = true := by
  rw [sourceLocalLayerBoundaryRebaseSuccessorTrackedStateAt_connected_iff]
  change _ ↔
    ((sourceLocalLayerBoundaryRebaseSuccessorCutDataAt corridor hunique offset
      hnext).regionalProfile coloring (fun _ => web.tait _)
      ).strandConnected pair left right = true
  rw [(sourceLocalLayerBoundaryRebaseSuccessorCutDataAt corridor hunique offset
    hnext).regionalProfile_strandConnected_eq_true_iff]
  simp only [sourceLocalLayerBoundaryRebaseEdgeAt_successorPortRole,
    sourceLocalLayerBoundaryRebaseSuccessorCutDataAt,
    sourceLocalLayerSerialTerminalInputCutDataAt_regionEdges]
  rw [regionalTrackedConnectivity_eq_true_iff]

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
