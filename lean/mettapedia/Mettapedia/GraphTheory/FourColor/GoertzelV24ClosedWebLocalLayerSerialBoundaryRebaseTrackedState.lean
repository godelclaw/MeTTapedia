import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebase
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphSupportedPortResidualFactorContraction

/-!
# Exact finite tracked state on the actual Cell boundary rebase

The four-role boundary switch is finite, but the accumulated prefix may be
arbitrarily large.  This file records exactly the information about that
prefix which tracked connectivity can observe at the switch: the nonzero
colour and regional membership of every role, together with the component
relation of each tracked two-colour graph.

The residual component code uses no persistent ports.  Thus it records the
literal component relation on the switch rather than hiding old-prefix
reachability in a purportedly local letter.  The final adequacy theorem says
that decoding the finite state is exactly the graph-derived tracked
connectivity predicate used by `CorridorCutProfile`.

This closes only the tracked predecessor-state interface of the actual
boundary rebase.  Its local update and the occurrence-sensitive facial state
remain separate obligations.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorFiniteColorTransition
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open GoertzelV24WindingClassification
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialBoundaryRebaseTrackedStateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- Exact finite predecessor data needed to interpret tracked connectivity on
the four literal boundary-rebase roles. -/
structure SourceLocalLayerBoundaryRebaseTrackedState where
  roleColor : SourceLocalLayerBoundaryRebaseRole → StrandColor
  roleInRegion : SourceLocalLayerBoundaryRebaseRole → Bool
  trackedResidual : TrackedColorPair →
    BoundedSupportedPortResidualCode
      SourceLocalLayerBoundaryRebaseRole Empty

private def sourceLocalLayerBoundaryRebaseTrackedStateEquiv :
    SourceLocalLayerBoundaryRebaseTrackedState ≃
      (SourceLocalLayerBoundaryRebaseRole → StrandColor) ×
        (SourceLocalLayerBoundaryRebaseRole → Bool) ×
          (TrackedColorPair → BoundedSupportedPortResidualCode
            SourceLocalLayerBoundaryRebaseRole Empty) where
  toFun state := ⟨state.roleColor, state.roleInRegion, state.trackedResidual⟩
  invFun state := ⟨state.1, state.2.1, state.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance :
    DecidableEq SourceLocalLayerBoundaryRebaseTrackedState :=
  Classical.decEq _

noncomputable instance :
    Fintype SourceLocalLayerBoundaryRebaseTrackedState := by
  letI : Fintype (SourceLocalLayerBoundaryRebaseRole → StrandColor) :=
    Fintype.ofFinite _
  letI : Fintype (SourceLocalLayerBoundaryRebaseRole → Bool) :=
    Fintype.ofFinite _
  letI : Fintype (TrackedColorPair → BoundedSupportedPortResidualCode
      SourceLocalLayerBoundaryRebaseRole Empty) :=
    Fintype.ofFinite _
  exact Fintype.ofEquiv _ sourceLocalLayerBoundaryRebaseTrackedStateEquiv.symm

/-- Graph-free interpretation of one tracked-connectivity bit.  Regional
membership and colour guards are retained explicitly because graph
reachability is reflexive even at an absent or untracked coordinate. -/
def SourceLocalLayerBoundaryRebaseTrackedState.connected
    (state : SourceLocalLayerBoundaryRebaseTrackedState)
    (pair : TrackedColorPair)
    (left right : SourceLocalLayerBoundaryRebaseRole) : Prop :=
  state.roleInRegion left = true ∧
    state.roleInRegion right = true ∧
    IsTrackedColor (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2 (state.roleColor left).toColor ∧
    IsTrackedColor (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2 (state.roleColor right).toColor ∧
    SupportedPortResidualFactoredReachability
      (state.trackedResidual pair) (fun _ _ : Empty => False) left right

/-- Extract the exact finite tracked predecessor state from the actual
pre-rebase cumulative region. -/
noncomputable def sourceLocalLayerBoundaryRebaseTrackedStateAt
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
      sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
  trackedResidual := fun pair =>
    exactSupportedPortResidualCode
      (regionalTrackedEdgeGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        coloring (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2)
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext)
      Empty.elim

@[simp]
theorem sourceLocalLayerBoundaryRebaseTrackedStateAt_roleColor_toColor
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (role : SourceLocalLayerBoundaryRebaseRole) :
    ((sourceLocalLayerBoundaryRebaseTrackedStateAt corridor hunique offset
      hnext).roleColor role).toColor =
      coloring (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset
        hnext role) := by
  simp [sourceLocalLayerBoundaryRebaseTrackedStateAt]

@[simp]
theorem sourceLocalLayerBoundaryRebaseTrackedStateAt_roleInRegion_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (role : SourceLocalLayerBoundaryRebaseRole) :
    (sourceLocalLayerBoundaryRebaseTrackedStateAt corridor hunique offset
        hnext).roleInRegion role = true ↔
      sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role ∈
        sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
          offset := by
  simp [sourceLocalLayerBoundaryRebaseTrackedStateAt]

/-- The finite state decodes exactly to the tracked-connectivity predicate
used by the complete graph-derived profile on the pre-rebase region. -/
theorem sourceLocalLayerBoundaryRebaseTrackedStateAt_connected_iff
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
    (sourceLocalLayerBoundaryRebaseTrackedStateAt corridor hunique offset
        hnext).connected pair left right ↔
      regionalTrackedConnectivity web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        coloring pair
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext left)
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext right) =
          true := by
  let graph := regionalTrackedEdgeGraph web.annular.RS
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
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
    sourceLocalLayerBoundaryRebaseTrackedStateAt]
  change (_ ∧ _ ∧ _ ∧ _ ∧
      SupportedPortResidualFactoredReachability
        (exactSupportedPortResidualCode graph edgeAt Empty.elim)
        (fun _ _ : Empty => False) left right) ↔
    _ ∧ _ ∧ _ ∧ _ ∧ graph.Reachable (edgeAt left) (edgeAt right)
  rw [hreachable]
  simp

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
