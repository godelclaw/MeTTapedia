import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseTrackedState
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFaceCollar
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFullProfileRelation

/-!
# Finite tracked input attachments for an actual source boundary rebase

The four rebase roles do not include the two crossings displayed by the
pre-rebase output profile.  Recording only the component relation among the
roles therefore loses the way the accumulated prefix attaches those roles to
the old cut.

This file retains those two displayed crossings as persistent ports.  For
each tracked colour pair, a finite supported residual code records which
rebase roles attach to which old ports and which role components avoid both
ports.  Its graph-free interpretation uses the tracked-connectivity matrix of
the complete incoming zero-terminal profile.

The first adequacy theorem records the full predecessor receipt.  Because a
rebase can remove a role which was internal to a path, that receipt alone is
not a deletion-safe recurrence state.  The second state therefore records the
same finite factorization in the unchanged core, including the core relation
among the two old ports.  Its adequacy theorem is the deletion-safe input for
the later core-plus-local closure.

This file does not yet compute the successor state or assemble the complete
five-field letter.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open GoertzelV24WindingClassification
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialBoundaryRebaseTrackedInputAttachmentStateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- Exact predecessor attachments from the four rebase roles to the two
crossings displayed by the zero-terminal input profile. -/
abbrev SourceLocalLayerBoundaryRebaseTrackedInputAttachmentState :=
  TrackedColorPair →
    BoundedSupportedPortResidualCode SourceLocalLayerBoundaryRebaseRole (Fin 2)

/-- Interpret the finite attachment state through the old profile's tracked
connectivity matrix. -/
def sourceLocalLayerBoundaryRebaseTrackedInputFactoredReachability
    (state : SourceLocalLayerBoundaryRebaseTrackedInputAttachmentState)
    (input : BoundedCorridorCutProfile 2 0 4)
    (pair : TrackedColorPair)
    (left right : SourceLocalLayerBoundaryRebaseRole) : Prop :=
  SupportedPortResidualFactoredReachability (state pair)
    (fun leftPort rightPort =>
      input.profile.strandConnected pair (.inl leftPort) (.inl rightPort) = true)
    left right

/-- Extract the finite predecessor attachment state from the actual
pre-rebase cumulative region. -/
noncomputable def sourceLocalLayerBoundaryRebaseTrackedInputAttachmentStateAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    SourceLocalLayerBoundaryRebaseTrackedInputAttachmentState :=
  fun pair =>
    exactSupportedPortResidualCode
      (regionalTrackedEdgeGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        coloring (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2)
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext)
      (sourceLocalLayerRightCrossingAt corridor hunique offset)

/-- The literal old output profile is sound and complete for connectivity
among its two displayed crossing ports. -/
private theorem sourceLocalLayerSerialPreRebaseOutputProfile_portConnected_exact
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (pair : TrackedColorPair) :
    let data := sourceLocalLayerSerialPreRebaseOutputCutDataAt corridor hunique
      offset
    let graph := regionalTrackedEdgeGraph web.annular.RS data.regionEdges
      coloring (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2
    let input := sourceLocalLayerSerialPreRebaseOutputBoundedProfileAt corridor
      hunique offset
    (∀ left right : Fin 2,
      input.profile.strandConnected pair (.inl left) (.inl right) = true →
        graph.Reachable (data.portEdge (.inl left))
          (data.portEdge (.inl right))) ∧
    (∀ left right : Fin 2,
      data.portEdge (.inl left) ∈ graph.support →
      data.portEdge (.inl right) ∈ graph.support →
      graph.Reachable (data.portEdge (.inl left))
        (data.portEdge (.inl right)) →
      input.profile.strandConnected pair (.inl left) (.inl right) = true) := by
  dsimp only
  let data := sourceLocalLayerSerialPreRebaseOutputCutDataAt corridor hunique
    offset
  let graph := regionalTrackedEdgeGraph web.annular.RS data.regionEdges coloring
    (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
  let input := sourceLocalLayerSerialPreRebaseOutputBoundedProfileAt corridor
    hunique offset
  constructor
  · intro left right hconnected
    change
      (data.regionalProfile coloring (fun _ => web.tait _)
        ).strandConnected pair (.inl left) (.inl right) = true at hconnected
    exact (data.regionalProfile_strandConnected_eq_true_iff coloring
      (fun _ => web.tait _) pair (.inl left) (.inl right)).1 hconnected
        |>.2.2.2.2
  · intro left right hleftSupport hrightSupport hreachable
    rcases (SimpleGraph.mem_support graph).1 hleftSupport with
      ⟨leftNeighbor, hleftAdj⟩
    rcases (SimpleGraph.mem_support graph).1 hrightSupport with
      ⟨rightNeighbor, hrightAdj⟩
    have hraw :
        (data.regionalProfile coloring (fun _ => web.tait _)
          ).strandConnected pair (.inl left) (.inl right) = true :=
      (data.regionalProfile_strandConnected_eq_true_iff coloring
        (fun _ => web.tait _) pair (.inl left) (.inl right)).2
        ⟨sourceLocalLayerSerialPreRebaseOutputCutDataAt_portsInRegion corridor
            hunique offset (.inl left),
          sourceLocalLayerSerialPreRebaseOutputCutDataAt_portsInRegion corridor
            hunique offset (.inl right),
          hleftAdj.1.2.1, hrightAdj.1.2.1, hreachable⟩
    change
      (data.regionalProfile coloring (fun _ => web.tait _)
        ).strandConnected pair (.inl left) (.inl right) = true
    exact hraw

/-- The two-port attachment state and the complete old profile recover exact
pre-rebase tracked reachability between all four literal rebase roles. -/
theorem sourceLocalLayerBoundaryRebaseTrackedInputAttachmentStateAt_factoredReachability_iff
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
    sourceLocalLayerBoundaryRebaseTrackedInputFactoredReachability
        (sourceLocalLayerBoundaryRebaseTrackedInputAttachmentStateAt corridor
          hunique offset hnext)
        (sourceLocalLayerSerialPreRebaseOutputBoundedProfileAt corridor hunique
          offset)
        pair left right ↔
      (regionalTrackedEdgeGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        coloring (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext left)
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
          right) := by
  let data := sourceLocalLayerSerialPreRebaseOutputCutDataAt corridor hunique
    offset
  let graph := regionalTrackedEdgeGraph web.annular.RS data.regionEdges coloring
    (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
  let edgeAt := sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
  let input := sourceLocalLayerSerialPreRebaseOutputBoundedProfileAt corridor
    hunique offset
  let portConnected := fun leftPort rightPort : Fin 2 =>
    input.profile.strandConnected pair (.inl leftPort) (.inl rightPort) = true
  have hports := sourceLocalLayerSerialPreRebaseOutputProfile_portConnected_exact
    corridor hunique offset pair
  have hexact :
      graph.Reachable (edgeAt left) (edgeAt right) ↔
        SupportedPortResidualFactoredReachability
          (exactSupportedPortResidualCode graph edgeAt
            (sourceLocalLayerRightCrossingAt corridor hunique offset))
          portConnected left right := by
    exact reachable_iff_exactSupportedPortResidualFactoredReachability graph
      edgeAt (sourceLocalLayerRightCrossingAt corridor hunique offset)
      portConnected hports.1 hports.2 left right
  exact hexact.symm

/-- Deletion-safe tracked predecessor data in the common old/new core.  The
two old crossing ports need their own component relation because the complete
input profile is measured before the switch edges are removed. -/
structure SourceLocalLayerBoundaryRebaseTrackedCoreState where
  corePortConnected : TrackedColorPair → Fin 2 → Fin 2 → Bool
  coreResidual : TrackedColorPair →
    BoundedSupportedPortResidualCode SourceLocalLayerBoundaryRebaseRole (Fin 2)

private def sourceLocalLayerBoundaryRebaseTrackedCoreStateEquiv :
    SourceLocalLayerBoundaryRebaseTrackedCoreState ≃
      (TrackedColorPair → Fin 2 → Fin 2 → Bool) ×
        (TrackedColorPair → BoundedSupportedPortResidualCode
          SourceLocalLayerBoundaryRebaseRole (Fin 2)) where
  toFun state := ⟨state.corePortConnected, state.coreResidual⟩
  invFun state := ⟨state.1, state.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance :
    DecidableEq SourceLocalLayerBoundaryRebaseTrackedCoreState :=
  Classical.decEq _

noncomputable instance :
    Fintype SourceLocalLayerBoundaryRebaseTrackedCoreState := by
  exact Fintype.ofEquiv _
    sourceLocalLayerBoundaryRebaseTrackedCoreStateEquiv.symm

/-- Graph-free core reachability reconstructed through the two old crossing
ports, with port-free components retained explicitly. -/
def SourceLocalLayerBoundaryRebaseTrackedCoreState.connected
    (state : SourceLocalLayerBoundaryRebaseTrackedCoreState)
    (pair : TrackedColorPair)
    (left right : SourceLocalLayerBoundaryRebaseRole) : Prop :=
  SupportedPortResidualFactoredReachability (state.coreResidual pair)
    (fun leftPort rightPort =>
      state.corePortConnected pair leftPort rightPort = true)
    left right

/-- Extract the exact finite tracked state of the unchanged core. -/
noncomputable def sourceLocalLayerBoundaryRebaseTrackedCoreStateAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    SourceLocalLayerBoundaryRebaseTrackedCoreState where
  corePortConnected := fun pair left right => by
    classical
    exact decide
      ((regionalTrackedEdgeGraph web.annular.RS
        (sourceLocalLayerBoundaryRebaseFaceCoreRegionAt corridor hunique offset
          hnext)
        coloring (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable
        (sourceLocalLayerRightCrossingAt corridor hunique offset left)
        (sourceLocalLayerRightCrossingAt corridor hunique offset right))
  coreResidual := fun pair =>
    exactSupportedPortResidualCode
      (regionalTrackedEdgeGraph web.annular.RS
        (sourceLocalLayerBoundaryRebaseFaceCoreRegionAt corridor hunique offset
          hnext)
        coloring (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2)
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext)
      (sourceLocalLayerRightCrossingAt corridor hunique offset)

/-- The finite core state exactly recovers tracked reachability between all
four rebase roles after the changed switch support has been removed. -/
theorem sourceLocalLayerBoundaryRebaseTrackedCoreStateAt_connected_iff
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
    (sourceLocalLayerBoundaryRebaseTrackedCoreStateAt corridor hunique offset
      hnext).connected pair left right ↔
      (regionalTrackedEdgeGraph web.annular.RS
        (sourceLocalLayerBoundaryRebaseFaceCoreRegionAt corridor hunique offset
          hnext)
        coloring (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext left)
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
          right) := by
  let graph := regionalTrackedEdgeGraph web.annular.RS
    (sourceLocalLayerBoundaryRebaseFaceCoreRegionAt corridor hunique offset
      hnext)
    coloring (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2
  let edgeAt := sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
  let portAt := sourceLocalLayerRightCrossingAt corridor hunique offset
  let portConnected := fun leftPort rightPort : Fin 2 =>
    (sourceLocalLayerBoundaryRebaseTrackedCoreStateAt corridor hunique offset
      hnext).corePortConnected pair leftPort rightPort = true
  have hportSound : ∀ leftPort rightPort,
      portConnected leftPort rightPort →
        graph.Reachable (portAt leftPort) (portAt rightPort) := by
    intro leftPort rightPort hconnected
    simpa [portConnected, sourceLocalLayerBoundaryRebaseTrackedCoreStateAt,
      graph, portAt] using hconnected
  have hportComplete : ∀ leftPort rightPort,
      portAt leftPort ∈ graph.support →
      portAt rightPort ∈ graph.support →
      graph.Reachable (portAt leftPort) (portAt rightPort) →
        portConnected leftPort rightPort := by
    intro leftPort rightPort _ _ hconnected
    simpa [portConnected, sourceLocalLayerBoundaryRebaseTrackedCoreStateAt,
      graph, portAt] using hconnected
  have hexact := reachable_iff_exactSupportedPortResidualFactoredReachability
    graph edgeAt portAt portConnected hportSound hportComplete left right
  exact hexact.symm

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
