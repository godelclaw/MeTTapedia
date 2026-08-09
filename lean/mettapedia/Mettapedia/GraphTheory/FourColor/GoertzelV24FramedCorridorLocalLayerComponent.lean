import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorLocalLayerSeparator
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalCutBond

/-!
# Exact deletion component of a source corridor layer

A source-realized local layer cycle already gives a literal four-edge wall.
Here the wall is promoted from mere disconnection to its exact graph-side
boundary: deleting it constructs a component, and every listed wall edge
crosses that component.  This is the component/removed/boundary portion of
the source splice geometry, proved for the actual framed cellulation rather
than supplied as a chord-side premise.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CleanHexCorridor
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24DualCycleBond
open GoertzelV24DualCycleSeparator
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteEdgeDeletion
open GoertzelV24FramedDualCycleSeparator
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance corridorLayerComponentGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceConsecutiveSlabInterface

variable {source : SourceTrail G}
  {embedded : source.AnnularEmbedding} {blockLength : Nat}
  {realization : BoundaryCleanCorridorRealization embedded blockLength}
  {htwoSided : OrbitFacesTwoSided
    embedded.cellulation.rotation.toRotationSystem}
  {hunique : PairwiseUniqueSharedInteriorEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
  {leftInterior : CorridorInterior blockLength}
  {hnext : leftInterior.center.val + 2 < blockLength}

/-- The literal finite wall crossed by a source slab's two local layers. -/
noncomputable def localLayerLoopCutEdges
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) : Finset G.edgeSet :=
  dualWalkCrossingEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
    interface.localLayerLoop

/-- The source slab wall has exactly four different primal edges. -/
theorem localLayerLoopCutEdges_card_eq_four
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.localLayerLoopCutEdges.card = 4 := by
  rw [localLayerLoopCutEdges,
    card_dualWalkCrossingEdges_eq_length_of_isCycle
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))
      (orbitFace_incidence_le_two embedded.cellulation.rotation.toRotationSystem)
      hunique interface.localLayerLoop interface.localLayerLoop_isCycle]
  simp [SourceConsecutiveSlabInterface.localLayerLoop,
    interface.localLayer_walk_length_eq_two,
    interface.nextLocalLayer_walk_length_eq_two]

/-- A nontrivial finite edge deletion in a connected graph has a component
with a nonempty original-graph boundary whenever a different deletion
component exists. -/
private theorem componentCrossingEdges_nonempty_of_distinct
    (hconnected : G.Connected) (removed : Finset G.edgeSet)
    (inside outside :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent)
    (hdistinct : inside ≠ outside) :
    (componentCrossingEdges removed inside).Nonempty := by
  rcases inside.nonempty_supp with ⟨insideVertex, hinside⟩
  rcases outside.nonempty_supp with ⟨outsideVertex, houtside⟩
  have houtsideNotInside : outsideVertex ∉ inside.supp := by
    intro hcommon
    apply hdistinct
    exact SimpleGraph.ConnectedComponent.eq_of_common_vertex hcommon houtside
  rcases hconnected insideVertex outsideVertex with ⟨walk⟩
  rcases exists_edgeCrossesVertexSide_of_walk_endpoint_sides
      (fun vertex => vertex ∈ inside.supp) walk hinside houtsideNotInside with
    ⟨edge, _hwalkEdge, hcross⟩
  exact ⟨edge,
    (mem_componentCrossingEdges_iff removed inside edge).2 hcross⟩

/-- A local source layer supplies a genuine finite deletion component whose
computed graph boundary is exactly the four primal edges crossed by the
facial-dual layer loop.  This is the bridge from the source's cell geometry
to a splice-ready vertex side. -/
theorem exists_localLayerLoop_component_exactBoundary
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    ∃ component : (G.deleteEdges
        (edgeFinsetValueSet interface.localLayerLoopCutEdges)).ConnectedComponent,
      componentCrossingEdges interface.localLayerLoopCutEdges component =
        interface.localLayerLoopCutEdges := by
  have hcut :
      dualWalkPrimalCut embedded.cellulation.rotation hunique
        interface.localLayerLoop =
        edgeFinsetValueSet interface.localLayerLoopCutEdges := by
    exact dualWalkPrimalCut_eq_edgeFinsetValueSet_dualWalkCrossingEdges
      embedded.cellulation.rotation hunique interface.localLayerLoop
  have hnotConnected : ¬ (G.deleteEdges
      (edgeFinsetValueSet interface.localLayerLoopCutEdges)).Connected := by
    rw [← hcut]
    exact interface.localLayerLoop_crossings_disconnect
  rcases exists_distinct_components_of_not_connected
      embedded.cellulation.connected interface.localLayerLoopCutEdges
      hnotConnected with ⟨inside, outside, hdistinct⟩
  refine ⟨inside, ?_⟩
  have hsubset : crossingEdgeFinset G (fun vertex => vertex ∈ inside.supp) ⊆
      interface.localLayerLoopCutEdges := by
    rw [← componentCrossingEdges_eq_crossingEdgeFinset
      interface.localLayerLoopCutEdges inside]
    exact componentCrossingEdges_subset_removed interface.localLayerLoopCutEdges
      inside
  have hnonempty :
      (crossingEdgeFinset G (fun vertex => vertex ∈ inside.supp)).Nonempty := by
    rw [← componentCrossingEdges_eq_crossingEdgeFinset
      interface.localLayerLoopCutEdges inside]
    exact componentCrossingEdges_nonempty_of_distinct
      embedded.cellulation.connected interface.localLayerLoopCutEdges
      inside outside hdistinct
  have hboundary : crossingEdgeFinset G (fun vertex => vertex ∈ inside.supp) =
      interface.localLayerLoopCutEdges := by
    exact crossingEdgeFinset_eq_dualWalkCrossingEdges_of_isCycle_of_subset
      embedded.cellulation.rotation htwoSided hunique interface.localLayerLoop
      interface.localLayerLoop_isCycle (fun vertex => vertex ∈ inside.supp)
      hsubset hnonempty
  rw [componentCrossingEdges_eq_crossingEdgeFinset]
  exact hboundary

end SourceConsecutiveSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
