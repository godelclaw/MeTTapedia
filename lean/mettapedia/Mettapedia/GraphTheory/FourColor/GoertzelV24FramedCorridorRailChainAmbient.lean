import Mettapedia.GraphTheory.FourColor.GoertzelV24DeleteEdgesCyclicCutPullback
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorRailChainComponent

/-!
# Transporting a source rail shore to the closed ambient graph

The source corridor is represented on a graph with one edge deleted.  The
physical D3 consumer, however, lives on the original closed cubic graph.  This
file closes that representation seam.  Connected vertex sides survive when
the missing edge is restored, the source outer-container cycle survives by
the canonical graph inclusion, and the ambient cubic degree condition then
gives nonempty proper majority data for the literal incident-edge shore.

The restored edge is allowed to cross the source side.  Thus the theorem does
not smuggle in a noncrossing premise or claim that the source cut-edge finset
is literally unchanged in the ambient graph.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedCorridorRailChainAmbient

open GoertzelV24CleanHexCorridor
open GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24ConnectedVertexSideEdgeShore
open GoertzelV24DeleteEdgesCyclicCutPullback
open GoertzelV24DeletedEdgeTrail
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24FramedCorridorRailChainComponent
open GoertzelV24FramedTrail
open GoertzelV24FramedTrail.SourceTrail
open GoertzelV24FramedTrail.SourceTrail.AnnularEmbedding
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

/-- Connectedness of an induced vertex side is preserved when deleted edges
are restored. -/
theorem connected_induce_of_deleteEdges
    (removed : Set (Sym2 V)) (side : V → Prop)
    (hconnected : ((G.deleteEdges removed).induce side).Connected) :
    (G.induce side).Connected := by
  apply hconnected.mono
  intro x y hxy
  exact (G.deleteEdges_le removed) hxy

/-- Consumer-facing ambient certificate for a boundary-separated source rail
segment.  The exact source boundary is retained as provenance; on the closed
ambient cubic graph the same vertex bipartition has connected induced sides,
connected complementary incident-edge shores, and a nonempty proper majority
core. -/
theorem alignedBoundary_ambientInnerIncidentShore_certificate
    {u v : V} (huv : G.Adj u v)
    {source : SourceTrail (DeletedEdgeGraph G u v)}
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
    {hnextNext :
      (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    {hnextThird :
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hnext) hnextNext).center.val + 2 <
          blockLength}
    {first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext}
    {last : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hnext) hnextNext) hnextThird}
    (chain : SourceCornerAlignedRailChain first last)
    (hseparation : chain.BoundarySeparation)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3) :
    let component := alignedBoundaryOuterComponent chain
    let innerSide : V → Prop := fun vertex ↦ vertex ∉ component.supp
    let outerSide : V → Prop := fun vertex ↦ vertex ∈ component.supp
    componentCrossingEdges (alignedBoundaryCutEdges chain) component =
        alignedBoundaryCutEdges chain ∧
      (G.induce innerSide).Connected ∧
      (G.induce outerSide).Connected ∧
      EdgeShoreConnected G (incidentEdgeShore G innerSide) ∧
      EdgeShoreConnected G
        (Finset.univ \ incidentEdgeShore G innerSide) ∧
      (∃ vertex, majorityVertexSide G
        (incidentEdgeShore G innerSide) vertex) ∧
      (∃ vertex, ¬ majorityVertexSide G
        (incidentEdgeShore G innerSide) vertex) := by
  dsimp only
  classical
  have _hrestoredEdge : s(u, v) ∈ G.edgeSet := huv
  let component := alignedBoundaryOuterComponent chain
  let innerSide : V → Prop := fun vertex ↦ vertex ∉ component.supp
  let outerSide : V → Prop := fun vertex ↦ vertex ∈ component.supp
  rcases alignedBoundaryOuterComponent_exactBoundary_connectedSides
      chain hseparation with ⟨hboundary, houterDeleted, hinnerDeleted⟩
  have hinnerAmbient : (G.induce innerSide).Connected :=
    connected_induce_of_deleteEdges ({s(u, v)} : Set (Sym2 V)) innerSide
      hinnerDeleted
  have houterAmbient : (G.induce outerSide).Connected :=
    connected_induce_of_deleteEdges ({s(u, v)} : Set (Sym2 V)) outerSide
      houterDeleted
  have hpredicate : (fun vertex ↦ ¬ innerSide vertex) = outerSide := by
    funext vertex
    apply propext
    change (¬ ¬ vertex ∈ component.supp) ↔ vertex ∈ component.supp
    exact Classical.not_not
  have houterAmbient' :
      (G.induce (fun vertex ↦ ¬ innerSide vertex)).Connected := by
    rw [hpredicate]
    exact houterAmbient
  have hconnectedShores := connected_edgeShores_of_connected_vertexSides
    (G := G) innerSide hinnerAmbient houterAmbient'
  rcases exists_inner_vertex_two_le_degree chain hseparation with
    ⟨innerVertex, hinnerVertex, _hinnerDegree⟩
  have hmajority : ∃ vertex, majorityVertexSide G
      (incidentEdgeShore G innerSide) vertex :=
    exists_majorityVertexSide_incidentEdgeShore hcubic innerSide
      ⟨innerVertex, hinnerVertex⟩
  have houterCycleDeleted :=
    outerContainer_hasCycleOn_alignedBoundaryOuterComponent
      chain hseparation
  have houterCycleAmbient : HasCycleOnSide G outerSide := by
    exact hasCycleOnSide_of_deleteEdges ({s(u, v)} : Set (Sym2 V))
      outerSide houterCycleDeleted
  have hcomplementCycleAmbient :
      HasCycleOnSide G (fun vertex ↦ ¬ innerSide vertex) := by
    rw [hpredicate]
    exact houterCycleAmbient
  have hnotMajority : ∃ vertex, ¬ majorityVertexSide G
      (incidentEdgeShore G innerSide) vertex :=
    exists_not_majorityVertexSide_incidentEdgeShore_of_complement_cycle
      hcubic innerSide hcomplementCycleAmbient
  exact ⟨hboundary, hinnerAmbient, houterAmbient,
    hconnectedShores.1, hconnectedShores.2, hmajority, hnotMajority⟩

end

end GoertzelV24FramedCorridorRailChainAmbient

end Mettapedia.GraphTheory.FourColor
