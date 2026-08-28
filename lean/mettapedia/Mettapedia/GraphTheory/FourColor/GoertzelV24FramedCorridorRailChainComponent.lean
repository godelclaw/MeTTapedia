import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorRailChainBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedDualCycleExactBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedAnnularFaceParityCut
import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedVertexSideEdgeShore

/-!
# Exact shore bounded by a finite source rail chain

The literal source corridor supplies two facial-dual rails.  Under the exact
noncollision data of `BoundarySeparation`, the endpoint transverse layers and
those rails form a simple dual cycle.  The generic framed-cycle separator then
turns that cycle into a deletion component whose primal boundary is exactly
the set of crossed edges.

This is the first graph-facing output of a nonlocal source rail chain.  It does
not assume a profile equality or a ready-made cut, and it makes no claim yet
about nesting shores from chains with different right endpoints.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedCorridorRailChainComponent

open GoertzelV24CleanHexCorridor
open GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24ConnectedVertexSideEdgeShore
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24FramedDualCycleExactBoundary
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24FramedTrail
open GoertzelV24FramedTrail.SourceTrail
open GoertzelV24FramedTrail.SourceTrail.AnnularEmbedding
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

/-- The finite primal boundary crossed by a source rail-chain cycle. -/
noncomputable def alignedBoundaryCutEdges
    {source : SourceTrail G}
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
    (chain : SourceCornerAlignedRailChain first last) : Finset G.edgeSet :=
  dualWalkCrossingEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
    chain.alignedBoundaryWalk

/-- The deletion component distinguished by the source's named outer
container root.  Choosing this component, rather than an arbitrary component
of the cut graph, gives the rail boundary a stable annular orientation. -/
noncomputable def alignedBoundaryOuterComponent
    {source : SourceTrail G}
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
    (chain : SourceCornerAlignedRailChain first last) :
    (G.deleteEdges
      (edgeFinsetValueSet (alignedBoundaryCutEdges chain))).ConnectedComponent :=
  (G.deleteEdges
    (edgeFinsetValueSet (alignedBoundaryCutEdges chain))).connectedComponentMk
      source.outerRoot

/-- Because every face of the completed rail boundary is internal, none of
its crossed primal edges belongs to the named outer-hole boundary. -/
theorem alignedBoundaryCutEdges_disjoint_outerHoleBoundary
    {source : SourceTrail G}
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
    (hseparation : chain.BoundarySeparation) :
    Disjoint (alignedBoundaryCutEdges chain)
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
        embedded.cellulation.outerHole) := by
  apply dualWalkCrossingEdges_disjoint_holeBoundary_of_support_internal
    (hunique := hunique) embedded chain.alignedBoundaryWalk
      (chain.alignedBoundaryWalk_support_internal hseparation)
      embedded.cellulation.outerHole
  simp [GoertzelV24FramedAnnularExcess.FramedAnnularCellulation.interiorFaces,
    GoertzelV24FramedAnnularExcess.FramedAnnularCellulation.holeFaces]

/-- The source rail-chain cycle theorem, re-exported from the module which
packages its graph-facing component. -/
theorem alignedBoundaryWalk_isCycle
    {source : SourceTrail G}
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
    (hseparation : chain.BoundarySeparation) :
    chain.alignedBoundaryWalk.IsCycle :=
  chain.alignedBoundaryWalk_isCycle hseparation

/-- Every edge of the named outer container avoids the primal deletion set
crossed by an internal rail boundary. -/
theorem outerContainer_avoids_alignedBoundaryValueSet
    {source : SourceTrail G}
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
    (edge : G.edgeSet) (hedge : edge.1 ∈ source.outerContainer.edges) :
    edge.1 ∉ edgeFinsetValueSet (alignedBoundaryCutEdges chain) := by
  have hcontainer : edge ∈ source.outerContainerEdges := by
    simp [SourceTrail.outerContainerEdges, walkEdgeFinset, hedge]
  have hhole : edge ∈
      orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
        embedded.cellulation.outerHole := by
    rw [embedded.outerHole_boundary]
    exact Finset.mem_union_left _ hcontainer
  have hdisjoint := Finset.disjoint_left.mp
    (alignedBoundaryCutEdges_disjoint_outerHoleBoundary chain hseparation)
  intro hremoved
  rcases (mem_edgeFinsetValueSet_iff
      (alignedBoundaryCutEdges chain) edge.1).1 hremoved with
    ⟨crossed, hcrossed, hvalue⟩
  have hcrossedEq : crossed = edge := Subtype.ext hvalue
  subst crossed
  exact hdisjoint hcrossed hhole

/-- The source outer-container cycle lies wholly in the distinguished outer
deletion component.  This supplies the annular orientation without choosing
a side nonconstructively. -/
theorem outerContainer_hasCycleOn_alignedBoundaryOuterComponent
    {source : SourceTrail G}
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
    (hseparation : chain.BoundarySeparation) :
    HasCycleOnSide G (fun vertex => vertex ∈
      (alignedBoundaryOuterComponent chain).supp) := by
  apply hasCycleOnSide_of_walk_avoiding_removed
    (alignedBoundaryCutEdges chain) (alignedBoundaryOuterComponent chain)
    source.outerContainer source.outerContainer_isCycle
  · exact fun edge hedge =>
      outerContainer_avoids_alignedBoundaryValueSet
        chain hseparation edge hedge
  · exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem

/-- The generic cycle separator saturates the boundary of the prescribed
outer-root component, and both oriented vertex sides are connected. -/
theorem alignedBoundaryOuterComponent_exactBoundary_connectedSides
    {source : SourceTrail G}
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
    (hseparation : chain.BoundarySeparation) :
    componentCrossingEdges (alignedBoundaryCutEdges chain)
        (alignedBoundaryOuterComponent chain) = alignedBoundaryCutEdges chain ∧
      (G.induce (fun vertex => vertex ∈
        (alignedBoundaryOuterComponent chain).supp)).Connected ∧
      (G.induce (fun vertex => vertex ∉
        (alignedBoundaryOuterComponent chain).supp)).Connected := by
  simpa only [alignedBoundaryCutEdges] using
    (component_exactBoundary_connectedSides_of_dualCycle
      embedded.cellulation.rotation htwoSided
      embedded.cellulation.fullOrbitFaceInteriorDual_connected
      embedded.cellulation.connected embedded.cellulation.euler hunique
      chain.alignedBoundaryWalk
      (alignedBoundaryWalk_isCycle chain hseparation)
      (alignedBoundaryOuterComponent chain))

/-- A simple dual rail boundary crosses at least three distinct primal
edges, hence in particular its deletion support contains two distinct edges. -/
theorem one_lt_card_alignedBoundaryCutEdges
    {source : SourceTrail G}
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
    (hseparation : chain.BoundarySeparation) :
    1 < (alignedBoundaryCutEdges chain).card := by
  have hcycle := alignedBoundaryWalk_isCycle chain hseparation
  rw [alignedBoundaryCutEdges,
    card_dualWalkCrossingEdges_eq_length_of_isCycle
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))
      (orbitFace_incidence_le_two
        embedded.cellulation.rotation.toRotationSystem)
      hunique chain.alignedBoundaryWalk hcycle]
  exact lt_of_lt_of_le (by omega) hcycle.three_le_length

/-- The bounded side of the oriented rail boundary contains a vertex of
degree at least two.  This is derived from two distinct crossing edges and
connectedness, not from a false global-cubic assumption on the open source
trail. -/
theorem exists_inner_vertex_two_le_degree
    {source : SourceTrail G}
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
    (hseparation : chain.BoundarySeparation) :
    ∃ vertex, vertex ∉ (alignedBoundaryOuterComponent chain).supp ∧
      2 ≤ (incidentEdgeFinset G vertex).card := by
  let component := alignedBoundaryOuterComponent chain
  rcases alignedBoundaryOuterComponent_exactBoundary_connectedSides
      chain hseparation with ⟨hboundary, _houterConnected, hinnerConnected⟩
  rcases Finset.one_lt_card.mp
      (one_lt_card_alignedBoundaryCutEdges chain hseparation) with
    ⟨firstEdge, hfirstMem, secondEdge, hsecondMem, hne⟩
  have hfirstOuter : EdgeCrossesVertexSide G
      (fun vertex => vertex ∈ component.supp) firstEdge :=
    (mem_componentCrossingEdges_iff
      (alignedBoundaryCutEdges chain) component firstEdge).1
        (hboundary.symm ▸ hfirstMem)
  have hsecondOuter : EdgeCrossesVertexSide G
      (fun vertex => vertex ∈ component.supp) secondEdge :=
    (mem_componentCrossingEdges_iff
      (alignedBoundaryCutEdges chain) component secondEdge).1
        (hboundary.symm ▸ hsecondMem)
  have hfirstInner : EdgeCrossesVertexSide G
      (fun vertex => vertex ∉ component.supp) firstEdge :=
    (edgeCrossesVertexSide_compl G
      (fun vertex => vertex ∈ component.supp) firstEdge).2 hfirstOuter
  have hsecondInner : EdgeCrossesVertexSide G
      (fun vertex => vertex ∉ component.supp) secondEdge :=
    (edgeCrossesVertexSide_compl G
      (fun vertex => vertex ∈ component.supp) secondEdge).2 hsecondOuter
  simpa only [component] using
    (exists_two_le_degree_of_connected_side_of_two_crossing_edges
      (G := G) (fun vertex => vertex ∉ component.supp)
      hinnerConnected hne hfirstInner hsecondInner)

/-- Consumer-facing source-cut certificate.  The oriented bounded side gives
the incident-edge shore; the source outer-container cycle lies on the other
side.  Both edge shores are connected, and both the majority and
non-majority vertex classes are nonempty.  Only subcubic source
well-formedness is used. -/
theorem alignedBoundary_innerIncidentShore_certificate
    {source : SourceTrail G}
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
    (hsource : source.WellFormed) :
    let component := alignedBoundaryOuterComponent chain
    let innerSide : V → Prop := fun vertex => vertex ∉ component.supp
    componentCrossingEdges (alignedBoundaryCutEdges chain) component =
        alignedBoundaryCutEdges chain ∧
      EdgeShoreConnected G (incidentEdgeShore G innerSide) ∧
      EdgeShoreConnected G
        (Finset.univ \ incidentEdgeShore G innerSide) ∧
      (∃ vertex, majorityVertexSide G
        (incidentEdgeShore G innerSide) vertex) ∧
      (∃ vertex, ¬ majorityVertexSide G
        (incidentEdgeShore G innerSide) vertex) := by
  dsimp only
  classical
  let component := alignedBoundaryOuterComponent chain
  let innerSide : V → Prop := fun vertex => vertex ∉ component.supp
  rcases alignedBoundaryOuterComponent_exactBoundary_connectedSides
      chain hseparation with ⟨hboundary, houterConnected, hinnerConnected⟩
  have hpredicate : (fun vertex => ¬ innerSide vertex) =
      (fun vertex => vertex ∈ component.supp) := by
    funext vertex
    apply propext
    change (¬ ¬ vertex ∈ component.supp) ↔ vertex ∈ component.supp
    exact Classical.not_not
  have houterConnected' :
      (G.induce (fun vertex => ¬ innerSide vertex)).Connected := by
    rw [hpredicate]
    exact houterConnected
  have hconnectedShores := connected_edgeShores_of_connected_vertexSides
    (G := G) innerSide hinnerConnected houterConnected'
  rcases exists_inner_vertex_two_le_degree chain hseparation with
    ⟨innerVertex, hinnerVertex, hinnerDegree⟩
  have hmajority : ∃ vertex, majorityVertexSide G
      (incidentEdgeShore G innerSide) vertex :=
    ⟨innerVertex,
      majorityVertexSide_incidentEdgeShore_of_side_of_two_le_degree
        innerSide hinnerVertex hinnerDegree⟩
  have houterCycle :=
    outerContainer_hasCycleOn_alignedBoundaryOuterComponent
      chain hseparation
  have hcomplementCycle :
      HasCycleOnSide G (fun vertex => ¬ innerSide vertex) := by
    rw [hpredicate]
    exact houterCycle
  have hnotMajority : ∃ vertex, ¬ majorityVertexSide G
      (incidentEdgeShore G innerSide) vertex :=
    exists_not_majorityVertexSide_incidentEdgeShore_of_complement_cycle_of_subcubic
      (G := G) (fun vertex => source.incidentEdgeFinset_card_le_three
        hsource vertex) innerSide hcomplementCycle
  exact ⟨hboundary, hconnectedShores.1, hconnectedShores.2,
    hmajority, hnotMajority⟩

/-- A boundary-separated source rail chain constructs a literal deletion
shore whose graph-computed boundary is exactly the chain's crossed edges. -/
theorem exists_alignedBoundary_component_exactBoundary
    {source : SourceTrail G}
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
    (hseparation : chain.BoundarySeparation) :
    ∃ component :
        (G.deleteEdges
          (edgeFinsetValueSet (alignedBoundaryCutEdges chain))).ConnectedComponent,
      componentCrossingEdges (alignedBoundaryCutEdges chain) component =
        alignedBoundaryCutEdges chain := by
  simpa only [alignedBoundaryCutEdges] using
    (exists_component_exactBoundary_of_dualCycle
      embedded.cellulation.rotation htwoSided
      embedded.cellulation.fullOrbitFaceInteriorDual_connected
      embedded.cellulation.connected embedded.cellulation.euler hunique
      chain.alignedBoundaryWalk
      (alignedBoundaryWalk_isCycle chain hseparation))

/-- The same literal source boundary supplies both connected vertex sides.
Thus connected complementary shores are consequences of the constructed
dual cycle, not extra corridor certificates. -/
theorem exists_alignedBoundary_component_exactBoundary_connectedSides
    {source : SourceTrail G}
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
    (hseparation : chain.BoundarySeparation) :
    ∃ component :
        (G.deleteEdges
          (edgeFinsetValueSet (alignedBoundaryCutEdges chain))).ConnectedComponent,
      componentCrossingEdges (alignedBoundaryCutEdges chain) component =
          alignedBoundaryCutEdges chain ∧
        (G.induce (fun vertex => vertex ∈ component.supp)).Connected ∧
        (G.induce (fun vertex => vertex ∉ component.supp)).Connected := by
  simpa only [alignedBoundaryCutEdges] using
    (exists_component_exactBoundary_connectedSides_of_dualCycle
      embedded.cellulation.rotation htwoSided
      embedded.cellulation.fullOrbitFaceInteriorDual_connected
      embedded.cellulation.connected embedded.cellulation.euler hunique
      chain.alignedBoundaryWalk
      (alignedBoundaryWalk_isCycle chain hseparation))

/-- The connected vertex sides of the literal source boundary canonically
induce complementary connected edge shores.  Boundary edges are assigned to
the component side, so this edge-shore assignment is monotone when the chosen
component sides are nested. -/
theorem exists_alignedBoundary_component_exactBoundary_connectedEdgeShores
    {source : SourceTrail G}
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
    (hseparation : chain.BoundarySeparation) :
    ∃ component :
        (G.deleteEdges
          (edgeFinsetValueSet (alignedBoundaryCutEdges chain))).ConnectedComponent,
      componentCrossingEdges (alignedBoundaryCutEdges chain) component =
          alignedBoundaryCutEdges chain ∧
        (G.induce (fun vertex => vertex ∈ component.supp)).Connected ∧
        (G.induce (fun vertex => vertex ∉ component.supp)).Connected ∧
        EdgeShoreConnected G
          (incidentEdgeShore G (fun vertex => vertex ∈ component.supp)) ∧
        EdgeShoreConnected G
          (Finset.univ \
            incidentEdgeShore G (fun vertex => vertex ∈ component.supp)) := by
  rcases exists_alignedBoundary_component_exactBoundary_connectedSides
      chain hseparation with
    ⟨component, hboundary, hside, hcomplement⟩
  have hconnectedEdgeShores :=
    connected_edgeShores_of_connected_vertexSides
      (G := G) (fun vertex => vertex ∈ component.supp)
      hside hcomplement
  exact ⟨component, hboundary, hside, hcomplement,
    hconnectedEdgeShores.1, hconnectedEdgeShores.2⟩

end

end GoertzelV24FramedCorridorRailChainComponent

end Mettapedia.GraphTheory.FourColor
