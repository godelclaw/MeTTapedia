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
