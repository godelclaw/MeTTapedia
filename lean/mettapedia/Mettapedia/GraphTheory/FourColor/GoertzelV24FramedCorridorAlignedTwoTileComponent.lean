import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTileBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedLocalDualCycleBond

/-!
# Exact deletion component of the aligned two-tile boundary

The source-aligned six-step facial-dual boundary already gives a finite
six-edge deletion that disconnects the ambient graph.  This module constructs
one of its deletion components and proves that the component's graph boundary
is exactly those six crossed edges.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FramedLocalDualCycleBond
open GoertzelV24FramedLocalDualCycleSeparator
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorAlignedTwoTileComponentEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

omit [DecidableEq V] in
/-- Distinct components of a finite edge deletion in a connected graph have
a nonempty original-graph boundary. -/
private theorem localComponentCrossingEdges_nonempty_of_distinct
    (hconnected : G.Connected) (removed : Finset G.edgeSet)
    (inside outside :
      (G.deleteEdges (localEdgeFinsetValueSet removed)).ConnectedComponent)
    (hdistinct : inside ≠ outside) :
    (localComponentCrossingEdges removed inside).Nonempty := by
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
    (mem_localComponentCrossingEdges_iff removed inside edge).2 hcross⟩

/-- The aligned two-tile source boundary constructs an actual deletion
component whose original-graph boundary is exactly its six crossed edges. -/
theorem exists_sourceTwoTileAlignedBoundaryComponent_exactBoundary
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4)) :
    ∃ component : (G.deleteEdges (localEdgeFinsetValueSet
        (sourceTwoTileAlignedBoundaryCrossingEdgesAt realization hcubic
          hrotation htwoSided hunique offset))).ConnectedComponent,
      localComponentCrossingEdges
          (sourceTwoTileAlignedBoundaryCrossingEdgesAt realization hcubic
            hrotation htwoSided hunique offset) component =
        sourceTwoTileAlignedBoundaryCrossingEdgesAt realization hcubic
          hrotation htwoSided hunique offset := by
  let removed := sourceTwoTileAlignedBoundaryCrossingEdgesAt realization hcubic
    hrotation htwoSided hunique offset
  let walk := sourceTwoTileAlignedBoundaryWalkAt realization hcubic hrotation
    htwoSided hunique offset
  have hnotConnected :
      ¬ (G.deleteEdges (localEdgeFinsetValueSet removed)).Connected := by
    simpa [removed] using
      sourceTwoTileAlignedBoundaryCut_not_connected realization hcubic hrotation
        htwoSided hunique offset
  rcases exists_distinct_localComponents_of_not_connected
      embedded.cellulation.connected removed hnotConnected with
    ⟨inside, outside, hdistinct⟩
  refine ⟨inside, ?_⟩
  have hcomponentBoundary : localComponentCrossingEdges removed inside =
      localCrossingEdgeFinset G (fun vertex => vertex ∈ inside.supp) := by
    ext edge
    simp [localComponentCrossingEdges, localCrossingEdgeFinset]
  have hsubset :
      localCrossingEdgeFinset G (fun vertex => vertex ∈ inside.supp) ⊆
        removed := by
    rw [← hcomponentBoundary]
    exact localComponentCrossingEdges_subset_removed removed inside
  have hnonempty :
      (localCrossingEdgeFinset G
        (fun vertex => vertex ∈ inside.supp)).Nonempty := by
    rw [← hcomponentBoundary]
    exact localComponentCrossingEdges_nonempty_of_distinct
      embedded.cellulation.connected removed inside outside hdistinct
  have hboundary :
      localCrossingEdgeFinset G (fun vertex => vertex ∈ inside.supp) =
        removed := by
    apply
      crossingEdgeFinset_eq_dualWalkCrossingEdges_of_isCycle_of_subset_of_supportTwoSided
        embedded.cellulation.rotation hunique walk
        (by
          simpa [walk] using
            sourceTwoTileAlignedBoundaryWalkAt_isCycle realization hcubic
              hrotation htwoSided hunique offset)
        (fun vertex => vertex ∈ inside.supp)
    · change localCrossingEdgeFinset G
        (fun vertex => vertex ∈ inside.supp) ⊆ removed
      exact hsubset
    · exact hnonempty
    · intro _face _hface dart _hdart
      exact htwoSided dart
  rw [hcomponentBoundary]
  exact hboundary

/-- The aligned boundary can be oriented by the distinguished outer vertex.
The selected component has the exact six-edge boundary, and a vertex on the
other side witnesses that the retained carrier is strictly smaller. -/
theorem exists_sourceTwoTileAlignedOuterComponent_exactBoundary_and_removed
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4)) :
    ∃ component : (G.deleteEdges (localEdgeFinsetValueSet
        (sourceTwoTileAlignedBoundaryCrossingEdgesAt realization hcubic
          hrotation htwoSided hunique offset))).ConnectedComponent,
      ∃ removedVertex : V,
        embedded.cellulation.rotation.toRotationSystem.vertOf
            embedded.cellulation.rotation.toRotationSystem.outer ∈
          component.supp ∧
        removedVertex ∉ component.supp ∧
        localComponentCrossingEdges
            (sourceTwoTileAlignedBoundaryCrossingEdgesAt realization hcubic
              hrotation htwoSided hunique offset) component =
          sourceTwoTileAlignedBoundaryCrossingEdgesAt realization hcubic
            hrotation htwoSided hunique offset := by
  let removedEdges :=
    sourceTwoTileAlignedBoundaryCrossingEdgesAt realization hcubic hrotation
      htwoSided hunique offset
  let walk := sourceTwoTileAlignedBoundaryWalkAt realization hcubic hrotation
    htwoSided hunique offset
  have hnotConnected :
      ¬ (G.deleteEdges (localEdgeFinsetValueSet removedEdges)).Connected := by
    simpa [removedEdges] using
      sourceTwoTileAlignedBoundaryCut_not_connected realization hcubic hrotation
        htwoSided hunique offset
  let outerVertex := embedded.cellulation.rotation.toRotationSystem.vertOf
    embedded.cellulation.rotation.toRotationSystem.outer
  let outerComponent : (G.deleteEdges
      (localEdgeFinsetValueSet removedEdges)).ConnectedComponent :=
    (G.deleteEdges (localEdgeFinsetValueSet removedEdges)).connectedComponentMk
      outerVertex
  have houterMem : outerVertex ∈ outerComponent.supp := by
    dsimp [outerComponent]
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  rcases exists_distinct_localComponents_of_not_connected
      embedded.cellulation.connected removedEdges hnotConnected with
    ⟨inside, outside, hdistinct⟩
  have outerBoundary_of_distinct
      (other : (G.deleteEdges
        (localEdgeFinsetValueSet removedEdges)).ConnectedComponent)
      (hother : outerComponent ≠ other) :
      localComponentCrossingEdges removedEdges outerComponent =
        removedEdges := by
    have hcomponentBoundary :
        localComponentCrossingEdges removedEdges outerComponent =
          localCrossingEdgeFinset G
            (fun vertex => vertex ∈ outerComponent.supp) := by
      ext edge
      simp [localComponentCrossingEdges, localCrossingEdgeFinset]
    have hsubset : localCrossingEdgeFinset G
        (fun vertex => vertex ∈ outerComponent.supp) ⊆ removedEdges := by
      rw [← hcomponentBoundary]
      exact localComponentCrossingEdges_subset_removed removedEdges
        outerComponent
    have hnonempty : (localCrossingEdgeFinset G
        (fun vertex => vertex ∈ outerComponent.supp)).Nonempty := by
      rw [← hcomponentBoundary]
      exact localComponentCrossingEdges_nonempty_of_distinct
        embedded.cellulation.connected removedEdges outerComponent other hother
    have hboundary : localCrossingEdgeFinset G
        (fun vertex => vertex ∈ outerComponent.supp) = removedEdges := by
      apply
        crossingEdgeFinset_eq_dualWalkCrossingEdges_of_isCycle_of_subset_of_supportTwoSided
          embedded.cellulation.rotation hunique walk
          (by
            simpa [walk] using
              sourceTwoTileAlignedBoundaryWalkAt_isCycle realization hcubic
                hrotation htwoSided hunique offset)
          (fun vertex => vertex ∈ outerComponent.supp)
      · change localCrossingEdgeFinset G
          (fun vertex => vertex ∈ outerComponent.supp) ⊆ removedEdges
        exact hsubset
      · exact hnonempty
      · intro _face _hface dart _hdart
        exact htwoSided dart
    rw [hcomponentBoundary]
    exact hboundary
  by_cases hinside : inside = outerComponent
  · have houterNeOutside : outerComponent ≠ outside := by
      intro heq
      exact hdistinct (hinside.trans heq)
    rcases outside.nonempty_supp with ⟨removedVertex, hremoved⟩
    have hremovedNotOuter : removedVertex ∉ outerComponent.supp := by
      intro houter
      have heq : outside = outerComponent :=
        SimpleGraph.ConnectedComponent.eq_of_common_vertex hremoved houter
      exact hdistinct (hinside.trans heq.symm)
    refine ⟨outerComponent, removedVertex, ?_, hremovedNotOuter, ?_⟩
    · simpa [outerVertex] using houterMem
    · exact outerBoundary_of_distinct outside houterNeOutside
  · have houterNeInside : outerComponent ≠ inside := by
      intro heq
      exact hinside heq.symm
    rcases inside.nonempty_supp with ⟨removedVertex, hremoved⟩
    have hremovedNotOuter : removedVertex ∉ outerComponent.supp := by
      intro houter
      exact hinside (SimpleGraph.ConnectedComponent.eq_of_common_vertex
        hremoved houter)
    refine ⟨outerComponent, removedVertex, ?_, hremovedNotOuter, ?_⟩
    · simpa [outerVertex] using houterMem
    · exact outerBoundary_of_distinct inside houterNeInside

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
