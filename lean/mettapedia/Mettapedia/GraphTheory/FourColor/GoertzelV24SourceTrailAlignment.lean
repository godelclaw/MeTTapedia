import Mettapedia.GraphTheory.FourColor.GoertzelV24BetweenRegionDefectPaths

/-!
# Source trail data and the definitional L10 alignment

The source manuscript permits a trail to be represented on the graph side by
its subcubic framed graph.  This module records the part of that representation
needed for L10: two disjoint container cycles, the marked defect endpoint on
each container, and the frozen outward interface.  The between-region core is
then defined to be every remaining edge of the framed graph.

Consequently, the source annulus covers exactly the movable framed edges by
construction.  `BetweenRegionEdgeAligned` is proved for this source object; it
is not stored as a hypothesis.  This is only the graph-side trail object.  A
future formation-to-graph theorem must construct it from the manuscript's
Jordan-curve formation semantics rather than treating this file as that
topological theorem.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  [Fintype G.edgeSet] [DecidableEq G.edgeSet]

/-- The graph edges traversed by a concrete walk, retained as edges of `G`. -/
def walkEdgeFinset {start finish : V} (walk : G.Walk start finish) :
    Finset G.edgeSet :=
  Finset.univ.filter fun edge => edge.1 ∈ walk.edges

/-- Graph-side data of a source trail.  The ambient graph here is already the
framed between-region graph, not the original closed cubic graph.  The two
container curves are represented by disjoint cycles, the missing-edge defects
lie on the prescribed outer and inner containers, and the outward interface is
identified independently of the containers. -/
structure SourceTrail (G : SimpleGraph V) where
  innerRoot : V
  outerRoot : V
  innerContainer : G.Walk innerRoot innerRoot
  outerContainer : G.Walk outerRoot outerRoot
  innerContainer_isCycle : innerContainer.IsCycle
  outerContainer_isCycle : outerContainer.IsCycle
  containers_vertex_disjoint :
    Disjoint innerContainer.support.toFinset outerContainer.support.toFinset
  frozenInterfaceStubVertices : Finset V
  frozenInterfaceEdges : Finset G.edgeSet
  defectVertex : Fin 2 -> V
  defect_zero_on_outer : defectVertex 0 ∈ outerContainer.support
  defect_one_on_inner : defectVertex 1 ∈ innerContainer.support
  innerContainer_avoids_frozenInterface :
    ∀ edge : G.edgeSet, edge.1 ∈ innerContainer.edges →
      edge ∉ frozenInterfaceEdges
  outerContainer_avoids_frozenInterface :
    ∀ edge : G.edgeSet, edge.1 ∈ outerContainer.edges →
      edge ∉ frozenInterfaceEdges

namespace SourceTrail

/-- Edge support of the inner source container. -/
def innerContainerEdges (source : SourceTrail G) : Finset G.edgeSet :=
  walkEdgeFinset source.innerContainer

/-- Edge support of the outer source container. -/
def outerContainerEdges (source : SourceTrail G) : Finset G.edgeSet :=
  walkEdgeFinset source.outerContainer

/-- The non-container, non-frozen part of the framed graph.  Since the graph
of a `SourceTrail` is already the source's framed between-region, this
complement is the graph-side meaning of "all other curves/segments lie in the
annulus between the two containers." -/
def betweenRegionCoreEdges (source : SourceTrail G) : Finset G.edgeSet :=
  Finset.univ \ (source.frozenInterfaceEdges ∪
    source.innerContainerEdges ∪ source.outerContainerEdges)

/-- Forget the explicit container walks while retaining exactly the framed
edge partition consumed by the Kempe dynamics. -/
def toFramedTrailData (source : SourceTrail G) : FramedTrailData G where
  innerContainerEdges := source.innerContainerEdges
  outerContainerEdges := source.outerContainerEdges
  betweenRegionCoreEdges := source.betweenRegionCoreEdges
  frozenInterfaceStubVertices := source.frozenInterfaceStubVertices
  frozenInterfaceEdges := source.frozenInterfaceEdges
  defectVertex := source.defectVertex

/-- Structural well-formedness of a source trail is exactly the already
audited framed degree/stub condition on its graph-side realization. -/
def WellFormed (source : SourceTrail G) : Prop :=
  source.toFramedTrailData.WellFormed

/-- The source constructor proves, rather than assumes, that its two container
supports and remaining between-region core exhaust precisely the non-frozen
edges of the framed graph. -/
theorem toFramedTrailData_betweenRegionEdgeAligned
    (source : SourceTrail G) :
    source.toFramedTrailData.BetweenRegionEdgeAligned := by
  rw [FramedTrailData.BetweenRegionEdgeAligned]
  apply Finset.Subset.antisymm
  · intro edge hedge
    simp only [FramedTrailData.sourceBetweenRegionEdges, toFramedTrailData,
      FramedTrailData.movableEdges] at hedge ⊢
    rcases Finset.mem_union.mp hedge with hcontainers | hcore
    · rcases Finset.mem_union.mp hcontainers with hinner | houter
      · have hnotFrozen : edge ∉ source.frozenInterfaceEdges := by
          apply source.innerContainer_avoids_frozenInterface edge
          exact (Finset.mem_filter.mp hinner).2
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ edge, hnotFrozen⟩
      · have hnotFrozen : edge ∉ source.frozenInterfaceEdges := by
          apply source.outerContainer_avoids_frozenInterface edge
          exact (Finset.mem_filter.mp houter).2
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ edge, hnotFrozen⟩
    · have hnotUnion :=
        (Finset.mem_sdiff.mp hcore).2
      have hnotFrozen : edge ∉ source.frozenInterfaceEdges := by
        intro hfrozen
        apply hnotUnion
        exact Finset.mem_union_left _ (Finset.mem_union_left _ hfrozen)
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ edge, hnotFrozen⟩
  · intro edge hmovable
    simp only [FramedTrailData.sourceBetweenRegionEdges, toFramedTrailData,
      FramedTrailData.movableEdges] at hmovable ⊢
    by_cases hinner : edge ∈ source.innerContainerEdges
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hinner)
    by_cases houter : edge ∈ source.outerContainerEdges
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ houter)
    apply Finset.mem_union_right
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ edge, ?_⟩
    intro hunion
    rcases Finset.mem_union.mp hunion with hfrozenOrInner | houter'
    · rcases Finset.mem_union.mp hfrozenOrInner with hfrozen | hinner'
      · exact (Finset.mem_sdiff.mp hmovable).2 hfrozen
      · exact hinner hinner'
    · exact houter houter'

/-- L10 at one step for an actual graph-side source trail: the legal framed
moves are exactly the corrected source circuit-or-defect-path moves, with no
free alignment premise. -/
theorem legalKempeStep_iff_sourceBetweenRegionKempeStep
    (source : SourceTrail G) (hsource : source.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (C' : G.EdgeColoring Color) :
    FramedTangleLegalKempeStep source.toFramedTrailData C C' ↔
      SourceBetweenRegionKempeStep source.toFramedTrailData C C' := by
  exact framedTangleLegalKempeStep_iff_kauffman_or_defectPath
    source.toFramedTrailData hsource
    source.toFramedTrailData_betweenRegionEdgeAligned C hC C'

/-- L10 at finite reachability for an actual graph-side source trail. -/
theorem kempeReachable_iff_sourceBetweenRegionKempeReachable
    (source : SourceTrail G) (hsource : source.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (C' : G.EdgeColoring Color) :
    FramedTangleKempeReachable source.toFramedTrailData C C' ↔
      SourceBetweenRegionKempeReachable source.toFramedTrailData C C' := by
  exact (sourceBetweenRegionKempeReachable_iff_framedTangleKempeReachable
    source.toFramedTrailData hsource
    source.toFramedTrailData_betweenRegionEdgeAligned C hC C').symm

/-- L10 at the completion predicate for an actual graph-side source trail. -/
theorem completable_iff_sourceBetweenRegionCompletable
    (source : SourceTrail G) (hsource : source.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    FramedTangleCompletable source.toFramedTrailData C ↔
      SourceBetweenRegionCompletable source.toFramedTrailData C := by
  exact (sourceBetweenRegionCompletable_iff_framedTangleCompletable
    source.toFramedTrailData hsource
    source.toFramedTrailData_betweenRegionEdgeAligned C hC).symm

end SourceTrail

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
