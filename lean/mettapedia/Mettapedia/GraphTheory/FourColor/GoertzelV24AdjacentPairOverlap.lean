import Mettapedia.GraphTheory.EdgeColoringEmbedding
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairInsertion

/-!
# The common carrier of two adjacent-pair deletions

Two adjacent-pair colourings live on different induced graphs.  Their exact
common comparison carrier is the graph obtained by deleting the union of the
two endpoint pairs.  This file constructs that carrier and its two canonical
embeddings without imposing any relation between the pairs or their
colourings.

The declarations were factored out of the all-face reentry development so
that wall- and mesh-level consumers can use the common carrier without
importing that specialized route.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

/-- The common induced graph left after deleting two ordered vertex pairs. -/
abbrev DeletedTwoPairsGraph
    (G : SimpleGraph V) (first second third fourth : V) :
    SimpleGraph {vertex : V |
      vertex ≠ first ∧ vertex ≠ second ∧
        vertex ≠ third ∧ vertex ≠ fourth} :=
  G.induce {vertex |
    vertex ≠ first ∧ vertex ≠ second ∧
      vertex ≠ third ∧ vertex ≠ fourth}

/-- The common four-vertex deletion embeds into the deletion of its first
ordered pair. -/
def deletedTwoPairsToFirstDeletionEmbedding
    (G : SimpleGraph V) (first second third fourth : V) :
    DeletedTwoPairsGraph G first second third fourth ↪g
      DeletedAdjacentPairGraph G first second where
  toFun vertex := ⟨vertex.1, vertex.2.1, vertex.2.2.1⟩
  inj' left right heq := by
    apply Subtype.ext
    exact congrArg
      (fun vertex : retainedVertexSet first second => vertex.1) heq
  map_rel_iff' := Iff.rfl

/-- The same common deletion embeds into the deletion of its second ordered
pair. -/
def deletedTwoPairsToSecondDeletionEmbedding
    (G : SimpleGraph V) (first second third fourth : V) :
    DeletedTwoPairsGraph G first second third fourth ↪g
      DeletedAdjacentPairGraph G third fourth where
  toFun vertex := ⟨vertex.1, vertex.2.2.2.1, vertex.2.2.2.2⟩
  inj' left right heq := by
    apply Subtype.ext
    exact congrArg
      (fun vertex : retainedVertexSet third fourth => vertex.1) heq
  map_rel_iff' := Iff.rfl

/-- Restrict a colouring of the first adjacent-pair deletion to the common
four-vertex deleted graph. -/
def firstDeletionCommonCoreColoring
    {first second third fourth : V}
    (coloring :
      (DeletedAdjacentPairGraph G first second).EdgeColoring Color) :
    (DeletedTwoPairsGraph G first second third fourth).EdgeColoring Color :=
  coloring.pullbackEmbedding
    (deletedTwoPairsToFirstDeletionEmbedding G first second third fourth)

/-- Restrict a colouring of the second adjacent-pair deletion to the same
common four-vertex deleted graph. -/
def secondDeletionCommonCoreColoring
    {first second third fourth : V}
    (coloring :
      (DeletedAdjacentPairGraph G third fourth).EdgeColoring Color) :
    (DeletedTwoPairsGraph G first second third fourth).EdgeColoring Color :=
  coloring.pullbackEmbedding
    (deletedTwoPairsToSecondDeletionEmbedding G first second third fourth)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Restriction to the common carrier preserves the nonzero Tait condition
from the first deletion. -/
theorem isTaitEdgeColoring_firstDeletionCommonCoreColoring
    {first second third fourth : V}
    (coloring :
      (DeletedAdjacentPairGraph G first second).EdgeColoring Color)
    (hcoloring : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G first second) coloring) :
    IsTaitEdgeColoring
      (DeletedTwoPairsGraph G first second third fourth)
      (firstDeletionCommonCoreColoring coloring) := by
  intro edge
  exact hcoloring
    ((deletedTwoPairsToFirstDeletionEmbedding G first second third fourth).mapEdgeSet
      edge)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Restriction to the common carrier preserves the nonzero Tait condition
from the second deletion. -/
theorem isTaitEdgeColoring_secondDeletionCommonCoreColoring
    {first second third fourth : V}
    (coloring :
      (DeletedAdjacentPairGraph G third fourth).EdgeColoring Color)
    (hcoloring : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G third fourth) coloring) :
    IsTaitEdgeColoring
      (DeletedTwoPairsGraph G first second third fourth)
      (secondDeletionCommonCoreColoring coloring) := by
  intro edge
  exact hcoloring
    ((deletedTwoPairsToSecondDeletionEmbedding G first second third fourth).mapEdgeSet
      edge)

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

/-! Publication-facing aliases keep manuscript citations recoverable from the
defining module while the implementation remains in the adjacent-pair API. -/

alias GoertzelV24AdjacentPairOverlap.isTaitEdgeColoring_firstDeletionCommonCoreColoring :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.isTaitEdgeColoring_firstDeletionCommonCoreColoring

alias GoertzelV24AdjacentPairOverlap.isTaitEdgeColoring_secondDeletionCommonCoreColoring :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.isTaitEdgeColoring_secondDeletionCommonCoreColoring

end Mettapedia.GraphTheory.FourColor
