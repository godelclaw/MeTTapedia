import Mettapedia.GraphTheory.FourColor.RotationSystemEdgeColoring

/-!
# Two-color tracked subgraphs of a rotation system

The selected-color predicate and its induced edge graph are generic
rotation-system notions.  They live here so corridor and boundary arguments
do not need to import the facial-square development that first used them.
-/

namespace Mettapedia.GraphTheory.FourColor

/-- Membership in the pair of colors whose connectivity profile is being
tracked. -/
def IsTrackedColor (first second color : Color) : Prop :=
  color = first ∨ color = second
  deriving Decidable

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E)

/-- The ambient edge-adjacency graph restricted to edges carrying either
tracked color.  Vertices remain on the original edge type. -/
def trackedEdgeGraph (coloring : E → Color) (first second : Color) :
    SimpleGraph E where
  Adj edge other := RS.edgeAdjacencyGraph.Adj edge other ∧
    IsTrackedColor first second (coloring edge) ∧
    IsTrackedColor first second (coloring other)
  symm := ⟨by
    intro edge other h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by
    intro edge h
    exact h.1.1 rfl⟩

end RotationSystem

end Mettapedia.GraphTheory.FourColor
