import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Card

namespace Mettapedia.GraphTheory.FourColor.Curriculum.Actual

variable {α : Type*} [Fintype α]
variable (G : SimpleGraph α) [DecidableRel G.Adj]

/-- The neighbor set cardinality is bounded by the ambient vertex cardinality. -/
theorem card_neighborSet_le_card (v : α) :
    Fintype.card (G.neighborSet v) ≤ Fintype.card α := by
  exact Fintype.card_subtype_le (fun w => w ∈ G.neighborSet v)

end Mettapedia.GraphTheory.FourColor.Curriculum.Actual
