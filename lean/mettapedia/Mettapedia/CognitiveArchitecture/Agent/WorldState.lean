import Mettapedia.CognitiveArchitecture.Agent.WorldStateCore
import Mathlib.Data.Fintype.Card

/-!
# Finite limits on universally lossless context compaction

The typed state and query-relative contracts are re-exported from
`WorldStateCore`. Only the finite-cardinality consequence requires Mathlib.
-/

namespace Mettapedia.CognitiveArchitecture.Agent.WorldState

/-- Finite universal-lossless compaction is impossible whenever the view has
strictly fewer states than the concrete state space. -/
theorem no_universal_query_complete_compression
    {State Query Answer View : Type*}
    [Fintype State] [Fintype View]
    {answer : State → Query → Answer} {view : State → View}
    (separating : QuerySeparating answer)
    (smaller : Fintype.card View < Fintype.card State) :
    ¬ QueryComplete answer view := by
  intro complete
  have injective : Function.Injective view :=
    queryComplete_injective separating complete
  have card_le : Fintype.card State ≤ Fintype.card View :=
    Fintype.card_le_of_injective view injective
  exact (Nat.not_le_of_gt smaller) card_le

end Mettapedia.CognitiveArchitecture.Agent.WorldState

#print axioms Mettapedia.CognitiveArchitecture.Agent.WorldState.no_universal_query_complete_compression
