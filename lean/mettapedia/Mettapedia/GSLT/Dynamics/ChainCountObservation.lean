import Mettapedia.GSLT.Dynamics.ChainMoments

/-!
# Complete path counts through continuations

The grouped path algorithm can feed a constant fold or publish one terminal
answer annotated with its occurrence multiplicity. The reference still folds
each enumerated occurrence independently. These laws connect the two executions
through an arbitrary pure continuation, and separate complete count observation
from a finite event purse. Machine range checks remain implementation controls.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ChainCountObservation

open ChainAggregation ChainMoments

variable {Item Key Answer : Type*}

def constantFold (items : List Item) (value initial : Int) : Int :=
  items.foldl (fun total _ => total + value) initial

theorem constantFold_length (items : List Item) (value initial : Int) :
    constantFold items value initial = initial + (items.length : Int) * value := by
  induction items generalizing initial with
  | nil => simp [constantFold]
  | cons item rest ih =>
      change constantFold rest value (initial + value) = _
      rw [ih, List.length_cons, Nat.cast_add, Nat.cast_one]
      ring

theorem complete_path_fold [DecidableEq Key]
    (relations : List (List (Edge Key Moment)))
    (unit : ∀ relation ∈ relations, ∀ row ∈ relation, row.weight.fst = 1)
    (value initial : Int) :
    constantFold (enumerate relations) value initial =
      initial + (aggregate relations).fst * value := by
  rw [(aggregate_accounts relations unit).1]
  exact constantFold_length _ _ _

/-- Nesting the complete fold in a constructor or another pure consumer
does not change its answer. It does not turn an effectful consumer into a
pure one, nor weaken the path and unit-weight obligations. -/
theorem continuation_of_complete_path_fold [DecidableEq Key]
    (relations : List (List (Edge Key Moment)))
    (unit : ∀ relation ∈ relations, ∀ row ∈ relation, row.weight.fst = 1)
    (value initial : Int) (continuation : Int → Answer) :
    continuation (constantFold (enumerate relations) value initial) =
      continuation (initial + (aggregate relations).fst * value) := by
  rw [complete_path_fold relations unit value initial]

theorem sum_constant_annotations (items : List Item) (weight : Int) :
    (items.map fun _ => weight).sum = (items.length : Int) * weight := by
  induction items with
  | nil => simp
  | cons item rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.cast_add, Nat.cast_one]
      rw [ih]
      ring

/-- Publishing one weighted continuation preserves the complete count of
all occurrence continuations, including multiplicity accumulated earlier. -/
theorem weighted_terminal_count [DecidableEq Key]
    (relations : List (List (Edge Key Moment)))
    (unit : ∀ relation ∈ relations, ∀ row ∈ relation, row.weight.fst = 1)
    (observerWeight : Int) :
    (aggregate relations).fst * observerWeight =
      ((enumerate relations).map fun _ => observerWeight).sum := by
  rw [(aggregate_accounts relations unit).1, sum_constant_annotations]

def eventPrefixCount (limit : Nat) (annotations : List Nat) : Nat :=
  (annotations.take limit).sum

theorem complete_event_purse (annotations : List Nat) (limit : Nat)
    (complete : annotations.length ≤ limit) :
    eventPrefixCount limit annotations = annotations.sum := by
  simp [eventPrefixCount, List.take_of_length_le complete]

namespace Controls

theorem contraction_preserves_complete_count :
    ([1, 1, 1, 1] : List Nat).sum = [4].sum := by decide

theorem finite_event_purse_distinguishes_contraction :
    eventPrefixCount 1 [1, 1, 1, 1] ≠ eventPrefixCount 1 [4] := by decide

theorem equal_counts_do_not_preserve_ordered_answers :
    ([0, 1] : List Nat).length = [1, 0].length ∧
      ([0, 1] : List Nat).take 1 ≠ [1, 0].take 1 := by decide

end Controls

end Mettapedia.GSLT.Dynamics.ChainCountObservation
