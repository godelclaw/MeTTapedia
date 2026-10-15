import Mettapedia.OSLF.MeTTaIL.GeneralPremiseExecutionFrames

/-!
# Declaration order of complete premise histories

The child search uses declaration positions derived from the language. This
readout states that each retained directed child event visits an earlier
declaration, including its own premise history. Equation origins remain
separate from the primitive declaration positions used for child execution.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

mutual
def eventOrdered (limit : Nat) : Event → Bool
  | .query _ _ _ _ | .freshness _ _ _ _ => true
  | .child _ _ index _ _ _ _ _ _ _ history =>
      decide (index < limit) && eventsOrdered index history
  | .quantified _ _ _ elements => quantifiedOrdered limit elements
termination_by event => sizeOf event

def eventsOrdered (limit : Nat) : List Event → Bool
  | [] => true
  | event :: events => eventOrdered limit event && eventsOrdered limit events
termination_by events => sizeOf events

def quantifiedOrdered (limit : Nat) : List (Nat × Syntax.Pattern × List Event) → Bool
  | [] => true
  | (_, _, history) :: elements => eventsOrdered limit history && quantifiedOrdered limit elements
termination_by elements => sizeOf elements
end

namespace Execution

def Result.ordered {environment : Environment} {goal : Goal} : Result environment goal → Bool :=
  fun result => match goal, result with
  | .premise context _ _, .premise _ event _ => eventOrdered context.ruleIndex event
  | .premises context _ _, .premises _ history _ => eventsOrdered context.ruleIndex history
  | .quantified context _ _ _ _ _, .quantified _ elements _ =>
      quantifiedOrdered context.ruleIndex elements
  | .root _ _ _ index, .root _ _ _ history _ _ => eventsOrdered index history
  | .steps _ _ _ _, .steps index _ _ _ history _ _ _ => eventsOrdered index history

end Execution

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
