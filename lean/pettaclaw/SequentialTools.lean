/-!
# Sequential tool dispatch

The simplified dispatcher records every proposed position, including errors.
Only an explicit stopped state prevents execution. Failure is ordinary result
data, so it cannot discard the remaining commands. There is no numeric batch
bound, dependency classifier, or pending-resolution obligation in this model.

This models the dispatch contract, not the correctness of arbitrary tools, the
truth of their output, or a proof that the Python/Prolog implementation refines
Lean. Runtime conformance is checked separately with real evaluator fixtures.
`CommandHolds` compares this all-call rule with the historical hold policy.
-/

namespace PettaClaw.SequentialTools

inductive Outcome (Value : Type) where
  | returned (value : Value)
  | failed (reason : String)
  | unknown
  | stopped
  deriving Repr, DecidableEq

structure Receipt (Command Value : Type) where
  command : Command
  outcome : Outcome Value
  deriving Repr, DecidableEq

/-- The state includes the operator's stop latch. A tool may update state and
return any outcome. Neither the outcome nor the command kind is a stop rule. -/
def dispatch {State Command Value : Type}
    (isStopped : State → Bool)
    (execute : State → Command → State × Outcome Value) :
    State → List Command → State × List (Receipt Command Value)
  | state, [] => (state, [])
  | state, command :: rest =>
    let step := if isStopped state then (state, Outcome.stopped)
                else execute state command
    let tail := dispatch isStopped execute step.1 rest
    (tail.1, ⟨command, step.2⟩ :: tail.2)

/-- Every emitted position has a receipt, in the original order. This also
covers a stopped suffix; an unexecuted command is never reported as run. -/
theorem command_order {State Command Value : Type}
    (stop : State → Bool) (execute : State → Command → State × Outcome Value)
    (state : State) (commands : List Command) :
    ((dispatch stop execute state commands).2.map Receipt.command) = commands := by
  induction commands generalizing state with
  | nil => rfl
  | cons command rest ih =>
    simp only [dispatch, List.map_cons]
    rw [ih]

theorem receipt_count {State Command Value : Type}
    (stop : State → Bool) (execute : State → Command → State × Outcome Value)
    (state : State) (commands : List Command) :
    (dispatch stop execute state commands).2.length = commands.length := by
  have h := congrArg List.length (command_order stop execute state commands)
  simpa using h

/-- A failed tool still leaves exactly the same dispatch of the suffix from
the state it returned. No inferred dependency or failure hold is inserted. -/
theorem failure_continues {State Command Value : Type}
    (stop : State → Bool) (execute : State → Command → State × Outcome Value)
    (state next : State) (command : Command) (rest : List Command) (reason : String)
    (running : stop state = false)
    (result : execute state command = (next, .failed reason)) :
    dispatch stop execute state (command :: rest) =
      ((dispatch stop execute next rest).1,
       ⟨command, .failed reason⟩ :: (dispatch stop execute next rest).2) := by
  simp [dispatch, running, result]

theorem stopped_suffix {State Command Value : Type}
    (stop : State → Bool) (execute : State → Command → State × Outcome Value)
    (state : State) (commands : List Command) (paused : stop state = true) :
    dispatch stop execute state commands =
      (state, commands.map (fun command => ⟨command, Outcome.stopped⟩)) := by
  induction commands with
  | nil => rfl
  | cons command rest ih => simp [dispatch, paused, ih]

#print axioms command_order
#print axioms receipt_count
#print axioms failure_continues
#print axioms stopped_suffix

end PettaClaw.SequentialTools
