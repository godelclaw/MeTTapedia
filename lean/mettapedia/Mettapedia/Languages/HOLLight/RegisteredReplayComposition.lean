import Mettapedia.Languages.HOLLight.ProofExecution

/-!
# Composition of registered proof and declaration histories

Appending a checked suffix to a checked prefix retains the actual intermediate
declaration context and theorem cache. The law includes constant and type
definitions, whose effects cannot be replaced by proof-graph concatenation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ProofExecution.Registered

open Mettapedia.Languages.OpenTheory

theorem replayFrom_append (policy : AxiomPolicy) [DecidablePred policy]
    (before : State) (earlier later : List Command) :
    replayFrom policy before (earlier ++ later) =
      (replayFrom policy before earlier).bind (fun middle => replayFrom policy middle later) := by
  induction earlier generalizing before with
  | nil => rfl
  | cons command rest hypotheses =>
    cases checked : apply policy before command with
    | none => simp [replayFrom, checked]
    | some middle =>
      simpa [replayFrom, checked] using hypotheses middle

theorem replayFrom_append_accepted (policy : AxiomPolicy) [DecidablePred policy]
    {before middle after : State} {earlier later : List Command}
    (first : replayFrom policy before earlier = some middle)
    (second : replayFrom policy middle later = some after) :
    replayFrom policy before (earlier ++ later) = some after := by
  rw [replayFrom_append, first]
  exact second

#print axioms replayFrom_append_accepted

end Mettapedia.Languages.HOLLight.ProofExecution.Registered
