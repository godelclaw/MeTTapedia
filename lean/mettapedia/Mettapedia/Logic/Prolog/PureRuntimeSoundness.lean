import Mettapedia.Logic.Prolog.PureRuntime
import Mettapedia.Logic.LP.RuntimeUnificationSoundness

/-!
# Soundness of the canonical pure Prolog entrypoint

The theorem in this module does not restate resolution.  It transports the
already-proved `Logic.LP.runtimeAnswer_leastModel` theorem through the exact
pure projection of `Logic.Prolog.Goal` and `Logic.Prolog.Program`.
-/

namespace Mettapedia.Logic.Prolog.PureRuntime

open Mettapedia.Logic
open LP
open LP.RuntimeQuery

/-- Every answer returned through the canonical pure Prolog entrypoint carries
a standardized-apart SLD derivation and is true in the same least Herbrand
model as the `Logic.LP` kernel. -/
theorem answer_leastModel {sigma : LP.LPSignature}
    [DecidableEq sigma.vars] [DecidableEq sigma.constants]
    [DecidableEq sigma.functionSymbols] [DecidableEq sigma.relationSymbols]
    [IsEmpty sigma.functionSymbols]
    (kb : LP.KnowledgeBase sigma) (sourceProgram : Program sigma)
    (sourceGoal : Goal sigma) (goals : List (LP.Atom sigma))
    (session : Session sigma) (fuel : Nat)
    (answer : LP.RuntimeQuery.Answer sigma) (resumed : Session sigma)
    (hProgram : sourceProgram.toLP? = some kb.prog)
    (hGoal : sourceGoal.toAtoms? = some goals)
    (hOpen : openEmpty sourceProgram sourceGoal = .ok session)
    (hPull : pull fuel session = .answer answer resumed) :
    ∃ theta : LP.Subst sigma.scoped,
      LP.SLDScopedTree kb.prog 1 (LP.queryAtScope 0 goals) theta ∧
      (∀ pair ∈ answer.queryVarMap, ∀ term,
        LP.RuntimeReadback.Heap.readTerm answer.memory.heap pair.2 = .ok term →
        theta pair.1 = term) ∧
      ∀ grounding : LP.Grounding sigma.scoped,
        ∀ atom ∈ LP.queryAtScope 0 goals,
          ((grounding.compSubst theta).groundAtom atom).unscope ∈
            LP.leastHerbrandModel kb := by
  unfold openEmpty openSession at hOpen
  rw [hProgram, hGoal] at hOpen
  cases hOpened : LP.RuntimeQuery.openQuery
      (LP.RuntimeTerm.Memory.empty sigma.scoped) 0 1 goals with
  | error error =>
      simp [hOpened] at hOpen
  | ok state =>
    simp [hOpened] at hOpen
    subst session
    unfold pull at hPull
    cases hPulled : LP.RuntimeQuery.pull (noControl sigma) kb.prog fuel state with
    | «open» openState =>
        simp [hPulled] at hPull
    | answer pulledAnswer pulledState =>
      simp [hPulled] at hPull
      obtain ⟨answerEq, _resumedEq⟩ := hPull
      subst pulledAnswer
      exact LP.RuntimeUnificationSoundness.runtimeAnswer_leastModel
        (noControl sigma) kb goals _ fuel answer _
        (fun _ => rfl) hOpened hPulled
    | terminal result =>
        simp [hPulled] at hPull

end Mettapedia.Logic.Prolog.PureRuntime
