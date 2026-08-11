import Mettapedia.Logic.Prolog.RuntimeControl
import Mettapedia.Logic.Prolog.PureRuntime
import Mettapedia.Logic.LP.RuntimeQueryConservation
import Mettapedia.Logic.LP.RuntimeUnificationSoundness

/-!
# Grounding the canonical typed Prolog runtime

This file attaches the existing LP soundness endpoint to execution through
`RuntimeControl.step` and `RuntimeControl.pull`.  It does so by instantiating
the conservation theorem of the shared `RuntimeQuery.stepCore`; no second
resolver or semantic transition relation is introduced.

The present certificate covers the embedded pure definite-clause fragment.
Each additional typed control action must extend the semantic certificate
before it can inherit a stronger grounding claim.
-/

namespace Mettapedia.Logic.Prolog.RuntimeControl

open Mettapedia.Logic
open LP.RuntimeTerm LP.RuntimeMaterialize
open LP.RuntimeQuery
open LP.RuntimeQuery.Conservation

/-- The typed clause and instruction representations realize the pure LP
specialization through the unchanged shared machine. -/
def pureCoreRealization {sigma : LP.LPSignature}
    [DecidableEq sigma.scoped.vars] [DecidableEq sigma.relationSymbols]
    (program : LP.Program sigma) :
    Realization
      (LP.RuntimeQuery.lpClauseMaterializer (σ := sigma))
      (clauseMaterializer (sigma := sigma))
      (LP.RuntimeQuery.lpDispatchAction
        (PureRuntime.noControl sigma) program)
      (dispatchAction (Program.ofLP program))
      RuntimeGoal.call Clause.ofLP := by
  constructor
  · intro memory scope clause
    simp only [clauseMaterializer, Clause.atScope_ofLP,
      materializeClause_ofLP]
    unfold LP.RuntimeQuery.lpClauseMaterializer
    cases hMaterialize : LP.RuntimeMaterialize.materializeClause memory
        (clause.atScope scope) <;>
      simp [hMaterialize, Except.map, mapMaterializedBody,
        RuntimeClause.ofLP, RuntimeGoal.calls]
  · intro next
    simp [dispatchAction, LP.RuntimeQuery.lpDispatchAction,
      PureRuntime.noControl, clausesFor_ofLP, mapDispatchAction]

/-- Pure source queries realize the LP query materializer through the same
typed `call` embedding. -/
def pureQueryRealization {sigma : LP.LPSignature}
    [DecidableEq sigma.vars] :
    QueryRealization
      (LP.RuntimeQuery.lpQueryMaterializer (σ := sigma))
      (queryMaterializer (sigma := sigma))
      RuntimeGoal.call Goal.calls := by
  constructor
  intro memory scope goals
  rw [queryMaterializer_calls]
  unfold LP.RuntimeQuery.lpQueryMaterializer
  cases hMaterialize : LP.RuntimeMaterialize.materializeGoals memory
      (LP.queryAtScope scope goals) <;>
    simp [hMaterialize, Except.map, mapMaterializedQuery, RuntimeGoal.calls]

/-- Opening an embedded definite query through typed Prolog is the conserved
realization of opening it through the LP specialization. -/
theorem openQuery_calls_conserves {sigma : LP.LPSignature}
    [DecidableEq sigma.vars]
    (memory : Memory sigma.scoped) (queryScope nextScope : Nat)
    (goals : List (LP.Atom sigma)) :
    openQuery memory queryScope nextScope (Goal.calls goals) =
      (LP.RuntimeQuery.openQuery memory queryScope nextScope goals).map
        (mapState RuntimeGoal.call Clause.ofLP) := by
  unfold openQuery LP.RuntimeQuery.openQuery
  exact openQueryCore_conserves
    (sourceClause := Clause.ofLP) pureQueryRealization
    memory queryScope nextScope goals

/-- Every typed Prolog step on an embedded definite program is the conserved
realization of the LP step on the same heap, choices, and scope supply. -/
theorem step_ofLP_conserves {sigma : LP.LPSignature}
    [DecidableEq sigma.vars] [DecidableEq sigma.constants]
    [DecidableEq sigma.functionSymbols] [DecidableEq sigma.relationSymbols]
    (program : LP.Program sigma) (state : LP.RuntimeQuery.State sigma) :
    step (Program.ofLP program)
        (mapState RuntimeGoal.call Clause.ofLP state) =
      mapStepResult RuntimeGoal.call Clause.ofLP
        (LP.RuntimeQuery.step (PureRuntime.noControl sigma) program state) := by
  unfold step LP.RuntimeQuery.step
  exact stepCore_conserves (pureCoreRealization program) state

/-- The conservation law extends to every exact demand-driven fuel prefix. -/
theorem pull_ofLP_conserves {sigma : LP.LPSignature}
    [DecidableEq sigma.vars] [DecidableEq sigma.constants]
    [DecidableEq sigma.functionSymbols] [DecidableEq sigma.relationSymbols]
    (program : LP.Program sigma) (fuel : Nat)
    (state : LP.RuntimeQuery.State sigma) :
    pull (Program.ofLP program) fuel
        (mapState RuntimeGoal.call Clause.ofLP state) =
      mapPullResult RuntimeGoal.call Clause.ofLP
        (LP.RuntimeQuery.pull (PureRuntime.noControl sigma) program fuel state) := by
  unfold pull LP.RuntimeQuery.pull
  exact pullCore_conserves (pureCoreRealization program) fuel state

/-- **Canonical typed-runtime grounding, pure function-free fragment.**
An answer actually returned by `RuntimeControl.pull` on embedded definite
source carries a standardized-apart SLD derivation and is true in the same
least Herbrand model as the `Logic.LP` kernel. -/
theorem pureCallAnswer_leastModel {sigma : LP.LPSignature}
    [DecidableEq sigma.vars] [DecidableEq sigma.constants]
    [DecidableEq sigma.functionSymbols] [DecidableEq sigma.relationSymbols]
    [IsEmpty sigma.functionSymbols]
    (kb : LP.KnowledgeBase sigma) (goals : List (LP.Atom sigma))
    (state : State sigma) (fuel : Nat) (answer : Answer sigma)
    (resumed : State sigma)
    (hOpen : openQuery (Memory.empty sigma.scoped) 0 1 (Goal.calls goals) =
      .ok state)
    (hPull : pull (Program.ofLP kb.prog) fuel state =
      .answer answer resumed) :
    ∃ theta : LP.Subst sigma.scoped,
      LP.SLDScopedTree kb.prog 1 (LP.queryAtScope 0 goals) theta ∧
      (∀ pair ∈ answer.queryVarMap, ∀ term,
        LP.RuntimeReadback.Heap.readTerm answer.memory.heap pair.2 = .ok term →
        theta pair.1 = term) ∧
      ∀ grounding : LP.Grounding sigma.scoped,
        ∀ atom ∈ LP.queryAtScope 0 goals,
          ((grounding.compSubst theta).groundAtom atom).unscope ∈
            LP.leastHerbrandModel kb := by
  rw [openQuery_calls_conserves] at hOpen
  cases hOpened : LP.RuntimeQuery.openQuery
      (Memory.empty sigma.scoped) 0 1 goals with
  | error error =>
      simp [Except.map, hOpened] at hOpen
  | ok sourceState =>
      rw [hOpened] at hOpen
      change Except.ok (mapState RuntimeGoal.call Clause.ofLP sourceState) =
        Except.ok state at hOpen
      injection hOpen with hState
      subst state
      rw [pull_ofLP_conserves] at hPull
      cases hPulled : LP.RuntimeQuery.pull (PureRuntime.noControl sigma)
          kb.prog fuel sourceState with
      | «open» openState =>
          simp [mapPullResult, hPulled] at hPull
      | terminal result =>
          simp [mapPullResult, hPulled] at hPull
      | answer sourceAnswer sourceResumed =>
          simp [mapPullResult, hPulled] at hPull
          obtain ⟨answerEq, _resumedEq⟩ := hPull
          subst sourceAnswer
          exact LP.RuntimeUnificationSoundness.runtimeAnswer_leastModel
            (PureRuntime.noControl sigma) kb goals sourceState fuel answer
            sourceResumed (fun _ => rfl) hOpened hPulled

end Mettapedia.Logic.Prolog.RuntimeControl
