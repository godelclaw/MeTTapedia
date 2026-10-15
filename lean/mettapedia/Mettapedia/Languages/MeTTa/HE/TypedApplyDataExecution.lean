import Mettapedia.Languages.MeTTa.HE.TypedApplyReflection

/-!
# Executing represented typed argument states

The driver decodes and admits the saved configuration on every transition,
executes the data step, and decodes its declared action. The correspondence
preserves the ordered event list and every retained outcome at the same
transition budget. It is a constructed instance for the typed application
component, with its finite leaf services still explicit.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.TypedApplyDataExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open TypedApplyDerivation (Services)
open TypedApplyStreaming (Configuration machine next events)
open TypedApplyReflection
open TypedApplyEncoding

def representedAction : Action → Transition Atom ResultPair Atom Empty
  | .silent state => .silent (configurationData state)
  | .publish emitted state => .publish emitted (configurationData state)
  | .finish state => .finish (configurationData state)
  | .fail emitted => .fail emitted
  | .call request _ => nomatch request

/-- Incoming data is checked on every advance, including resumption. -/
def dataMachine (services : Services) : Machine Atom ResultPair Atom Empty where
  step input := do
    let output ← stepData services input
    let action ← readAction output
    return representedAction action

theorem step_representation (services : Services) (state : Configuration)
    (valid : WellFormed state) :
    (dataMachine services).step (configurationData state) =
      representedAction <$> (machine services).step state := by
  cases executed : (machine services).step state with
  | none => simp [dataMachine, stepData_configurationData, valid, executed]
  | some action => simp [dataMachine, stepData_configurationData, valid, executed]

theorem step_done (services : Services) (state : Configuration)
    (valid : WellFormed state) (done : state.isDone = true) :
    (dataMachine services).step (configurationData state) =
      some (.finish (configurationData state)) := by
  rw [step_representation services state valid, TypedApplyStreaming.step_done services state done]
  rfl

theorem step_silent (services : Services) (state : Configuration)
    (valid : WellFormed state) (done : ¬state.isDone = true)
    (silent : events state (next services state) = []) :
    (dataMachine services).step (configurationData state) =
      some (.silent (configurationData (next services state))) := by
  rw [step_representation services state valid,
    TypedApplyStreaming.step_silent services state done silent]
  rfl

theorem step_publish (services : Services) (state : Configuration)
    (valid : WellFormed state) (done : ¬state.isDone = true)
    (visible : events state (next services state) ≠ []) :
    (dataMachine services).step (configurationData state) =
      some (.publish (events state (next services state))
        (configurationData (next services state))) := by
  rw [step_representation services state valid,
    TypedApplyStreaming.step_publish services state done visible]
  rfl

def representedOutcome : Outcome Configuration Configuration Empty → Outcome Atom Atom Empty
  | .finished state => .finished (configurationData state)
  | .exhausted state => .exhausted (configurationData state)
  | .stuck state => .stuck (configurationData state)
  | .faulted => .faulted
  | .suspended request _ => nomatch request

/-- Data execution and component execution have exactly the same ordered
occurrences, outcomes and saved states at every finite budget. -/
theorem run_representation (services : Services) (budget : Nat) (state : Configuration)
    (valid : WellFormed state) :
    (dataMachine services).run budget (configurationData state) =
      (((machine services).run budget state).1,
        representedOutcome ((machine services).run budget state).2) := by
  induction budget generalizing state with
  | zero => rfl
  | succ budget ih =>
      by_cases done : state.isDone = true
      · rw [(dataMachine services).run_succ_finish (step_done services state valid done),
          (machine services).run_succ_finish (TypedApplyStreaming.step_done services state done)]
        rfl
      · have pending : state.worklist ≠ [] := by
          simpa [TypedApplyConfig.isDone, List.isEmpty_iff] using done
        have nextValid := source_preserves_wellFormed services state (next services state)
          (stepConfig_spec _ _ _ _ _ state pending) valid
        by_cases silent : events state (next services state) = []
        · rw [(dataMachine services).run_succ_silent
              (step_silent services state valid done silent),
            (machine services).run_succ_silent
              (TypedApplyStreaming.step_silent services state done silent)]
          exact ih (next services state) nextValid
        · rw [(dataMachine services).run_succ_publish
              (step_publish services state valid done silent),
            (machine services).run_succ_publish
              (TypedApplyStreaming.step_publish services state done silent),
            ih (next services state) nextValid]

/-- The encoded driver's residual is the representation of the actual
saved component, so later budgets preserve the original ordered prefix. -/
theorem resume_after_prefix (services : Services) (first second : Nat)
    (initial saved : Configuration) (emitted : ResultList) (valid : WellFormed initial)
    (paused : (machine services).run first initial = (emitted, .exhausted saved)) :
    (dataMachine services).run (first + second) (configurationData initial) =
      (emitted ++ ((dataMachine services).run second (configurationData saved)).1,
        ((dataMachine services).run second (configurationData saved)).2) := by
  have encoded := run_representation services first initial valid
  rw [paused] at encoded
  exact (dataMachine services).established_and_pending first second
    (configurationData initial) (configurationData saved) emitted encoded

/-- The component's proved work account supplies an actual finishing budget
for data execution. This does not bound the inner work of its leaf services. -/
theorem finishes (services : Services) (state : Configuration) (valid : WellFormed state)
    (budget : Nat) (enough : TypedApplyStreaming.rank services state + 1 ≤ budget) :
    ∃ emitted final, (dataMachine services).run budget (configurationData state) =
      (emitted, .finished (configurationData final)) := by
  rcases TypedApplyStreaming.finishes services budget state enough with ⟨emitted, final, completed⟩
  refine ⟨emitted, final, ?_⟩
  rw [run_representation services budget state valid, completed]
  rfl

/-- A full encoded run also constructs the independent argument derivations. -/
theorem completed_initial (services : Services) (state : TypedApplyState)
    (valid : state.WellFormed) (budget : Nat) (emitted : ResultList) (final : Configuration)
    (completed : (machine services).run budget (.initial state) = (emitted, .finished final)) :
    (dataMachine services).run budget (configurationData (.initial state)) =
      (emitted, .finished (configurationData final)) ∧
    emitted = typedApplyDirect services.evaluate services.apply services.merge
      services.extend services.raw state ∧
    (∀ result, result ∈ emitted ↔ TypedApplyDerivation.Derivation services state result) := by
  constructor
  · rw [run_representation services budget (.initial state) (initial_wellFormed state valid),
      completed]
    rfl
  · exact TypedApplyStreaming.completed_initial services state budget emitted final completed

end Mettapedia.Languages.MeTTa.HE.TypedApplyDataExecution
