import Mettapedia.Languages.MeTTa.HE.TypedApplyEncoding

/-!
# Validated reflection of the typed argument component

The admission check verifies the selected-prefix length, domain arity and
live consumer position of every frame. The executable data step is connected
to the existing inductive application rules, including rejected merges and
binder extensions. A successful decode alone is not admission.

The interaction boundary remains the finite argument services in
`TypedApplyDerivation.Services`; this module does not implement their inner
evaluation, effects or native callbacks.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.TypedApplyReflection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open TypedApplyDerivation (Services)
open TypedApplyStreaming (Configuration next events machine)
open TypedApplyEncoding

def FrameWellFormed : TypedApplyFrame → Prop
  | .apply state => state.WellFormed
  | .argConsumer _ _ _ state => state.WellFormed ∧ state.idx < state.origArgs.length

instance (frame : TypedApplyFrame) : Decidable (FrameWellFormed frame) := by
  cases frame <;> unfold FrameWellFormed TypedApplyState.WellFormed <;> infer_instance

def WellFormed (state : Configuration) : Prop :=
  ∀ frame ∈ state.worklist, FrameWellFormed frame

instance (state : Configuration) : Decidable (WellFormed state) := by
  unfold WellFormed
  infer_instance

theorem initial_wellFormed (state : TypedApplyState) (valid : state.WellFormed) :
    WellFormed (.initial state) := by
  simpa [WellFormed, TypedApplyConfig.initial, FrameWellFormed] using valid

theorem advance_wellFormed (state : TypedApplyState) (value : Atom) (environment : Bindings)
    (valid : state.WellFormed) (live : state.idx < state.origArgs.length) :
    (state.advance value environment).WellFormed := by
  rcases valid with ⟨selectedLength, arity, bound⟩
  simp only [TypedApplyState.advance, TypedApplyState.WellFormed,
    List.length_append, List.length_singleton]
  exact ⟨by omega, arity, by omega⟩

/-- Every independent application rule preserves admitted frame structure. -/
theorem source_preserves_wellFormed (services : Services) (before after : Configuration)
    (source : TypedApplyStep services.evaluate services.apply services.merge
      services.extend services.raw before after) (valid : WellFormed before) :
    WellFormed after := by
  cases source <;>
    simp only [WellFormed, List.forall_mem_cons, FrameWellFormed] at valid ⊢
  all_goals first
    | exact valid.2
    | exact valid
    | exact ⟨advance_wellFormed _ _ _ valid.1 (by assumption), valid.2⟩
    | exact ⟨⟨valid.1, by assumption⟩, valid.2⟩
    | exact ⟨advance_wellFormed _ _ _ valid.1.1 valid.1.2, valid⟩

/-- The executable step is also complete for the independent rules. -/
theorem source_eq_next (services : Services) (before after : Configuration)
    (source : TypedApplyStep services.evaluate services.apply services.merge
      services.extend services.raw before after) :
    after = next services before := by
  cases source <;>
    simp_all [next, stepConfig, processFrame, processApplyFrame,
      processConsumerFrame, getArgType]
  all_goals
    rcases ‹_ ∨ _› with normal | unchanged <;> simp_all

theorem source_not_done (services : Services) (before after : Configuration)
    (source : TypedApplyStep services.evaluate services.apply services.merge
      services.extend services.raw before after) :
    ¬before.isDone = true := by
  cases source <;> simp [TypedApplyConfig.isDone]

abbrev Action := Transition Configuration ResultPair Configuration Empty

/-- Observable transitions are licensed by the inductive rules and exact
history extension, independently of the executable transition classifier. -/
inductive ObservedStep (services : Services) : Configuration → Action → Prop where
  | finished (state : Configuration) (done : state.isDone = true) :
      ObservedStep services state (.finish state)
  | administrative (before after : Configuration)
      (source : TypedApplyStep services.evaluate services.apply services.merge
        services.extend services.raw before after)
      (sameHistory : after.emitted = before.emitted) :
      ObservedStep services before (.silent after)
  | emitted (before after : Configuration) (newResults : ResultList)
      (source : TypedApplyStep services.evaluate services.apply services.merge
        services.extend services.raw before after)
      (history : after.emitted = before.emitted ++ newResults)
      (visible : newResults ≠ []) :
      ObservedStep services before (.publish newResults after)

theorem observed_sound (services : Services) (state : Configuration) (action : Action)
    (executed : (machine services).step state = some action) :
    ObservedStep services state action := by
  by_cases done : state.isDone = true
  · rw [TypedApplyStreaming.step_done services state done] at executed
    cases Option.some.inj executed
    exact .finished state done
  · have pending : state.worklist ≠ [] := by
      simpa [TypedApplyConfig.isDone, List.isEmpty_iff] using done
    have source := stepConfig_spec services.evaluate services.apply services.merge
      services.extend services.raw state pending
    have history := TypedApplyStreaming.next_history services state pending
    by_cases silent : events state (next services state) = []
    · rw [TypedApplyStreaming.step_silent services state done silent] at executed
      cases Option.some.inj executed
      exact .administrative state (next services state) source (by simpa [silent] using history.symm)
    · rw [TypedApplyStreaming.step_publish services state done silent] at executed
      cases Option.some.inj executed
      exact .emitted state (next services state) (events state (next services state))
        source history.symm silent

theorem observed_complete (services : Services) (state : Configuration) (action : Action)
    (source : ObservedStep services state action) :
    (machine services).step state = some action := by
  cases source with
  | finished done => exact TypedApplyStreaming.step_done services state done
  | administrative after source history =>
      have done := source_not_done services state after source
      have equal := source_eq_next services state after source
      subst after
      have silent : events state (next services state) = [] := by
        simp [events, history]
      exact TypedApplyStreaming.step_silent services state done silent
  | emitted after newResults source history visible =>
      have done := source_not_done services state after source
      have equal := source_eq_next services state after source
      subst after
      have observed : events state (next services state) = newResults := by
        simp [events, history]
      simpa [observed] using
        TypedApplyStreaming.step_publish services state done (by simpa [observed] using visible)

theorem observed_iff (services : Services) (state : Configuration) (action : Action) :
    (machine services).step state = some action ↔ ObservedStep services state action :=
  ⟨observed_sound services state action, observed_complete services state action⟩

def actionData : Action → Atom
  | .silent state => .expression [.symbol "he-typed-silent-v1", configurationData state]
  | .publish emitted state =>
      .expression [.symbol "he-typed-publish-v1", resultsData emitted, configurationData state]
  | .finish state => .expression [.symbol "he-typed-finish-v1", configurationData state]
  | .fail emitted => .expression [.symbol "he-typed-fail-v1", resultsData emitted]
  | .call request _ => nomatch request

def readAction : Atom → Option Action
  | .expression [.symbol "he-typed-silent-v1", state] => do
      return .silent (← readConfiguration state)
  | .expression [.symbol "he-typed-publish-v1", emitted, state] => do
      return .publish (← readResults emitted) (← readConfiguration state)
  | .expression [.symbol "he-typed-finish-v1", state] => do
      return .finish (← readConfiguration state)
  | .expression [.symbol "he-typed-fail-v1", emitted] => do
      return .fail (← readResults emitted)
  | _ => none

@[simp] theorem readAction_actionData (action : Action) :
    readAction (actionData action) = some action := by
  cases action with
  | call request _ => nomatch request
  | silent state => simp [actionData, readAction]
  | publish emitted state => simp [actionData, readAction]
  | finish state => simp [actionData, readAction]
  | fail emitted => simp [actionData, readAction]

theorem actionData_injective : Function.Injective actionData := by
  intro left right equal
  have decoded := congrArg readAction equal
  simpa using decoded

/-- Decode and admit the complete saved component before advancing it.
Malformed or structurally invalid data receives no transition. -/
def stepData (services : Services) (data : Atom) : Option Atom := do
  let state ← readConfiguration data
  if WellFormed state then actionData <$> (machine services).step state else none

@[simp] theorem stepData_configurationData (services : Services) (state : Configuration) :
    stepData services (configurationData state) =
      if WellFormed state then actionData <$> (machine services).step state else none := by
  simp [stepData]

/-- Every represented step is exactly an admitted independent rule with its
declared history observation, and every such rule is executable. -/
theorem stepData_iff (services : Services) (state : Configuration) (action : Action) :
    stepData services (configurationData state) = some (actionData action) ↔
      WellFormed state ∧ ObservedStep services state action := by
  rw [stepData_configurationData]
  by_cases valid : WellFormed state
  · simp only [if_pos valid]
    constructor
    · intro executed
      rcases Option.map_eq_some_iff.mp executed with ⟨actual, actualStep, represented⟩
      have equal := actionData_injective represented
      subst actual
      exact ⟨valid, observed_sound services state action actualStep⟩
    · intro source
      rw [observed_complete services state action source.2]
      rfl
  · simp [valid]

/-- The guarantee also covers arbitrary incoming data, rather than only
configurations constructed by the encoder. -/
theorem stepData_decoded_iff (services : Services) (input output : Atom) :
    stepData services input = some output ↔
      ∃ state action, readConfiguration input = some state ∧ WellFormed state ∧
        ObservedStep services state action ∧ actionData action = output := by
  cases decoded : readConfiguration input with
  | none => simp [stepData, decoded]
  | some state =>
      by_cases valid : WellFormed state
      · simp only [stepData, decoded]
        change (if WellFormed state then actionData <$> (machine services).step state else none)
          = some output ↔ _
        rw [if_pos valid]
        constructor
        · intro executed
          rcases Option.map_eq_some_iff.mp executed with ⟨action, actual, represented⟩
          exact ⟨state, action, rfl, valid,
            observed_sound services state action actual, represented⟩
        · rintro ⟨returned, action, same, admitted, source, represented⟩
          cases Option.some.inj same
          rw [observed_complete services state action source]
          exact congrArg some represented
      · simp [stepData, decoded, valid]

def actionResidual : Action → Option Configuration
  | .silent state | .publish _ state | .finish state => some state
  | .fail _ => none
  | .call request _ => nomatch request

/-- A successful observed transition keeps its retained state admitted. -/
theorem observed_preserves_wellFormed (services : Services) (before : Configuration)
    (action : Action) (saved : Configuration) (source : ObservedStep services before action)
    (valid : WellFormed before) (returned : actionResidual action = some saved) :
    WellFormed saved := by
  cases source with
  | finished done =>
      cases Option.some.inj returned
      exact valid
  | administrative after source _ =>
      cases Option.some.inj returned
      exact source_preserves_wellFormed services before saved source valid
  | emitted after emitted source _ _ =>
      cases Option.some.inj returned
      exact source_preserves_wellFormed services before saved source valid

/-- Every configuration returned by the common driver keeps admitted frame
structure. This uses its constructed path through the independent rules. -/
theorem run_preserves_wellFormed (services : Services) (budget : Nat)
    (before saved : Configuration) (valid : WellFormed before)
    (returned : TypedApplyStreaming.readback ((machine services).run budget before).2 = some saved) :
    WellFormed saved := by
  have path := TypedApplyStreaming.run_source services budget before saved returned
  clear returned
  induction path with
  | refl => exact valid
  | step source tail ih =>
      exact ih (source_preserves_wellFormed services _ _ source valid)

end Mettapedia.Languages.MeTTa.HE.TypedApplyReflection
