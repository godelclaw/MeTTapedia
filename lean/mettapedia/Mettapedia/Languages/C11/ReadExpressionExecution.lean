import Mettapedia.Languages.C11.ReadExpressionStep
import Mettapedia.GSLT.Distinction.ProductiveBlocks

/-!
# Retained execution of contextual integer expressions

Configurations retain byte memory, lexical frames, the complete expression,
the next occurrence ordinal and the remaining explicit choices. Selecting a
listed alternative constructs an independent source advance. Conversely,
every independent advance and finite expression history has a constructed
choice sequence and executable realization, with exact ordered occurrences.

The common driver supplies exact budget resumption and accounts. An empty
choice sequence suspends for a scheduler choice when a reduction is available.
This scheduler request is not a C function or external service call. Invalid
choices and unavailable pure-memory operations leave the configuration stuck;
they are not silently converted into source undefined behavior. Events record
semantic operations without host publication authority. Effects, ownership
transfer, calls, loops and full C source elaboration remain separate work.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ReadExpression

open ObjectAccessMemory
open Mettapedia.GSLT.Distinction.ProductiveBlocks

structure CoreConfiguration (layout : Layout) where
  memory : State layout.representation.characters
  environment : ScopedLvalues.Environment
  expression : Expression layout
  ordinal : Nat
  deriving DecidableEq, Repr

structure Occurrence (layout : Layout) where
  ordinal : Nat
  event : Event layout
  deriving DecidableEq, Repr

inductive Advance (layout : Layout) (policy : SignedConversionPolicy) :
    CoreConfiguration layout → Occurrence layout → CoreConfiguration layout → Prop where
  | reduced (memory : State layout.representation.characters) (environment : ScopedLvalues.Environment)
      (before after : Expression layout) (observed : Event layout) (ordinal : Nat)
      (reduced : Reduction layout policy (represent memory) environment before observed after) :
      Advance layout policy ⟨memory, environment, before, ordinal⟩ ⟨ordinal, observed⟩
        ⟨memory, environment, after, ordinal + 1⟩

theorem Advance.weight {layout : Layout} {policy : SignedConversionPolicy}
    {before after : CoreConfiguration layout} {observed : Occurrence layout}
    (advanced : Advance layout policy before observed after) :
    weight after.expression < weight before.expression := by
  cases advanced with
  | reduced _ _ _ _ _ _ reduced => exact reduction_weight _ _ _ _ _ _ _ reduced

def choose (layout : Layout) (policy : SignedConversionPolicy) (before : CoreConfiguration layout)
    (index : Nat) : Option (Occurrence layout × CoreConfiguration layout) :=
  ((steps layout policy before.memory before.environment before.expression)[index]?).map fun selected =>
    (⟨before.ordinal, selected.1⟩, {before with expression := selected.2, ordinal := before.ordinal + 1})

theorem choose_sound (layout : Layout) (policy : SignedConversionPolicy)
    (before after : CoreConfiguration layout) (index : Nat) (observed : Occurrence layout)
    (chosen : choose layout policy before index = some (observed, after)) : Advance layout policy before observed after := by
  cases selected : (steps layout policy before.memory before.environment before.expression)[index]? with
  | none => simp [choose, selected] at chosen
  | some result =>
      simp [choose, selected] at chosen
      obtain ⟨rfl, rfl⟩ := chosen
      have present := List.mem_iff_getElem?.mpr ⟨index, selected⟩
      exact .reduced _ _ _ _ _ _ (steps_sound _ _ _ _ _ _ _ present)

theorem choose_complete (layout : Layout) (policy : SignedConversionPolicy)
    (before after : CoreConfiguration layout) (observed : Occurrence layout)
    (advanced : Advance layout policy before observed after) :
    ∃ index, choose layout policy before index = some (observed, after) := by
  cases advanced with
  | reduced memory environment before after observed ordinal reduced =>
      obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp (steps_complete _ _ _ _ _ _ _ reduced)
      exact ⟨index, by simp [choose, selected]⟩

theorem choose_iff (layout : Layout) (policy : SignedConversionPolicy)
    (before after : CoreConfiguration layout) (observed : Occurrence layout) :
    (∃ index, choose layout policy before index = some (observed, after)) ↔ Advance layout policy before observed after :=
  ⟨fun ⟨index, selected⟩ => choose_sound _ _ _ _ index _ selected,
    choose_complete layout policy before after observed⟩

structure Configuration (layout : Layout) where
  core : CoreConfiguration layout
  choices : List Nat
  deriving DecidableEq, Repr

inductive Request where
  | choose (alternatives : Nat)
  deriving DecidableEq, Repr

def machine (layout : Layout) (policy : SignedConversionPolicy) :
    Machine (Configuration layout) (Occurrence layout) (IntegerScalar.Value layout.parameters) Request where
  step configuration :=
    match configuration.core.expression with
    | .value scalar => some (.finish scalar)
    | .fault reason => some (.fail [⟨configuration.core.ordinal, event layout (.fault reason)⟩])
    | _ =>
        match configuration.choices with
        | [] =>
            let alternatives := steps layout policy configuration.core.memory configuration.core.environment configuration.core.expression
            if alternatives.isEmpty then none
            else some (.call (.choose alternatives.length) configuration)
        | index :: rest =>
            (choose layout policy configuration.core index).map fun selected =>
              .publish [selected.1] ⟨selected.2, rest⟩

theorem machine_publish_of_choose (layout : Layout) (policy : SignedConversionPolicy)
    (before after : CoreConfiguration layout) (index : Nat) (rest : List Nat) (observed : Occurrence layout)
    (selected : choose layout policy before index = some (observed, after)) :
    (machine layout policy).step ⟨before, index :: rest⟩ = some (.publish [observed] ⟨after, rest⟩) := by
  cases expression : before.expression <;> try {simp only [machine, expression, selected, Option.map_some]}
  · simp only [choose, expression, steps_value, List.getElem?_nil, Option.map_none, reduceCtorEq] at selected
  · simp only [choose, expression, steps_fault, List.getElem?_nil, Option.map_none, reduceCtorEq] at selected

theorem publish_sound (layout : Layout) (policy : SignedConversionPolicy)
    (before after : Configuration layout) (events : List (Occurrence layout))
    (published : (machine layout policy).step before = some (.publish events after)) :
    ∃ index rest observed, before.choices = index :: rest ∧ events = [observed] ∧ after.choices = rest ∧
      Advance layout policy before.core observed after.core := by
  unfold machine at published
  dsimp only at published
  split at published
  · cases published
  · cases published
  · split at published
    · split at published <;> cases published
    · rename_i index rest selectedChoices
      cases selected : choose layout policy before.core index with
      | none => simp [selected] at published
      | some result =>
          simp [selected] at published
          obtain ⟨rfl, rfl⟩ := published
          exact ⟨index, rest, result.1, selectedChoices, rfl, rfl,
            choose_sound layout policy before.core result.2 index result.1 selected⟩

def stamp (layout : Layout) : Nat → List (Event layout) → List (Occurrence layout)
  | _, [] => []
  | ordinal, observed :: rest => ⟨ordinal, observed⟩ :: stamp layout (ordinal + 1) rest

theorem stamp_length (layout : Layout) (ordinal : Nat) (events : List (Event layout)) :
    (stamp layout ordinal events).length = events.length := by
  induction events generalizing ordinal with
  | nil => rfl
  | cons observed rest ih => simp only [stamp, List.length_cons, ih]

theorem history_realization (layout : Layout) (policy : SignedConversionPolicy)
    (memory : State layout.representation.characters) (environment : ScopedLvalues.Environment)
    (before after : Expression layout) (events : List (Event layout))
    (history : History layout policy (represent memory) environment before events after)
    (ordinal : Nat) (remaining : List Nat) :
    ∃ choices, (machine layout policy).run events.length
      ⟨⟨memory, environment, before, ordinal⟩, choices ++ remaining⟩ =
      (stamp layout ordinal events,
        .exhausted ⟨⟨memory, environment, after, ordinal + events.length⟩, remaining⟩) := by
  induction history generalizing ordinal remaining with
  | empty expression => exact ⟨[], rfl⟩
  | next before intermediate after observed rest reduced history ih =>
      obtain ⟨choices, continued⟩ := ih (ordinal + 1) remaining
      obtain ⟨index, chosen⟩ := choose_complete layout policy
        ⟨memory, environment, before, ordinal⟩ ⟨memory, environment, intermediate, ordinal + 1⟩
        ⟨ordinal, observed⟩ (.reduced _ _ _ _ _ _ reduced)
      refine ⟨index :: choices, ?_⟩
      have first := machine_publish_of_choose layout policy _ _ index (choices ++ remaining) _ chosen
      rw [List.cons_append, List.length_cons, Machine.run_succ_publish _ first, continued]
      simp only [stamp, List.singleton_append]
      have same : ordinal + 1 + rest.length = ordinal + (rest.length + 1) := by omega
      rw [same]

theorem prefix_resumption (layout : Layout) (policy : SignedConversionPolicy) (first second : Nat)
    (initial residual : Configuration layout) (events : List (Occurrence layout))
    (paused : (machine layout policy).run first initial = (events, .exhausted residual)) :
    (machine layout policy).run (first + second) initial =
      (events ++ ((machine layout policy).run second residual).1,
        ((machine layout policy).run second residual).2) :=
  Machine.established_and_pending _ first second initial residual events paused

def price {layout : Layout} (configuration : Configuration layout) : Nat :=
  match configuration.core.expression, configuration.choices with
  | .value _, _ | .fault _, _ | _, [] => 0
  | _, _ :: _ => 1

theorem resumed_accounts (layout : Layout) (policy : SignedConversionPolicy)
    (first second : Nat) (configuration : Configuration layout) :
    (machine layout policy).spent price (first + second) configuration =
      (machine layout policy).spent price first configuration +
        (machine layout policy).spentAfter price second ((machine layout policy).run first configuration).2 :=
  Machine.spent_add _ price first second configuration

theorem observed_advance_decreases (layout : Layout) (policy : SignedConversionPolicy)
    (before after : Configuration layout) (events : List (Occurrence layout))
    (published : (machine layout policy).step before = some (.publish events after)) :
    weight after.core.expression < weight before.core.expression := by
  obtain ⟨_, _, _, _, _, _, advanced⟩ := publish_sound _ _ _ _ _ published
  exact advanced.weight

end Mettapedia.Languages.C11.ReadExpression
