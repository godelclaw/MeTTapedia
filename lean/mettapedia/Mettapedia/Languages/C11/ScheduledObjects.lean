import Mettapedia.Languages.C11.SequencingSchedule
import Mettapedia.Languages.C11.ObjectStep

/-!
# Sequenced occurrence execution connected to byte/object memory

This driver executes a finite, already constructed object-operation plan.
It retains the complete sequencing table, occurrence identities, remaining
occurrences, allocator choices and finite memory state. It checks sequencing
validity and scalar conflicts independently of the selected schedule. A
selected occurrence must be enabled by the original relation and must have
an actual byte/object transition. Both directions of this combined
correspondence are proved, with the same extensional memory/catalog endpoint.

Selection is an explicit input. When it is unavailable, the driver exposes
the enabled occurrences and saves the complete continuation. It never
chooses a favorable order to make a conflicting plan appear defined. Saved
prefix resumption reuses the resulting memory and pending occurrences.

Plans contain fixed primitive requests. Data-dependent expression building,
typed source lvalues, function calls and volatile/external actions must
construct and extend these plans through their own source rules. These
kernel receipts are not committed host effects or publication authority.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ScheduledObjects

open Sequencing
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.Distinction.ProductiveBlocks

variable {Index Object Byte : Type}

structure Plan (Index Object Byte : Type) where
  enumeration : Enumeration Index
  evaluation : Evaluation Index Object
  request : Index → ObjectStep.Request Byte

structure State (Index Byte : Type) where
  pending : List Index
  memory : ObjectStep.State Byte

structure SemanticState (Index Byte : Type) where
  pending : List Index
  memory : ObjectStep.SemanticState Byte

def represent (state : State Index Byte) : SemanticState Index Byte :=
  ⟨state.pending, ObjectStep.represent state.memory⟩

inductive Reduction (profile : ArrayPointers.DifferenceProfile) (plan : Plan Index Object Byte) :
    SemanticState Index Byte → Index → ObjectStep.Response Byte → SemanticState Index Byte → Prop where
  | execute (before after : SemanticState Index Byte) (index : Index) (response : ObjectStep.Response Byte)
      (valid : plan.evaluation.order.Valid) (clean : ¬ plan.evaluation.Undefined)
      (scheduled : SequencingSchedule.Step plan.evaluation.order before.pending index after.pending)
      (operation : ObjectStep.Reduction profile before.memory (plan.request index) response after.memory) :
      Reduction profile plan before index response after

def execute [DecidableEq Index] [DecidableEq Object] (profile : ArrayPointers.DifferenceProfile)
    (plan : Plan Index Object Byte) (choice : ExecutableStorage.AllocationChoice)
    (before : State Index Byte) (index : Index) : Option (ObjectStep.Response Byte × State Index Byte) := do
  if plan.evaluation.order.check plan.enumeration then
    if (plan.evaluation.findConflict plan.enumeration).isSome then none
    else
      let pending ← SequencingSchedule.select plan.evaluation.order before.pending index
      let (response, memory) ← ObjectStep.execute profile choice before.memory (plan.request index)
      some (response, ⟨pending, memory⟩)
  else none

theorem execute_sound [DecidableEq Index] [DecidableEq Object] (profile : ArrayPointers.DifferenceProfile)
    (plan : Plan Index Object Byte) (choice : ExecutableStorage.AllocationChoice)
    (before after : State Index Byte) (index : Index) (response : ObjectStep.Response Byte)
    (computed : execute profile plan choice before index = some (response, after)) :
    Reduction profile plan (represent before) index response (represent after) := by
  by_cases valid : plan.evaluation.order.check plan.enumeration = true
  · cases conflict : plan.evaluation.findConflict plan.enumeration with
    | some pair => simp [execute, valid, conflict] at computed
    | none =>
        cases selected : SequencingSchedule.select plan.evaluation.order before.pending index with
        | none => simp [execute, valid, conflict, selected] at computed
        | some pending =>
            cases operated : ObjectStep.execute profile choice before.memory (plan.request index) with
            | none => simp [execute, valid, conflict, selected, operated] at computed
            | some result =>
                rcases result with ⟨value, memory⟩
                simp [execute, valid, conflict, selected, operated] at computed
                obtain ⟨rfl, rfl⟩ := computed
                exact .execute _ _ index value
                  ((plan.evaluation.order.check_iff plan.enumeration).mp valid)
                  ((plan.evaluation.findConflict_none_iff plan.enumeration).mp conflict)
                  (SequencingSchedule.select_sound plan.evaluation.order before.pending pending index selected)
                  (ObjectStep.execute_sound profile choice before.memory memory (plan.request index) value operated)
  · simp [execute, valid] at computed

theorem execute_complete [DecidableEq Index] [DecidableEq Object] (profile : ArrayPointers.DifferenceProfile)
    (plan : Plan Index Object Byte) (before : State Index Byte) (after : SemanticState Index Byte)
    (index : Index) (response : ObjectStep.Response Byte)
    (reduced : Reduction profile plan (represent before) index response after) :
    ∃ choice saved, execute profile plan choice before index = some (response, saved) ∧ represent saved = after := by
  cases reduced with
  | execute _ after _ valid clean scheduled operation =>
      obtain ⟨choice, memory, operated, final⟩ :=
        ObjectStep.execute_complete profile before.memory (plan.request index) response after.memory operation
      have selected := SequencingSchedule.select_complete plan.evaluation.order before.pending after.pending index scheduled
      have validated := (plan.evaluation.order.check_iff plan.enumeration).mpr valid
      have noConflict := (plan.evaluation.findConflict_none_iff plan.enumeration).mpr clean
      refine ⟨choice, ⟨after.pending, memory⟩, ?_, ?_⟩
      · simp [execute, validated, noConflict, selected, operated]
      · cases after
        simp only [represent, final]

theorem execute_iff [DecidableEq Index] [DecidableEq Object] (profile : ArrayPointers.DifferenceProfile)
    (plan : Plan Index Object Byte) (before : State Index Byte) (after : SemanticState Index Byte)
    (index : Index) (response : ObjectStep.Response Byte) :
    (∃ choice saved, execute profile plan choice before index = some (response, saved) ∧ represent saved = after) ↔
      Reduction profile plan (represent before) index response after := by
  constructor
  · rintro ⟨choice, saved, computed, rfl⟩
    exact execute_sound profile plan choice before saved index response computed
  · exact execute_complete profile plan before after index response

theorem executed_consumes_once [DecidableEq Index] [DecidableEq Object] (profile : ArrayPointers.DifferenceProfile)
    (plan : Plan Index Object Byte) (choice : ExecutableStorage.AllocationChoice)
    (before after : State Index Byte) (index : Index) (response : ObjectStep.Response Byte)
    (computed : execute profile plan choice before index = some (response, after)) (unique : before.pending.Nodup) :
    after.pending.length + 1 = before.pending.length ∧ after.pending.Nodup ∧ index ∉ after.pending := by
  cases execute_sound profile plan choice before after index response computed with
  | execute _ _ _ valid clean scheduled operation =>
      cases scheduled with
      | consume _ _ ready removed => exact ⟨removed.length, removed.unique unique, removed.absent unique⟩

structure Selection (Index : Type) where
  index : Index
  allocator : ExecutableStorage.AllocationChoice
  deriving DecidableEq, Repr

structure Configuration (Index Byte : Type) where
  state : State Index Byte
  selections : List (Selection Index)

structure Receipt (Index Byte : Type) where
  index : Index
  response : ObjectStep.Response Byte
  before : State Index Byte
  after : State Index Byte

inductive Verdict (Index Byte : Type) where
  | returned (saved : Configuration Index Byte)
  | refused (saved : Configuration Index Byte)

structure SelectionRequest (Index : Type) where
  enabled : List Index
  deriving DecidableEq, Repr

def admissible [DecidableEq Index] [DecidableEq Object] (plan : Plan Index Object Byte) : Bool :=
  plan.evaluation.order.check plan.enumeration && !(plan.evaluation.findConflict plan.enumeration).isSome

def machine [DecidableEq Index] [DecidableEq Object] (profile : ArrayPointers.DifferenceProfile)
    (plan : Plan Index Object Byte) :
    Machine (Configuration Index Byte) (Receipt Index Byte) (Verdict Index Byte) (SelectionRequest Index) where
  step configuration := some <|
    if admissible plan then
      match configuration.state.pending with
      | [] => .finish (.returned configuration)
      | _ :: _ =>
          match configuration.selections with
          | [] => .call ⟨SequencingSchedule.choices plan.evaluation.order configuration.state.pending⟩ configuration
          | selection :: rest =>
              match execute profile plan selection.allocator configuration.state selection.index with
              | none => .finish (.refused configuration)
              | some (response, after) =>
                  .publish [⟨selection.index, response, configuration.state, after⟩] ⟨after, rest⟩
    else .finish (.refused configuration)

def ValidReceipt (profile : ArrayPointers.DifferenceProfile) (plan : Plan Index Object Byte)
    (receipt : Receipt Index Byte) : Prop :=
  Reduction profile plan (represent receipt.before) receipt.index receipt.response (represent receipt.after)

theorem run_receipts_valid [DecidableEq Index] [DecidableEq Object] (profile : ArrayPointers.DifferenceProfile)
    (plan : Plan Index Object Byte) (fuel : Nat) (initial : Configuration Index Byte) :
    ∀ receipt ∈ ((machine profile plan).run fuel initial).1, ValidReceipt profile plan receipt := by
  induction fuel generalizing initial with
  | zero => simp [Machine.run]
  | succ fuel ih =>
      by_cases allowed : admissible plan = true
      · cases pending : initial.state.pending with
        | nil => simp [Machine.run, machine, allowed, pending]
        | cons head tail =>
            cases selections : initial.selections with
            | nil => simp [Machine.run, machine, allowed, pending, selections]
            | cons selection rest =>
                cases computed : execute profile plan selection.allocator initial.state selection.index with
                | none => simp [Machine.run, machine, allowed, pending, selections, computed]
                | some result =>
                    rcases result with ⟨response, after⟩
                    simp only [Machine.run, machine, allowed, ↓reduceIte, pending, selections,
                      computed, List.singleton_append, List.mem_cons]
                    intro receipt present
                    rcases present with rfl | following
                    · exact execute_sound profile plan selection.allocator initial.state after selection.index response computed
                    · have child := ih ⟨after, rest⟩ receipt
                      simp only [machine, allowed, ↓reduceIte] at child
                      exact child following
      · simp [Machine.run, machine, allowed]

theorem resume_after_prefix [DecidableEq Index] [DecidableEq Object] (profile : ArrayPointers.DifferenceProfile)
    (plan : Plan Index Object Byte) (first second : Nat) (initial saved : Configuration Index Byte)
    (events : List (Receipt Index Byte)) (paused : (machine profile plan).run first initial = (events, .exhausted saved)) :
    (machine profile plan).run (first + second) initial =
      (events ++ ((machine profile plan).run second saved).1, ((machine profile plan).run second saved).2) :=
  (machine profile plan).established_and_pending first second initial saved events paused

def productive [DecidableEq Index] [DecidableEq Object] (profile : ArrayPointers.DifferenceProfile)
    (plan : Plan Index Object Byte) : (machine profile plan).Productive where
  rank _ := 0
  moves configuration := by simp [machine]
  silent_decreases := by
    intro configuration next silent
    simp only [machine, Option.some.injEq] at silent
    split at silent
    · split at silent
      · contradiction
      · split at silent
        · contradiction
        · split at silent <;> contradiction
    · contradiction

end Mettapedia.Languages.C11.ScheduledObjects
