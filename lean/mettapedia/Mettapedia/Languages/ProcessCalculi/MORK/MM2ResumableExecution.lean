import Mettapedia.Languages.ProcessCalculi.MORK.MM2RuleScopedExecution
import Mettapedia.Machines.Cursor.ProducerOccurrenceLog
import Mettapedia.Machines.ResumableRegion

/-!
# Suspension at MM2 rule boundaries

The existing least-key rule-scoped evaluator retains its complete workspace
between bounded runs. It needs no host-language call stack at this boundary.
The split law preserves the exact ordered workspace and successful-step count,
including executable directives installed or removed by earlier firings.

One step here is a whole rule firing. Interrupting an expensive match or sink
batch within a firing requires finer residual state and a separate refinement.
The theorem fixes the policy and workspace while paused; it does not authorize
ignoring intervening edits, permission changes or external effects.

`controlledActivation` is an optional gate in front of one raw consume step,
before that step removes its selected exec. It is not installed in `machine`.
The pre-existing `machine` already defines its step as
`cRuleScopedSourceWorkQueueStep`, and this file adds no alias of that
definition. The runner takes no diary argument and does not publish a
transaction receipt. `activationRead` is the restored logical read. Native
currentness uses the live `SpaceReadToken`; these theorems do not equate the
two.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2ResumableExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open ReflectiveComputable
open Mettapedia.Machines

abbrev machine (policy : UnsupportedExecPolicy) : MachineCore (List Atom) where
  State := List Atom
  load := id
  step := cRuleScopedSourceWorkQueueStep policy

/-- Connect the generic region executor to the already existing MM2 evaluator. -/
theorem runSlice_eq_existing (policy : UnsupportedExecPolicy) (fuel : Nat)
    (workspace : List Atom) :
    (machine policy).runSlice fuel workspace =
      cRuleScopedSourceWorkQueueRunN policy fuel workspace := by
  induction fuel generalizing workspace with
  | zero => rfl
  | succ fuel ih =>
      simp only [MachineCore.runSlice, machine, cRuleScopedSourceWorkQueueRunN]
      cases transition : cRuleScopedSourceWorkQueueStep policy workspace with
      | none => rfl
      | some next => simp only [ih]

theorem pause_resume_exact (policy : UnsupportedExecPolicy) (first second : Nat)
    (workspace : List Atom) :
    cRuleScopedSourceWorkQueueRunN policy (first + second) workspace =
      let earlier := cRuleScopedSourceWorkQueueRunN policy first workspace
      let later := cRuleScopedSourceWorkQueueRunN policy second earlier.1
      (later.1, earlier.2 + later.2) := by
  simpa only [runSlice_eq_existing] using
    MachineCore.runSlice_add (machine policy) first second workspace

theorem used_le_budget (policy : UnsupportedExecPolicy) (fuel : Nat)
    (workspace : List Atom) :
    (cRuleScopedSourceWorkQueueRunN policy fuel workspace).2 ≤ fuel := by
  simpa only [runSlice_eq_existing] using
    MachineCore.runSlice_used_le (machine policy) fuel workspace

theorem early_stop_quiescent (policy : UnsupportedExecPolicy) (fuel : Nat)
    (workspace : List Atom)
    (early : (cRuleScopedSourceWorkQueueRunN policy fuel workspace).2 < fuel) :
    cRuleScopedSourceWorkQueueStep policy
      (cRuleScopedSourceWorkQueueRunN policy fuel workspace).1 = none := by
  have translated : ((machine policy).runSlice fuel workspace).2 < fuel := by
    simpa only [runSlice_eq_existing] using early
  simpa only [runSlice_eq_existing] using
    MachineCore.runSlice_under_budget_final (machine policy) fuel workspace translated

namespace Controls

def fact (label : String) : Atom := .expression [.symbol label]

def rule (priority label input output : String) : Atom :=
  .expression [.symbol "exec", .expression [.symbol priority, .symbol label],
    .expression [.symbol ",", fact input],
    .expression [.symbol "O",
      .expression [.symbol "-", fact input],
      .expression [.symbol "+", fact output]]]

def first : Atom := rule "0" "first" "start" "middle"
def second : Atom := rule "1" "second" "middle" "done"
def initial : List Atom := [first, second, fact "start"]

theorem first_slice_has_live_residual :
    cRuleScopedSourceWorkQueueRunN .leaveInert 1 initial =
      ([second, fact "middle"], 1) := by decide

theorem resumed_slice_finishes :
    cRuleScopedSourceWorkQueueRunN .leaveInert 1 [second, fact "middle"] =
      ([fact "done"], 1) := by decide

theorem complete_run_is_two_firings :
    cRuleScopedSourceWorkQueueRunN .leaveInert 10 initial = ([fact "done"], 2) := by
  decide

/-- Both slices use their entire budget; only the second endpoint is quiescent. -/
theorem whole_budget_is_not_completion :
    (cRuleScopedSourceWorkQueueRunN .leaveInert 1 initial).2 = 1 ∧
      (cRuleScopedSourceWorkQueueRunN .leaveInert 1 [second, fact "middle"]).2 = 1 ∧
      cRuleScopedSourceWorkQueueStep .leaveInert [second, fact "middle"] ≠ none ∧
      cRuleScopedSourceWorkQueueStep .leaveInert [fact "done"] = none := by decide

/-- Running the original input again recreates its first firing; it does not
advance the suspended frontier. -/
theorem restart_is_not_resume :
    (cRuleScopedSourceWorkQueueRunN .leaveInert 1 initial).1 ≠
      (cRuleScopedSourceWorkQueueRunN .leaveInert 1 [second, fact "middle"]).1 := by decide

end Controls

/-! ### Optional gate before a raw consume step removes its selected exec

The ordinary machine stays the pre-existing `cRuleScopedSourceWorkQueueStep`.
This runner is the optional check in front of the consume step only.
Authorization is `inspectionGate`'s first match. A refusal, breakpoint, or
incomplete inspection retains the selected raw directive and the restored
logical read, and does not call the step. The same directive resumes only
when that restored read is still the current restored read. A permitted step
is the direct consume operation.

`activationGate` applies `inspectionGate` to `activationRead` and the
selected `RawExecFact`. The adapter has no producer configuration. No diary
is stored here; `pauseOnGate`'s history option remains the generic schedule
diary and is not consulted by `machine`. Transaction publication
(`ProgrammableSpaceMM2.Advance` and its resumable cursor) is a different
contract: this result is a workspace, not a committed receipt. Native
currentness is the live `SpaceReadToken`. Equality of restored reads is not
that token check.
-/

section ActivationGate

open WQComputable
open Mettapedia.Machines.Cursor.ProducerOccurrenceLog
open Mettapedia.Machines.Cursor.ProducerOccurrenceLog.Accounting

/-- Restored logical read consulted before removal: erase the selected shell,
then put that representative back. This is not the native live
`SpaceReadToken`, and no currentness equivalence with that token is proved.
The live workspace is unchanged until a permitted step. -/
def activationRead (space : List Atom) (directive : RawExecFact) : List Atom :=
  morkInsertSupport (morkEraseSupport space directive.atom) directive.atom

private theorem dropLast_append_singleton :
    ∀ (xs : List Atom) (atom : Atom), (xs ++ [atom]).dropLast = xs
  | [], _ => rfl
  | [_], _ => rfl
  | head :: middle :: rest, atom => by
      have reduced :
          ((head :: middle :: rest) ++ [atom]).dropLast =
            head :: ((middle :: rest) ++ [atom]).dropLast := by
        rfl
      rw [reduced, dropLast_append_singleton (middle :: rest) atom]

private theorem erasure_eq_of_activationRead
    {space other : List Atom} {raw : RawExecFact}
    (same : activationRead space raw = activationRead other raw) :
    morkEraseSupport space raw.atom = morkEraseSupport other raw.atom := by
  have left : morkEraseSupport space raw.atom = (activationRead space raw).dropLast := by
    unfold activationRead
    rw [morkInsertSupport_morkEraseSupport_self, dropLast_append_singleton]
  have right : morkEraseSupport other raw.atom = (activationRead other raw).dropLast := by
    unfold activationRead
    rw [morkInsertSupport_morkEraseSupport_self, dropLast_append_singleton]
  rw [left, right, same]

private theorem decodeSupportedSourceExec_atom
    {raw : RawExecFact} {directive : SourceExecFact}
    (decoded : decodeSupportedSourceExec raw = some directive) :
    directive.atom = raw.atom := by
  unfold decodeSupportedSourceExec at decoded
  cases inputParsed : parseSupportedInput raw.inputExpr with
  | none => simp [inputParsed] at decoded
  | some input =>
      simp only [inputParsed] at decoded
      cases templateParsed : parseSupportedTemplate raw.templateExpr with
      | none => simp [templateParsed] at decoded
      | some template =>
          simp [templateParsed] at decoded
          subst decoded
          rfl

private theorem fire_eq_of_same_erasure
    (space other : List Atom) (directive : SourceExecFact)
    (same : morkEraseSupport space directive.atom = morkEraseSupport other directive.atom) :
    cFireRuleScopedSourceExecFact space directive =
      cFireRuleScopedSourceExecFact other directive := by
  unfold cFireRuleScopedSourceExecFact
  rw [same]

private theorem consume_step_supported
    (space : List Atom) (raw : RawExecFact) (directive : SourceExecFact)
    (selected : selectNextScheduled (cRawExecFacts space) = some raw)
    (decoded : decodeSupportedSourceExec raw = some directive) :
    cRuleScopedSourceWorkQueueStep .consume space =
      some (cFireRuleScopedSourceExecFact space directive) := by
  simp only [cRuleScopedSourceWorkQueueStep, selected, decoded]

private theorem consume_step_unsupported
    (space : List Atom) (raw : RawExecFact)
    (selected : selectNextScheduled (cRawExecFacts space) = some raw)
    (unsupported : decodeSupportedSourceExec raw = none) :
    cRuleScopedSourceWorkQueueStep .consume space =
      some (morkEraseSupport space raw.atom) := by
  simp only [cRuleScopedSourceWorkQueueStep, selected, unsupported]

private theorem consume_step_some (space : List Atom) (raw : RawExecFact)
    (selected : selectNextScheduled (cRawExecFacts space) = some raw) :
    (cRuleScopedSourceWorkQueueStep .consume space).isSome = true := by
  cases decoded : decodeSupportedSourceExec raw with
  | some directive =>
      simp only [consume_step_supported space raw directive selected decoded]
      rfl
  | none =>
      simp only [consume_step_unsupported space raw selected decoded]
      rfl

/-- Why a selected exec was not removed. These are the three non-permit
answers of `OperationGate`, under the same names as `ActionStop`. -/
inductive ActivationHold where
  | refused
  | breakpoint
  | incomplete
  deriving DecidableEq

/-- Directive, source read, and live workspace retained because the gate did
not permit removal. -/
structure HeldActivation where
  stop : ActivationHold
  directive : RawExecFact
  read : List Atom
  space : List Atom

/-- One optional consume check. `advanced` is only the direct step's
workspace. There is no diary field. -/
inductive ControlledActivation where
  | quiescent (space : List Atom)
  | held (held : HeldActivation)
  | advanced (space : List Atom)

/-- `inspectionGate` on the restored logical read and the selected raw exec. -/
def activationGate
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (space : List Atom) (directive : RawExecFact) : OperationGate :=
  inspectionGate authorized inspect (activationRead space directive) directive

theorem activation_authorization_precedes_inspection
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (space : List Atom) (directive : RawExecFact)
    (denied : authorized (activationRead space directive) directive = false) :
    activationGate authorized inspect space directive = .refuse := by
  unfold activationGate inspectionGate
  rw [denied]

theorem activation_stop_of_matched
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (space : List Atom) (directive : RawExecFact)
    (allowed : authorized (activationRead space directive) directive = true)
    (hit : inspect (activationRead space directive) directive = .matched) :
    activationGate authorized inspect space directive = .stopBefore := by
  unfold activationGate inspectionGate
  rw [allowed, hit]

theorem activation_incomplete_of_inspection
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (space : List Atom) (directive : RawExecFact)
    (allowed : authorized (activationRead space directive) directive = true)
    (pending : inspect (activationRead space directive) directive = .incomplete) :
    activationGate authorized inspect space directive = .incomplete := by
  unfold activationGate inspectionGate
  rw [allowed, pending]

theorem activation_permit_of_refuted
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (space : List Atom) (directive : RawExecFact)
    (allowed : authorized (activationRead space directive) directive = true)
    (pass : inspect (activationRead space directive) directive = .refuted) :
    activationGate authorized inspect space directive = .permit := by
  unfold activationGate inspectionGate
  rw [allowed, pass]

/-- Select the raw shell with the existing consume scheduler, then either
retain it or run `cRuleScopedSourceWorkQueueStep .consume`. -/
def controlledActivation
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (space : List Atom) : ControlledActivation :=
  match selectNextScheduled (cRawExecFacts space) with
  | none => .quiescent space
  | some raw =>
      match activationGate authorized inspect space raw with
      | .permit =>
          match cRuleScopedSourceWorkQueueStep .consume space with
          | some next => .advanced next
          | none => .quiescent space
      | .refuse => .held ⟨.refused, raw, activationRead space raw, space⟩
      | .stopBefore => .held ⟨.breakpoint, raw, activationRead space raw, space⟩
      | .incomplete => .held ⟨.incomplete, raw, activationRead space raw, space⟩

theorem nothing_selected_is_direct
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (space : List Atom)
    (noneSelected : selectNextScheduled (cRawExecFacts space) = none) :
    controlledActivation authorized inspect space = .quiescent space ∧
      cRuleScopedSourceWorkQueueStep .consume space = none := by
  refine ⟨?_, ?_⟩
  · unfold controlledActivation
    rw [noneSelected]
  · unfold cRuleScopedSourceWorkQueueStep
    rw [noneSelected]

theorem blocked_activation_retains_directive_and_read
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (space : List Atom) (raw : RawExecFact)
    (selected : selectNextScheduled (cRawExecFacts space) = some raw)
    (decision : OperationGate)
    (gate : activationGate authorized inspect space raw = decision) :
    (decision = .refuse →
        controlledActivation authorized inspect space =
          .held ⟨.refused, raw, activationRead space raw, space⟩) ∧
      (decision = .stopBefore →
        controlledActivation authorized inspect space =
          .held ⟨.breakpoint, raw, activationRead space raw, space⟩) ∧
      (decision = .incomplete →
        controlledActivation authorized inspect space =
          .held ⟨.incomplete, raw, activationRead space raw, space⟩) := by
  refine ⟨?_, ?_, ?_⟩
  · intro isRefuse
    simp only [controlledActivation, selected, gate, isRefuse]
  · intro isStop
    simp only [controlledActivation, selected, gate, isStop]
  · intro isIncomplete
    simp only [controlledActivation, selected, gate, isIncomplete]

theorem permitted_activation_erases_to_direct
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (space : List Atom) (raw : RawExecFact)
    (selected : selectNextScheduled (cRawExecFacts space) = some raw)
    (pass : activationGate authorized inspect space raw = .permit) :
    ∃ next, controlledActivation authorized inspect space = .advanced next ∧
      cRuleScopedSourceWorkQueueStep .consume space = some next := by
  have stepSome := consume_step_some space raw selected
  cases nextEq : cRuleScopedSourceWorkQueueStep .consume space with
  | none =>
      simp only [nextEq] at stepSome
      cases stepSome
  | some next =>
      refine ⟨next, ?_, rfl⟩
      simp only [controlledActivation, selected, pass, nextEq]

theorem ordinary_refuted_erases_to_direct
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (space : List Atom) (raw : RawExecFact)
    (selected : selectNextScheduled (cRawExecFacts space) = some raw)
    (allowed : authorized (activationRead space raw) raw = true)
    (pass : inspect (activationRead space raw) raw = .refuted) :
    ∃ next, controlledActivation authorized inspect space = .advanced next ∧
      cRuleScopedSourceWorkQueueStep .consume space = some next :=
  permitted_activation_erases_to_direct authorized inspect space raw selected
    (activation_permit_of_refuted authorized inspect space raw allowed pass)

theorem equal_read_same_consume_step
    (space other : List Atom) (raw : RawExecFact)
    (selectedSpace : selectNextScheduled (cRawExecFacts space) = some raw)
    (selectedOther : selectNextScheduled (cRawExecFacts other) = some raw)
    (sameRead : activationRead space raw = activationRead other raw) :
    cRuleScopedSourceWorkQueueStep .consume space =
      cRuleScopedSourceWorkQueueStep .consume other := by
  have erased := erasure_eq_of_activationRead sameRead
  cases decoded : decodeSupportedSourceExec raw with
  | none =>
      rw [consume_step_unsupported space raw selectedSpace decoded,
        consume_step_unsupported other raw selectedOther decoded, erased]
  | some directive =>
      have atomEq : directive.atom = raw.atom := decodeSupportedSourceExec_atom decoded
      have erasedDirective :
          morkEraseSupport space directive.atom = morkEraseSupport other directive.atom := by
        rw [atomEq, erased]
      rw [consume_step_supported space raw directive selectedSpace decoded,
        consume_step_supported other raw directive selectedOther decoded,
        fire_eq_of_same_erasure space other directive erasedDirective]

/-- Resuming the retained directive. `changed` performs no consume step. -/
inductive ResumedActivation where
  | sameOwner (step : ControlledActivation)
  | changed (space : List Atom)

def resumeActivation
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (held : HeldActivation) (current : List Atom) : ResumedActivation :=
  if selectNextScheduled (cRawExecFacts current) = some held.directive ∧
      activationRead current held.directive = held.read then
    .sameOwner (controlledActivation authorized inspect current)
  else
    .changed current

theorem resume_same_owner_iff
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (held : HeldActivation) (current : List Atom) :
    (∃ step, resumeActivation authorized inspect held current = .sameOwner step) ↔
      selectNextScheduled (cRawExecFacts current) = some held.directive ∧
        activationRead current held.directive = held.read := by
  unfold resumeActivation
  split
  · next cond =>
      exact ⟨fun _ => cond, fun _ => ⟨controlledActivation authorized inspect current, rfl⟩⟩
  · next absent =>
      constructor
      · intro ⟨_, same⟩
        cases same
      · intro cond
        exact absurd cond absent

theorem changed_source_does_not_resume
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (held : HeldActivation) (current : List Atom)
    (changed : activationRead current held.directive ≠ held.read) :
    resumeActivation authorized inspect held current = .changed current := by
  unfold resumeActivation
  split
  · next cond => exact absurd cond.2 changed
  · rfl

theorem different_owner_does_not_resume
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (held : HeldActivation) (current : List Atom)
    (other : selectNextScheduled (cRawExecFacts current) ≠ some held.directive) :
    resumeActivation authorized inspect held current = .changed current := by
  unfold resumeActivation
  split
  · next cond => exact absurd cond.1 other
  · rfl

theorem exact_current_permitted_resume
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (held : HeldActivation) (current : List Atom)
    (retained : activationRead held.space held.directive = held.read)
    (originalSelected :
      selectNextScheduled (cRawExecFacts held.space) = some held.directive)
    (selected : selectNextScheduled (cRawExecFacts current) = some held.directive)
    (currentRead : activationRead current held.directive = held.read)
    (pass : activationGate authorized inspect current held.directive = .permit) :
    ∃ next,
      resumeActivation authorized inspect held current = .sameOwner (.advanced next) ∧
        cRuleScopedSourceWorkQueueStep .consume current = some next ∧
        cRuleScopedSourceWorkQueueStep .consume held.space = some next := by
  obtain ⟨next, controlled, stepped⟩ :=
    permitted_activation_erases_to_direct authorized inspect current held.directive selected pass
  have sameRead : activationRead held.space held.directive = activationRead current held.directive :=
    retained.trans currentRead.symm
  have original := equal_read_same_consume_step held.space current held.directive
    originalSelected selected sameRead
  refine ⟨next, ?_, stepped, original.trans stepped⟩
  unfold resumeActivation
  rw [if_pos ⟨selected, currentRead⟩, controlled]

theorem exact_current_stop_retains
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (held : HeldActivation) (current : List Atom)
    (selected : selectNextScheduled (cRawExecFacts current) = some held.directive)
    (currentRead : activationRead current held.directive = held.read)
    (hit : activationGate authorized inspect current held.directive = .stopBefore) :
    resumeActivation authorized inspect held current =
      .sameOwner (.held {
        stop := .breakpoint
        directive := held.directive
        read := held.read
        space := current }) := by
  have retained :=
    (blocked_activation_retains_directive_and_read authorized inspect current held.directive
      selected .stopBefore hit).2.1 rfl
  rw [currentRead] at retained
  unfold resumeActivation
  rw [if_pos ⟨selected, currentRead⟩, retained]

#print axioms activation_authorization_precedes_inspection
#print axioms blocked_activation_retains_directive_and_read
#print axioms permitted_activation_erases_to_direct
#print axioms ordinary_refuted_erases_to_direct
#print axioms equal_read_same_consume_step
#print axioms resume_same_owner_iff
#print axioms changed_source_does_not_resume
#print axioms different_owner_does_not_resume
#print axioms exact_current_permitted_resume
#print axioms exact_current_stop_retains

end ActivationGate

end Mettapedia.Languages.ProcessCalculi.MORK.MM2ResumableExecution
