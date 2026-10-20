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

/-- The selected raw operation depends on its restored logical source
read; it does not select another shell while resuming this one. -/
theorem equal_read_same_selected_consume
    (space other : List Atom) (raw : RawExecFact)
    (sameRead : activationRead space raw = activationRead other raw) :
    cConsumeRuleScopedRawExecFact space raw = cConsumeRuleScopedRawExecFact other raw := by
  have erased := erasure_eq_of_activationRead sameRead
  cases decoded : decodeSupportedSourceExec raw with
  | none => simp only [cConsumeRuleScopedRawExecFact, decoded, erased]
  | some directive =>
      have atomEq : directive.atom = raw.atom := decodeSupportedSourceExec_atom decoded
      have same : morkEraseSupport space directive.atom = morkEraseSupport other directive.atom := by
        rw [atomEq, erased]
      simp only [cConsumeRuleScopedRawExecFact, decoded, fire_eq_of_same_erasure space other directive same]

private theorem consume_step_supported
    (space : List Atom) (raw : RawExecFact) (directive : SourceExecFact)
    (selected : selectNextScheduled (cRawExecFacts space) = some raw)
    (decoded : decodeSupportedSourceExec raw = some directive) :
    cRuleScopedSourceWorkQueueStep .consume space =
      some (cFireRuleScopedSourceExecFact space directive) := by
  simp only [cRuleScopedSourceWorkQueueStep, cConsumeRuleScopedRawExecFact, selected, decoded]

private theorem consume_step_unsupported
    (space : List Atom) (raw : RawExecFact)
    (selected : selectNextScheduled (cRawExecFacts space) = some raw)
    (unsupported : decodeSupportedSourceExec raw = none) :
    cRuleScopedSourceWorkQueueStep .consume space =
      some (morkEraseSupport space raw.atom) := by
  simp only [cRuleScopedSourceWorkQueueStep, cConsumeRuleScopedRawExecFact, selected, unsupported]

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

/-- Gate one supplied raw shell before the existing consume operation.
The programmable entry below additionally checks current source membership. -/
private def gatedRawActivation
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (space : List Atom) (raw : RawExecFact) : ControlledActivation :=
  match activationGate authorized inspect space raw with
  | .permit =>
      match cConsumeRuleScopedRawExecFact space raw with
      | some next => .advanced next
      | none => .quiescent space
  | .refuse => .held ⟨.refused, raw, activationRead space raw, space⟩
  | .stopBefore => .held ⟨.breakpoint, raw, activationRead space raw, space⟩
  | .incomplete => .held ⟨.incomplete, raw, activationRead space raw, space⟩

/-- The default least-key strategy applied to the selected raw operation. -/
def controlledActivation
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (space : List Atom) : ControlledActivation :=
  match selectNextScheduled (cRawExecFacts space) with
  | none => .quiescent space
  | some raw => gatedRawActivation authorized inspect space raw

/-- Factoring selected execution preserves the preceding default operation
exactly; programmable selection does not replace its least-key strategy. -/
theorem controlledActivation_default_preserved
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (space : List Atom) :
    controlledActivation authorized inspect space =
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
          | .incomplete => .held ⟨.incomplete, raw, activationRead space raw, space⟩ := by
  cases selected : selectNextScheduled (cRawExecFacts space) with
  | none => simp only [controlledActivation, selected]
  | some raw =>
      simp only [controlledActivation, selected, gatedRawActivation,
        cRuleScopedSourceWorkQueueStep]

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
    simp only [controlledActivation, gatedRawActivation, selected, gate, isRefuse]
  · intro isStop
    simp only [controlledActivation, gatedRawActivation, selected, gate, isStop]
  · intro isIncomplete
    simp only [controlledActivation, gatedRawActivation, selected, gate, isIncomplete]

theorem permitted_activation_erases_to_direct
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (space : List Atom) (raw : RawExecFact)
    (selected : selectNextScheduled (cRawExecFacts space) = some raw)
    (pass : activationGate authorized inspect space raw = .permit) :
    ∃ next, controlledActivation authorized inspect space = .advanced next ∧
      cRuleScopedSourceWorkQueueStep .consume space = some next := by
  have stepSome := cConsumeRuleScopedRawExecFact_isSome space raw
  cases nextEq : cConsumeRuleScopedRawExecFact space raw with
  | none => simp [nextEq] at stepSome
  | some next =>
      refine ⟨next, ?_, ?_⟩
      · simp only [controlledActivation, gatedRawActivation, selected, pass, nextEq]
      · simpa only [cRuleScopedSourceWorkQueueStep, selected] using nextEq

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


/-- A raw activation view is the existing shell extraction, before matching
inputs or instantiating outputs. Discovery returns the unchanged workspace. -/
def discoverActivations (space : List Atom) : List RawExecFact × List Atom :=
  (cRawExecFacts space, space)

theorem discovery_preserves_source (space : List Atom) :
    (discoverActivations space).2 = space := rfl

/-- A discovered choice names its exact authored shell and extracted fields.
Physical support multiplicity is not represented by this set-support profile. -/
theorem discovered_activation_identity (space : List Atom) (raw : RawExecFact)
    (member : raw ∈ (discoverActivations space).1) :
    raw.atom ∈ space ∧ extractRawExecFact raw.atom = some raw := by
  obtain ⟨atom, present, extracted⟩ := List.mem_filterMap.mp member
  have same := extractRawExecFact_atom_eq extracted
  rw [same]
  exact ⟨present, extracted⟩

/-- Capture a discovered raw choice in the existing retained-read state.
Inspection remains pending. This neither consumes the shell nor creates an
exclusive capability from the copied source evidence. -/
def captureSelectedRaw (space : List Atom) (raw : RawExecFact) : Option HeldActivation :=
  if raw ∈ cRawExecFacts space then
    some ⟨.incomplete, raw, activationRead space raw, space⟩
  else none

theorem captured_selection_identity (space : List Atom) (raw : RawExecFact)
    (held : HeldActivation) (captured : captureSelectedRaw space raw = some held) :
    raw ∈ cRawExecFacts space ∧ held.directive = raw ∧ held.read = activationRead space raw ∧ held.space = space := by
  unfold captureSelectedRaw at captured
  split at captured
  · next live =>
      cases captured
      exact ⟨live, rfl, rfl, rfl⟩
  · cases captured

/-- Explicit selection admits only an actual current raw source occurrence.
A missing or forged shell is a changed source, not a substitute directive. -/
def activateSelectedRaw
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (space : List Atom) (raw : RawExecFact) : ResumedActivation :=
  if raw ∈ cRawExecFacts space then
    .sameOwner (gatedRawActivation authorized inspect space raw)
  else .changed space

theorem selected_absent_keeps_source
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (space : List Atom) (raw : RawExecFact) (absent : raw ∉ cRawExecFacts space) :
    activateSelectedRaw authorized inspect space raw = .changed space := by
  simp [activateSelectedRaw, absent]

theorem selected_default_strategy
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (space : List Atom) (raw : RawExecFact)
    (least : selectNextScheduled (cRawExecFacts space) = some raw) :
    activateSelectedRaw authorized inspect space raw = .sameOwner (controlledActivation authorized inspect space) := by
  simp only [activateSelectedRaw, if_pos (selectNextScheduled_mem least), controlledActivation, least]

/-- An admitted result has a real current source shell, the current permit,
and exactly the selected consume transition. No least-key premise is needed. -/
theorem selected_advanced_origin
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (space : List Atom) (raw : RawExecFact) (next : List Atom)
    (advanced : activateSelectedRaw authorized inspect space raw = .sameOwner (.advanced next)) :
    raw ∈ cRawExecFacts space ∧ activationGate authorized inspect space raw = .permit ∧
      cConsumeRuleScopedRawExecFact space raw = some next := by
  unfold activateSelectedRaw at advanced
  split at advanced
  · next live =>
      unfold gatedRawActivation at advanced
      cases gate : activationGate authorized inspect space raw <;> rw [gate] at advanced
      · cases moved : cConsumeRuleScopedRawExecFact space raw with
        | none => simp [moved] at advanced
        | some target =>
            simp only [moved] at advanced
            cases advanced
            exact ⟨live, rfl, rfl⟩
      all_goals cases advanced
  · cases advanced

theorem selected_permitted_exact
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (space : List Atom) (raw : RawExecFact)
    (live : raw ∈ cRawExecFacts space)
    (pass : activationGate authorized inspect space raw = .permit) :
    ∃ next, activateSelectedRaw authorized inspect space raw = .sameOwner (.advanced next) ∧
      cConsumeRuleScopedRawExecFact space raw = some next := by
  have possible := cConsumeRuleScopedRawExecFact_isSome space raw
  cases moved : cConsumeRuleScopedRawExecFact space raw with
  | none => simp [moved] at possible
  | some next =>
      exact ⟨next, by simp only [activateSelectedRaw, if_pos live, gatedRawActivation, pass, moved], rfl⟩

theorem selected_nonpermit_keeps_source
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (space : List Atom) (raw : RawExecFact) (live : raw ∈ cRawExecFacts space) :
    (activationGate authorized inspect space raw = .refuse →
      activateSelectedRaw authorized inspect space raw = .sameOwner (.held ⟨.refused, raw, activationRead space raw, space⟩)) ∧
    (activationGate authorized inspect space raw = .stopBefore →
      activateSelectedRaw authorized inspect space raw = .sameOwner (.held ⟨.breakpoint, raw, activationRead space raw, space⟩)) ∧
    (activationGate authorized inspect space raw = .incomplete →
      activateSelectedRaw authorized inspect space raw = .sameOwner (.held ⟨.incomplete, raw, activationRead space raw, space⟩)) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro decision <;>
    simp only [activateSelectedRaw, if_pos live, gatedRawActivation, decision]

/-- A retained programmable choice resumes itself, not the default strategy.
Restored logical read equality is weaker than native live-token currency. -/
def resumeSelectedRaw
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (held : HeldActivation) (current : List Atom) : ResumedActivation :=
  if activationRead current held.directive = held.read then
    activateSelectedRaw authorized inspect current held.directive
  else .changed current

theorem selected_resume_current_iff
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (held : HeldActivation) (current : List Atom) :
    (∃ result, resumeSelectedRaw authorized inspect held current = .sameOwner result) ↔
      held.directive ∈ cRawExecFacts current ∧ activationRead current held.directive = held.read := by
  by_cases same : activationRead current held.directive = held.read
  · by_cases live : held.directive ∈ cRawExecFacts current
    · simp [resumeSelectedRaw, same, activateSelectedRaw, live]
    · simp [resumeSelectedRaw, same, activateSelectedRaw, live]
  · simp [resumeSelectedRaw, same]

theorem selected_stale_keeps_source
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (held : HeldActivation) (current : List Atom)
    (changed : activationRead current held.directive ≠ held.read) :
    resumeSelectedRaw authorized inspect held current = .changed current := by
  simp only [resumeSelectedRaw, if_neg changed]

/-- Exact execution of the retained chosen shell under a current permit.
The complete result is the existing consume operation in both logical reads. -/
theorem selected_resume_exact
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (held : HeldActivation) (current : List Atom)
    (retained : activationRead held.space held.directive = held.read)
    (live : held.directive ∈ cRawExecFacts current)
    (currentRead : activationRead current held.directive = held.read)
    (pass : activationGate authorized inspect current held.directive = .permit) :
    ∃ next, resumeSelectedRaw authorized inspect held current = .sameOwner (.advanced next) ∧
      cConsumeRuleScopedRawExecFact current held.directive = some next ∧
      cConsumeRuleScopedRawExecFact held.space held.directive = some next := by
  obtain ⟨next, activated, actual⟩ := selected_permitted_exact authorized inspect current held.directive live pass
  exact ⟨next, by simpa only [resumeSelectedRaw, if_pos currentRead] using activated, actual,
    (equal_read_same_selected_consume held.space current held.directive (retained.trans currentRead.symm)).trans actual⟩

/-- The first perform and every retry use the same captured-source validator.
A current authorization grant executes the captured choice, even when another
raw directive has the least key. -/
theorem captured_selection_permitted
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (source current : List Atom) (raw : RawExecFact) (held : HeldActivation)
    (captured : captureSelectedRaw source raw = some held)
    (live : raw ∈ cRawExecFacts current)
    (currentRead : activationRead current raw = activationRead source raw)
    (pass : activationGate authorized inspect current raw = .permit) :
    ∃ next, resumeSelectedRaw authorized inspect held current = .sameOwner (.advanced next) ∧
      cConsumeRuleScopedRawExecFact current raw = some next ∧
      cConsumeRuleScopedRawExecFact source raw = some next := by
  unfold captureSelectedRaw at captured
  split at captured
  · cases captured
    exact selected_resume_exact authorized inspect _ current rfl live currentRead pass
  · cases captured

/-- A supported chosen rule removes its shell before matching on the restored
read, then applies exactly the authored sink batch to that live remainder. -/
theorem selected_supported_exact_remainder
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (space : List Atom) (raw : RawExecFact) (directive : SourceExecFact)
    (live : raw ∈ cRawExecFacts space)
    (pass : activationGate authorized inspect space raw = .permit)
    (decoded : decodeSupportedSourceExec raw = some directive) :
    activateSelectedRaw authorized inspect space raw =
      .sameOwner (.advanced (cFireRuleScopedSourceExecFact space directive)) := by
  simp only [activateSelectedRaw, if_pos live, gatedRawActivation, pass,
    cConsumeRuleScopedRawExecFact_supported space raw directive decoded]

/-- A failed match still consumes the selected shell, leaving exactly the
ordered support remainder; it does not select another raw instruction. -/
theorem selected_no_matches_exact_remainder
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (space : List Atom) (raw : RawExecFact) (directive : SourceExecFact)
    (live : raw ∈ cRawExecFacts space)
    (pass : activationGate authorized inspect space raw = .permit)
    (decoded : decodeSupportedSourceExec raw = some directive)
    (noMatches :
      (cMatchInputSpecMork [] (activationRead space raw) directive.rule.input).filter
        (fun (substitution, _) => matchSourceGuards substitution directive.rule.guards) = []) :
    activateSelectedRaw authorized inspect space raw = .sameOwner (.advanced (morkEraseSupport space raw.atom)) := by
  have same := decodeSupportedSourceExec_atom decoded
  rw [selected_supported_exact_remainder authorized inspect space raw directive live pass decoded,
    cFireRuleScopedSourceExecFact_eq_erase_of_no_matches space directive
      (by simpa only [same, activationRead] using noMatches), same]

open Mettapedia.GSLT.Core.InferenceControl.Recording

private def observeActivationResult (history : Option (Prefix RawExecFact))
    (raw : RawExecFact) (result : ResumedActivation) : Option (Prefix RawExecFact) × ResumedActivation :=
  match history with
  | none => (none, result)
  | some record =>
      match result with
      | .sameOwner (.advanced _) => (some (record.push (fun _ => raw)), result)
      | _ => (some record, result)

/-- Optional observation of the actual permitted operation. The disabled
entry calls that same operation directly. Held choices request no record. -/
def observeSelectedRaw (history : Option (Prefix RawExecFact))
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (space : List Atom) (raw : RawExecFact) : Option (Prefix RawExecFact) × ResumedActivation :=
  observeActivationResult history raw (activateSelectedRaw authorized inspect space raw)

/-- The same optional Prefix hook observes a captured choice's actual resume,
including its first perform. Changed source and held gates request no record. -/
def observeResumeSelectedRaw (history : Option (Prefix RawExecFact))
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (held : HeldActivation) (current : List Atom) : Option (Prefix RawExecFact) × ResumedActivation :=
  observeActivationResult history held.directive (resumeSelectedRaw authorized inspect held current)

theorem observed_selected_plain
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (space : List Atom) (raw : RawExecFact) :
    observeSelectedRaw none authorized inspect space raw =
      (none, activateSelectedRaw authorized inspect space raw) := rfl

theorem observed_selected_erasure (history : Option (Prefix RawExecFact))
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (space : List Atom) (raw : RawExecFact) :
    (observeSelectedRaw history authorized inspect space raw).2 = activateSelectedRaw authorized inspect space raw := by
  cases history with
  | none => rfl
  | some record =>
      unfold observeSelectedRaw observeActivationResult
      cases activateSelectedRaw authorized inspect space raw with
      | changed => rfl
      | sameOwner result => cases result <;> rfl

theorem observed_selected_origin (record : Prefix RawExecFact)
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (space : List Atom) (raw : RawExecFact) (next : List Atom)
    (advanced : activateSelectedRaw authorized inspect space raw = .sameOwner (.advanced next)) :
    (observeSelectedRaw (some record) authorized inspect space raw).1 = some (record.push (fun _ => raw)) ∧
      raw.atom ∈ space ∧ extractRawExecFact raw.atom = some raw := by
  have actual := selected_advanced_origin authorized inspect space raw next advanced
  exact ⟨by simp only [observeSelectedRaw, observeActivationResult, advanced],
    discovered_activation_identity space raw actual.1⟩

theorem observed_selected_nonpermit (record : Prefix RawExecFact)
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (space : List Atom) (raw : RawExecFact)
    (blocked : activationGate authorized inspect space raw ≠ .permit) :
    (observeSelectedRaw (some record) authorized inspect space raw).1 = some record := by
  by_cases live : raw ∈ cRawExecFacts space
  · cases gate : activationGate authorized inspect space raw <;>
      simp [observeSelectedRaw, observeActivationResult, activateSelectedRaw, gatedRawActivation, live, gate] at blocked ⊢
  · simp [observeSelectedRaw, observeActivationResult, activateSelectedRaw, live]

theorem observed_resume_erasure (history : Option (Prefix RawExecFact))
    (authorized : List Atom → RawExecFact → Bool)
    (inspect : List Atom → RawExecFact → GuardInspection)
    (held : HeldActivation) (current : List Atom) :
    (observeResumeSelectedRaw history authorized inspect held current).2 = resumeSelectedRaw authorized inspect held current := by
  cases history with
  | none => rfl
  | some record =>
      unfold observeResumeSelectedRaw observeActivationResult
      cases resumeSelectedRaw authorized inspect held current with
      | changed => rfl
      | sameOwner result => cases result <;> rfl

#print axioms captured_selection_identity
#print axioms captured_selection_permitted
#print axioms observed_resume_erasure
#print axioms controlledActivation_default_preserved
#print axioms equal_read_same_selected_consume
#print axioms selected_no_matches_exact_remainder
#print axioms observed_selected_nonpermit
#print axioms discovered_activation_identity
#print axioms selected_default_strategy
#print axioms selected_advanced_origin
#print axioms selected_permitted_exact
#print axioms selected_nonpermit_keeps_source
#print axioms selected_resume_current_iff
#print axioms selected_stale_keeps_source
#print axioms selected_resume_exact
#print axioms selected_supported_exact_remainder
#print axioms observed_selected_plain
#print axioms observed_selected_erasure
#print axioms observed_selected_origin


namespace ProgrammableControls

open Mettapedia.GSLT.Core.InferenceControl.Recording

private def rawRule (priority label input output : String) : RawExecFact :=
  ⟨Controls.rule priority label input output,
    .expression [.symbol priority, .symbol label],
    .expression [.symbol ",", Controls.fact input],
    .expression [.symbol "O", .expression [.symbol "-", Controls.fact input],
      .expression [.symbol "+", Controls.fact output]]⟩

def least := rawRule "0" "least" "start" "default"
def chosen := rawRule "1" "chosen" "start" "selected"
def source : List Atom := [least.atom, chosen.atom, Controls.fact "start"]
def remainder : List Atom := [least.atom, Controls.fact "selected"]

def allow (_ : List Atom) (_ : RawExecFact) : Bool := true
def deny (_ : List Atom) (_ : RawExecFact) : Bool := false
def pass (_ : List Atom) (_ : RawExecFact) : GuardInspection := .refuted
def stop (_ : List Atom) (_ : RawExecFact) : GuardInspection := .matched

def held : HeldActivation := ⟨.breakpoint, chosen, activationRead source chosen, source⟩

/-- Programming the nonleast choice changes the trace, while ordinary source
execution continues from its actual remainder without restoring that shell. -/
theorem nonleast_selection_and_ordinary_remainder :
    discoverActivations source = ([least, chosen], source) ∧
      selectNextScheduled (cRawExecFacts source) = some least ∧
      activateSelectedRaw allow pass source chosen = .sameOwner (.advanced remainder) ∧
      cRuleScopedSourceWorkQueueRunN .consume 10 remainder = ([Controls.fact "selected"], 1) ∧
      cRuleScopedSourceWorkQueueRunN .consume 10 source = ([Controls.fact "default"], 2) := by
  exact ⟨rfl, by decide, rfl, by decide, by decide⟩

def changed := source ++ [Controls.fact "edit"]
def forged := { chosen with inputExpr := .symbol "forged-input" }

/-- Stop and refusal retain the chosen instruction. Current permission is
consulted on retry; a changed read or forged source selection cannot execute. -/
theorem retained_choice_refusal_and_stale_source :
    activateSelectedRaw allow stop source chosen = .sameOwner (.held held) ∧
      resumeSelectedRaw allow stop held source = .sameOwner (.held held) ∧
      resumeSelectedRaw deny pass held source = .sameOwner (.held ⟨.refused, chosen, held.read, source⟩) ∧
      resumeSelectedRaw allow pass held source = .sameOwner (.advanced remainder) ∧
      resumeSelectedRaw allow pass held changed = .changed changed ∧
      activateSelectedRaw allow pass source forged = .changed source ∧
      activateSelectedRaw allow pass [] chosen = .changed [] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def alien : RawExecFact :=
  ⟨.expression [.symbol "exec", .symbol "alien", .symbol "input", .symbol "output"],
    .symbol "alien", .symbol "input", .symbol "output"⟩

/-- Raw discovery does not require interpreted input or output. Consuming an
unsupported shell removes that shell by the existing support-key contract. -/
theorem unsupported_shell_is_a_real_unprepared_activation :
    discoverActivations [least.atom, alien.atom, Controls.fact "start"] =
      ([least, alien], [least.atom, alien.atom, Controls.fact "start"]) ∧
      decodeSupportedSourceExec alien = none ∧
      activateSelectedRaw allow pass [least.atom, alien.atom, Controls.fact "start"] alien =
        .sameOwner (.advanced [least.atom, Controls.fact "start"]) := by
  exact ⟨rfl, by decide, rfl⟩

def captured : HeldActivation := ⟨.incomplete, chosen, activationRead source chosen, source⟩

def recorded := observeSelectedRaw (some (Prefix.initial 1)) allow pass source chosen
def stopped := observeSelectedRaw (some (Prefix.initial 1)) allow stop source chosen

theorem optional_observation_and_forgetting_keep_selected_execution :
    captureSelectedRaw source chosen = some captured ∧
      (observeResumeSelectedRaw (some (Prefix.initial 1)) allow pass captured source).2 = recorded.2 ∧
      (observeResumeSelectedRaw (some (Prefix.initial 1)) allow pass captured changed).1.map Prefix.items = some [] ∧
      recorded.2 = .sameOwner (.advanced remainder) ∧ recorded.1.map Prefix.items = some [chosen] ∧
      stopped.1.map Prefix.items = some [] ∧ stopped.2 = .sameOwner (.held held) ∧
      observeSelectedRaw none allow pass source chosen = (none, recorded.2) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms nonleast_selection_and_ordinary_remainder
#print axioms retained_choice_refusal_and_stale_source
#print axioms unsupported_shell_is_a_real_unprepared_activation
#print axioms optional_observation_and_forgetting_keep_selected_execution

end ProgrammableControls

end ActivationGate

end Mettapedia.Languages.ProcessCalculi.MORK.MM2ResumableExecution
