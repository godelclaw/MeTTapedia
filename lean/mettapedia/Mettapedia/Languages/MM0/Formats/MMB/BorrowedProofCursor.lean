import Mettapedia.Languages.MM0.Formats.MMB.MachineCost
import Mettapedia.Languages.MM0.Formats.MMB.MachineControls
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.ExecutedSoundness

/-!
# Borrowing the original MMB proof-command stream

The cursor replaces the remaining proof-command list by a source address. It
retains the original allocated store, logical allocation indices, unifier and
return continuation. Command dispatch and unification call the existing MMB
operations; source materialization is used only in the comparison semantics.

Owner, source and revision coordinates are admission indices, not forge-proof
capabilities. The provider must bind them to the actual source and declaration
tables. A missing source command or mismatched scope stops without a completed
MMB verdict. This module establishes neither C ownership nor byte decoding.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Formats.MMB.BorrowedProofCursor

structure Scope where
  owner : Nat
  source : Nat
  revision : Nat
  deriving DecidableEq

structure Source where
  scope : Scope
  length : Nat
  read : Nat → Option ProofCmd

/-- The pending command list is absent. The declaration's active unification
stream is retained exactly, including its original return continuation. -/
inductive Phase where
  | commands (state : State)
  | unify (store : List Alloc) (mode : UMode) (unifier : Unifier)
      (stream : List UnifyCmd) (continuation : Continuation)
  | done (result : Option State)

structure Cursor where
  scope : Scope
  position : Nat
  phase : Phase

def Phase.withRest : Phase → List ProofCmd → Config
  | .commands state, rest => .commands state rest
  | .unify store mode unifier stream continuation, rest =>
      .unify store mode unifier stream continuation rest
  | .done result, _ => .done result

def Phase.ofConfig : Config → Phase
  | .commands state _ => .commands state
  | .unify store mode unifier stream continuation _ =>
      .unify store mode unifier stream continuation
  | .done result => .done result

def start (source : Source) (state : State) : Cursor :=
  ⟨source.scope, 0, .commands state⟩

/-- Missing source data is not an MMB rejection: no successor or completed
verdict is fabricated. Declaration microsteps never reread a proof command. -/
def next (tables : Tables) (mode : Mode) (source : Source) (cursor : Cursor) :
    Option Cursor := do
  if cursor.scope ≠ source.scope then none else
    match cursor.phase with
    | .commands state =>
        if cursor.position < source.length then do
          let command ← source.read cursor.position
          pure ⟨cursor.scope, cursor.position + 1,
            .ofConfig (startCommand tables mode state command [])⟩
        else pure ⟨cursor.scope, cursor.position, .done (some state)⟩
    | .unify store umode unifier stream continuation =>
        (MMB.next tables mode (.unify store umode unifier stream continuation [])).map
          fun config => ⟨cursor.scope, cursor.position, .ofConfig config⟩
    | .done _ => none

/-- Exact source reading, including the independently known stream endpoint.
This relation is comparison semantics and is not consulted by the worker. -/
inductive Reads (source : Source) : Nat → List ProofCmd → Prop where
  | nil {position : Nat} (ended : source.length ≤ position) : Reads source position []
  | cons {position : Nat} {command : ProofCmd} {rest : List ProofCmd}
      (beforeEnd : position < source.length) (read : source.read position = some command)
      (later : Reads source (position + 1) rest) : Reads source position (command :: rest)

/-- The relation retains the entire original MMB state; it does not quotient
allocated expressions by their printed or structural equality. -/
def Represents (source : Source) (cursor : Cursor) (config : Config) : Prop :=
  cursor.scope = source.scope ∧
    ∃ commands, Reads source cursor.position commands ∧
      cursor.phase.withRest commands = config

theorem startCommand_withRest (tables : Tables) (mode : Mode) (state : State)
    (command : ProofCmd) (rest : List ProofCmd) :
    (Phase.ofConfig (startCommand tables mode state command [])).withRest rest =
      startCommand tables mode state command rest := by
  cases command <;>
    simp only [startCommand, startThm, startUnfold]
  all_goals repeat' (split <;> simp_all [Phase.ofConfig, Phase.withRest])
  all_goals
    first
    | rename_i index _
      cases found : tables.thms[index]? with
      | none => rfl
      | some entry =>
          cases prepared : prepareThm entry state <;> simp [prepared]
    | rename_i _ e right term arguments below _
      cases found : tables.terms[term]? with
      | none => rfl
      | some entry =>
          cases value : entry.value <;> simp [value]

theorem unify_withRest (tables : Tables) (mode : Mode) (store : List Alloc)
    (umode : UMode) (unifier : Unifier) (stream : List UnifyCmd)
    (continuation : Continuation) (rest : List ProofCmd) :
    ((MMB.next tables mode (.unify store umode unifier stream continuation [])).map
      fun config => (Phase.ofConfig config).withRest rest) =
        MMB.next tables mode (.unify store umode unifier stream continuation rest) := by
  cases stream with
  | nil =>
      simp only [MMB.next]
      split <;> rfl
  | cons command stream =>
      simp only [MMB.next]
      cases unifyStep store umode unifier command <;> rfl

/-- One source-addressed microstep exists exactly when the original microstep
does, and its complete residual configuration is represented. -/
theorem next_correspondence (tables : Tables) (mode : Mode) (source : Source)
    (cursor : Cursor) (config : Config) (represented : Represents source cursor config) :
    match next tables mode source cursor, MMB.next tables mode config with
    | none, none => True
    | some after, some result => Represents source after result
    | _, _ => False := by
  obtain ⟨scope, commands, read, rfl⟩ := represented
  rcases cursor with ⟨stamp, position, phase⟩
  dsimp only at scope read ⊢
  cases phase with
  | done result => simp [next, Phase.withRest, MMB.next, scope]
  | commands state =>
      cases read with
      | nil ended =>
          simp only [next, scope, ne_eq, not_true_eq_false, ↓reduceIte]
          rw [if_neg (by omega)]
          simp only [Phase.withRest, MMB.next]
          exact ⟨rfl, [], .nil ended, rfl⟩
      | cons beforeEnd found later =>
          simp only [next, scope, ne_eq, not_true_eq_false, ↓reduceIte, beforeEnd,
            found, pure, Phase.withRest, MMB.next]
          exact ⟨rfl, _, later, startCommand_withRest tables mode state _ _⟩
  | unify store umode unifier stream continuation =>
      have compared := unify_withRest tables mode store umode unifier stream continuation commands
      simp only [next, scope, ne_eq, not_true_eq_false, ↓reduceIte]
      cases advanced : MMB.next tables mode
          (.unify store umode unifier stream continuation []) with
      | none =>
          rw [advanced, Option.map_none] at compared
          simp only [Phase.withRest, Option.map_none, ← compared]
      | some after =>
          rw [advanced, Option.map_some] at compared
          simp only [Phase.withRest, Option.map_some, ← compared]
          exact ⟨rfl, commands, read, rfl⟩

/-- A representation gives both preservation and reflection of the existence
of the next step, including a pause inside declaration unification. -/
theorem next_isSome_iff (tables : Tables) (mode : Mode) (source : Source)
    (cursor : Cursor) (config : Config) (represented : Represents source cursor config) :
    (next tables mode source cursor).isSome = (MMB.next tables mode config).isSome := by
  have compared := next_correspondence tables mode source cursor config represented
  cases cursorStep : next tables mode source cursor <;>
    cases referenceStep : MMB.next tables mode config <;>
    simp_all

theorem next_preserves (tables : Tables) (mode : Mode) (source : Source)
    (cursor after : Cursor) (config : Config)
    (represented : Represents source cursor config)
    (advanced : next tables mode source cursor = some after) :
    ∃ result, MMB.next tables mode config = some result ∧ Represents source after result := by
  have compared := next_correspondence tables mode source cursor config represented
  cases reference : MMB.next tables mode config with
  | none => simp [advanced, reference] at compared
  | some result => exact ⟨result, rfl, by simpa [advanced, reference] using compared⟩

theorem next_reflects (tables : Tables) (mode : Mode) (source : Source)
    (cursor : Cursor) (config result : Config)
    (represented : Represents source cursor config)
    (advanced : MMB.next tables mode config = some result) :
    ∃ after, next tables mode source cursor = some after ∧ Represents source after result := by
  have compared := next_correspondence tables mode source cursor config represented
  cases actual : next tables mode source cursor with
  | none => simp [actual, advanced] at compared
  | some after => exact ⟨after, rfl, by simpa [actual, advanced] using compared⟩

open Mettapedia.Machines Mettapedia.GSLT.Distinction.ProductiveBlocks

def answer (source : Source) (cursor : Cursor) : Option (Option State) :=
  if cursor.scope = source.scope then
    match cursor.phase with
    | .done result => some result
    | _ => none
  else none

abbrev answerCore (tables : Tables) (mode : Mode) (source : Source) :
    AnswerMachineCore State (Option State) where
  State := Cursor
  load := start source
  step := next tables mode source
  answer := answer source
  answer_final := by
    intro cursor result observed
    rcases cursor with ⟨scope, position, phase⟩
    cases phase <;> simp_all [answer, next]

def eventMachine (tables : Tables) (mode : Mode) (source : Source) :
    Machine Cursor (ProductiveCoreAdapters.Occurrence Cursor) (Option State) Empty :=
  ProductiveCoreAdapters.answerMachine (answerCore tables mode source)

theorem answer_correspondence (tables : Tables) (mode : Mode) (source : Source)
    (cursor : Cursor) (config : Config) (represented : Represents source cursor config) :
    answer source cursor = (MMB.answerCore tables mode).answer config := by
  obtain ⟨scope, commands, _, rfl⟩ := represented
  cases phase : cursor.phase <;> simp [answer, scope, phase, Phase.withRest, MMB.answerCore]

private theorem map_trace {Input TargetInput : Type}
    (left : MachineCore Input) (right : MachineCore TargetInput)
    (related : left.State → right.State → Prop)
    (forward : ∀ before after config, related before config → left.StepRel before after →
      ∃ result, right.StepRel config result ∧ related after result)
    {before after : left.State} {events : List (ProductiveCoreAdapters.Occurrence left.State)}
    (trace : ProductiveCoreAdapters.Trace left before events after)
    (config : right.State) (represented : related before config) :
    ∃ result referenceEvents,
      ProductiveCoreAdapters.Trace right config referenceEvents result ∧
      related after result ∧ referenceEvents.length = events.length := by
  induction trace generalizing config with
  | empty => exact ⟨config, [], .empty _, represented, rfl⟩
  | @cons before middle after events step _ ih =>
      obtain ⟨nextConfig, stepped, middleRepresents⟩ := forward before middle config represented step
      obtain ⟨result, referenceEvents, later, finalRepresents, sameLength⟩ := ih nextConfig middleRepresents
      exact ⟨result, (config, nextConfig) :: referenceEvents, .cons stepped later,
        finalRepresents, by simp [sameLength]⟩

/-- Every connected cursor history is an original MMB history of exactly the
same number of microsteps, with all allocation and continuation state intact. -/
theorem trace_preserves (tables : Tables) (mode : Mode) (source : Source)
    {cursor after : Cursor} {events : List (ProductiveCoreAdapters.Occurrence Cursor)}
    (trace : ProductiveCoreAdapters.Trace (answerCore tables mode source).toMachineCore
      cursor events after) (config : Config) (represented : Represents source cursor config) :
    ∃ result referenceEvents,
      ProductiveCoreAdapters.Trace (MMB.answerCore tables mode).toMachineCore
        config referenceEvents result ∧
      Represents source after result ∧ referenceEvents.length = events.length := by
  exact map_trace (answerCore tables mode source).toMachineCore
    (MMB.answerCore tables mode).toMachineCore (Represents source)
    (next_preserves tables mode source) trace config represented

/-- Every original MMB history has a source-addressed history with the same
microstep count. Source decoding is not substituted for execution. -/
theorem trace_reflects (tables : Tables) (mode : Mode) (source : Source)
    {config result : Config} {events : List (ProductiveCoreAdapters.Occurrence Config)}
    (trace : ProductiveCoreAdapters.Trace (MMB.answerCore tables mode).toMachineCore
      config events result) (cursor : Cursor) (represented : Represents source cursor config) :
    ∃ after cursorEvents,
      ProductiveCoreAdapters.Trace (answerCore tables mode source).toMachineCore
        cursor cursorEvents after ∧
      Represents source after result ∧ cursorEvents.length = events.length := by
  exact map_trace (MMB.answerCore tables mode).toMachineCore
    (answerCore tables mode source).toMachineCore (fun config cursor => Represents source cursor config)
    (fun config result cursor represents step =>
      next_reflects tables mode source cursor config result represents step)
    trace cursor represented

/-- Both acceptance and rejection agree with the existing retained MMB
machine. Incomplete, missing-source and exhausted executions are not verdicts. -/
theorem finished_iff (tables : Tables) (mode : Mode) (source : Source)
    (cursor : Cursor) (config : Config) (represented : Represents source cursor config)
    (result : Option State) :
    (∃ fuel events, (eventMachine tables mode source).run fuel cursor =
      (events, .finished result)) ↔
    (∃ fuel events, (MMB.eventMachine tables mode).run fuel config =
      (events, .finished result)) := by
  constructor
  · intro completed
    obtain ⟨after, reachable, observed⟩ :=
      (ProductiveCoreAdapters.answer_reachable_iff_finished
        (answerCore tables mode source) cursor result).mpr completed
    obtain ⟨events, trace⟩ := ProductiveCoreAdapters.trace_of_reachable _ reachable
    obtain ⟨resultConfig, _, referenceTrace, finalRepresents, _⟩ :=
      trace_preserves tables mode source trace config represented
    exact (ProductiveCoreAdapters.answer_reachable_iff_finished
      (MMB.answerCore tables mode) config result).mp
        ⟨resultConfig, referenceTrace.reachable _,
          (answer_correspondence tables mode source after resultConfig finalRepresents).symm.trans observed⟩
  · intro completed
    obtain ⟨resultConfig, reachable, observed⟩ :=
      (ProductiveCoreAdapters.answer_reachable_iff_finished
        (MMB.answerCore tables mode) config result).mpr completed
    obtain ⟨events, trace⟩ := ProductiveCoreAdapters.trace_of_reachable _ reachable
    obtain ⟨after, _, cursorTrace, finalRepresents, _⟩ :=
      trace_reflects tables mode source trace cursor represented
    exact (ProductiveCoreAdapters.answer_reachable_iff_finished
      (answerCore tables mode source) cursor result).mp
        ⟨after, cursorTrace.reachable _,
          (answer_correspondence tables mode source after resultConfig finalRepresents).trans observed⟩

/-- Borrowed command execution preserves and reflects the original complete
stream result, not merely existence of some derivation of its conclusion. -/
theorem finished_iff_run (tables : Tables) (mode : Mode) (source : Source)
    (state : State) (commands : List ProofCmd) (read : Reads source 0 commands)
    (result : Option State) :
    (∃ fuel events, (eventMachine tables mode source).run fuel (start source state) =
      (events, .finished result)) ↔ MMB.run tables mode state commands = result := by
  have represented : Represents source (start source state) (.commands state commands) :=
    ⟨rfl, commands, read, rfl⟩
  exact (finished_iff tables mode source _ _ represented result).trans
    (MMB.event_finished_iff tables mode state commands result)

theorem run_add (tables : Tables) (mode : Mode) (source : Source)
    (first extra : Nat) (cursor : Cursor) :
    (eventMachine tables mode source).run (first + extra) cursor =
      (eventMachine tables mode source).continueRun extra
        ((eventMachine tables mode source).run first cursor) :=
  Machine.run_add _ _ _ _

theorem events_prefix (tables : Tables) (mode : Mode) (source : Source)
    (first extra : Nat) (cursor : Cursor) :
    ((eventMachine tables mode source).run first cursor).1.IsPrefix
      ((eventMachine tables mode source).run (first + extra) cursor).1 := by
  rw [run_add]
  exact (eventMachine tables mode source).continueRun_events_prefix _ _

/-- Completion of the actual borrowed worker, followed by original assertion
validation, proves the original MM0 judgment in its full argument-and-dummy
context. The separately supplied declarations remain an explicit boundary. -/
theorem finished_assertion_derives
    {signature : Kernel.TermSignature} {definitions : Kernel.Definition.Signature}
    {theorems : Kernel.TheoremSignature} {tables : Tables}
    (declarations : MeTTa.ExecutedSoundness.KernelDeclarations
      signature definitions theorems tables)
    (source : Source) (commands : List ProofCmd) (read : Reads source 0 commands)
    (entry : ThmEntry) (declaration : Kernel.TheoremDecl)
    (declared : Statements.theoremDecl tables.terms entry = some declaration)
    (loaded after : State) (initialized : loadArgs tables.sorts entry.args = some loaded)
    (completed : ∃ fuel events, (eventMachine tables .assertion source).run fuel
      (start source loaded) = (events, .finished (some after)))
    (accepted : finishAssertion tables entry after false = true) :
    Kernel.Derives signature definitions theorems
      (Statements.context entry.args ++
        (MeTTa.MMBStateScopeSoundness.dummySorts commands).map Kernel.Binder.bound)
      declaration.hypotheses declaration.conclusion := by
  have executed := (finished_iff_run tables .assertion source loaded commands read (some after)).mp completed
  have checked : checkAssertion tables entry commands false = true :=
    (checkAssertion_of_run tables entry commands false loaded after initialized executed).trans accepted
  exact MeTTa.ExecutedSoundness.checkAssertion_derives declarations entry declaration commands declared checked

theorem changed_scope_stops (tables : Tables) (mode : Mode) (source : Source)
    (cursor : Cursor) (changed : cursor.scope ≠ source.scope) :
    next tables mode source cursor = none := by
  simp [next, changed]

theorem missing_command_stops (tables : Tables) (mode : Mode) (source : Source)
    (state : State) (position : Nat) (beforeEnd : position < source.length)
    (missing : source.read position = none) :
    next tables mode source ⟨source.scope, position, .commands state⟩ = none := by
  simp [next, beforeEnd, missing]

/-- Compare the actual commands already consumed by a cursor. An unchanged
label is insufficient. This check is a source-admission component, not an
authorization to import an invented checkpoint or change declaration tables.
Later source commands may differ: they have not contributed to this state. -/
def usedReadsAgree (previous current : Source) (cursor : Cursor) : Bool :=
  cursor.scope == previous.scope && previous.scope.owner == current.scope.owner &&
    previous.scope.source == current.scope.source && previous.length == current.length &&
    (List.range cursor.position).all (fun position => previous.read position == current.read position)

theorem usedReadsAgree_iff (previous current : Source) (cursor : Cursor) :
    usedReadsAgree previous current cursor = true ↔
      cursor.scope = previous.scope ∧ previous.scope.owner = current.scope.owner ∧
      previous.scope.source = current.scope.source ∧ previous.length = current.length ∧
      ∀ position < cursor.position, previous.read position = current.read position := by
  simp only [usedReadsAgree, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range]
  tauto

theorem changed_used_read_refused (previous current : Source) (cursor : Cursor)
    (position : Nat) (used : position < cursor.position)
    (changed : previous.read position ≠ current.read position) :
    usedReadsAgree previous current cursor = false := by
  cases agreement : usedReadsAgree previous current cursor with
  | false => rfl
  | true =>
      have exactReads := (usedReadsAgree_iff previous current cursor).mp agreement
      exact False.elim (changed (exactReads.2.2.2.2 position used))

theorem reads_of_lookup (source : Source) (position : Nat) (commands : List ProofCmd)
    (length : source.length = position + commands.length)
    (lookup : ∀ index, index < commands.length →
      source.read (position + index) = commands[index]?) : Reads source position commands := by
  induction commands generalizing position with
  | nil => exact .nil (by simp_all)
  | cons command rest ih =>
      refine .cons (by simp only [List.length_cons] at length; omega) ?_ ?_
      · simpa using lookup 0 (by simp)
      · apply ih (position + 1)
        · simp only [List.length_cons] at length
          omega
        · intro index beforeEnd
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            lookup (index + 1) (by simpa using beforeEnd)

/-- A list-backed calibration provider; production providers implement the
same read interface over their own stable source addresses. -/
def Source.ofCommands (scope : Scope) (commands : List ProofCmd) : Source :=
  ⟨scope, commands.length, fun position => commands[position]?⟩

theorem reads_ofCommands (scope : Scope) (commands : List ProofCmd) :
    Reads (.ofCommands scope commands) 0 commands := by
  apply reads_of_lookup
  · simp [Source.ofCommands]
  · intro index _
    simp [Source.ofCommands]

namespace Controls

private def scope : Scope := ⟨7, 19, 3⟩
private def initial : State := ⟨[], [], [], [], 0, 0⟩
private def pStore : List Alloc := [⟨.app 0 [], MMB.Controls.constant 0⟩]
private def pResult : State := ⟨pStore, [.proof 0], [], [], 0, 0⟩
private def theoremCommands : List ProofCmd := [.term 0, .thm 0]
private def source : Source := .ofCommands scope theoremCommands

/-- A pause really is inside the existing theorem unifier, and its next
command position already follows the consumed theorem command. -/
theorem pause_inside_unification :
    ((eventMachine MMB.Controls.tables .assertion source).run 2 (start source initial)).2 =
      .exhausted ⟨scope, 2, .unify pStore .apply ⟨[0], [], [], []⟩ [.term 0]
        (.theorem ⟨pStore, [], [], [], 0, 0⟩ 0 false)⟩ := by
  rfl

theorem completed_theorem :
    ((eventMachine MMB.Controls.tables .assertion source).run 6 (start source initial)).2 =
      .finished (some pResult) := by
  rfl

theorem split_inside_unification :
    (eventMachine MMB.Controls.tables .assertion source).continueRun 4
      ((eventMachine MMB.Controls.tables .assertion source).run 2 (start source initial)) =
    (eventMachine MMB.Controls.tables .assertion source).run 6 (start source initial) := by
  exact (run_add MMB.Controls.tables .assertion source 2 4 (start source initial)).symm

private def repeatedReferences : Source :=
  .ofCommands scope [.termSave 0, .ref 0, .ref 0]

/-- Equal references preserve one allocation and three distinct stack uses. -/
theorem repeated_references_one_allocation :
    ((eventMachine MMB.Controls.tables .assertion repeatedReferences).run 5
      (start repeatedReferences initial)).2 =
      .finished (some ⟨pStore, [.expr 0, .expr 0, .expr 0], [.expr 0], [], 0, 0⟩) := by
  rfl

private def savedConversion : Source :=
  .ofCommands scope [.termSave 0, .ref 0, .thm 0, .conv, .refl]

private def copiedConversion : Source :=
  .ofCommands scope [.term 0, .term 0, .thm 0, .conv, .refl]

theorem saved_identity_accepted :
    ((eventMachine MMB.Controls.tables .assertion savedConversion).run 9
      (start savedConversion initial)).2 = .finished (some
        ⟨pStore, [.proof 0], [.expr 0], [], 0, 0⟩) := by
  rfl

/-- Physical equality of the two printed constants must not merge the two
logical allocations: the original identity-sensitive proof is rejected. -/
theorem separately_allocated_equal_terms_refused :
    ((eventMachine MMB.Controls.tables .assertion copiedConversion).run 9
      (start copiedConversion initial)).2 = .finished none := by
  rfl

private def missingSource : Source := { source with read := fun _ => none }

theorem missing_source_is_stuck :
    ((eventMachine MMB.Controls.tables .assertion missingSource).run 4
      (start missingSource initial)).2 = .stuck (start missingSource initial) := by
  rfl

private def changedUsedSource : Source :=
  { source with
    scope := ⟨scope.owner, scope.source, scope.revision + 1⟩
    read := fun position => if position = 0 then some (.term 1) else source.read position }

private def afterFirst : Cursor := ⟨scope, 1, .commands
  ⟨pStore, [.expr 0], [], [], 0, 0⟩⟩

theorem changed_used_source_stops :
    next MMB.Controls.tables .assertion changedUsedSource afterFirst = none := by
  decide

theorem changed_used_source_has_no_verdict : answer changedUsedSource afterFirst = none := by
  decide

private def changedReadSameStamp : Source :=
  { source with read := fun position => if position = 0 then some (.term 1) else source.read position }

/-- Exact dependency validation catches a changed used command even when all
visible source labels were left unchanged. -/
theorem changed_read_with_same_stamp_refused :
    usedReadsAgree source changedReadSameStamp afterFirst = false := by
  decide

private def changedUnreadCommand : Source :=
  { source with
    scope := ⟨scope.owner, scope.source, scope.revision + 1⟩
    read := fun position => if position = 1 then some (.term 1) else source.read position }

theorem unread_change_preserves_source_prefix :
    usedReadsAgree source changedUnreadCommand afterFirst = true := by
  decide

private def foreignOwner : Source :=
  { source with scope := ⟨scope.owner + 1, scope.source, scope.revision⟩ }

theorem another_owner_stops : next MMB.Controls.tables .assertion foreignOwner afterFirst = none := by
  decide

theorem submitted_commands_correspond :
    (∃ fuel events, (eventMachine MMB.Controls.tables .assertion source).run fuel
      (start source initial) = (events, .finished (some pResult))) ↔
      MMB.run MMB.Controls.tables .assertion initial theoremCommands = some pResult :=
  finished_iff_run _ _ _ _ _ (reads_ofCommands _ _) _

end Controls

end Mettapedia.Languages.MM0.Formats.MMB.BorrowedProofCursor
