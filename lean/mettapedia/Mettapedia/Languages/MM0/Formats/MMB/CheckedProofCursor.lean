import Mettapedia.Languages.MM0.Formats.MMB.BorrowedProofCursor

/-!
# Reached, source-indexed MMB checking checkpoints

A checkpoint is indexed by the actual declaration tables, mode, source
provider and initial machine state. Its private constructor retains the
complete operational observation together with an erased proof that it was
reached. Begin and advance construct that evidence; a caller supplies neither
a plausible working state nor a claimed execution trace.

Advancing calls the existing occurrence-preserving runner's `continueRun`.
No source rebinding or table conversion is exposed. Numeric owner/source
labels do not identify providers. This is a Lean abstraction boundary, not a
claim about C memory protection, native capabilities or serialized inputs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Formats.MMB.CheckedProofCursor

open Mettapedia.GSLT.Distinction.ProductiveBlocks
open BorrowedProofCursor

abbrev Observation :=
  List (Mettapedia.Machines.ProductiveCoreAdapters.Occurrence Cursor) ×
    Outcome Cursor (Option State) Empty

/-- The constructor is private. The index contains the provider function and
actual tables, rather than only their printable identity coordinates. -/
structure Checkpoint (tables : Tables) (mode : Mode) (source : Source) (initial : State) where
  private mk ::
  spent : Nat
  observation : Observation
  reached : observation = (BorrowedProofCursor.eventMachine tables mode source).run spent (start source initial)

def begin (tables : Tables) (mode : Mode) (source : Source) (initial : State) :
    Checkpoint tables mode source initial :=
  ⟨0, ([], .exhausted (start source initial)), rfl⟩

/-- Resume the actual retained residual, including its prior publications.
The reachability proof is erased and does not run or reconstruct the prefix. -/
def advance {tables : Tables} {mode : Mode} {source : Source} {initial : State}
    (extra : Nat) (checkpoint : Checkpoint tables mode source initial) :
    Checkpoint tables mode source initial :=
  ⟨checkpoint.spent + extra,
    (BorrowedProofCursor.eventMachine tables mode source).continueRun extra checkpoint.observation, by
      rw [checkpoint.reached, ← BorrowedProofCursor.run_add]⟩

theorem advance_observation {tables : Tables} {mode : Mode} {source : Source} {initial : State}
    (extra : Nat) (checkpoint : Checkpoint tables mode source initial) :
    (advance extra checkpoint).observation =
      (BorrowedProofCursor.eventMachine tables mode source).continueRun extra checkpoint.observation := rfl

theorem advance_reached {tables : Tables} {mode : Mode} {source : Source} {initial : State}
    (extra : Nat) (checkpoint : Checkpoint tables mode source initial) :
    (advance extra checkpoint).observation =
      (BorrowedProofCursor.eventMachine tables mode source).run (checkpoint.spent + extra) (start source initial) :=
  (advance extra checkpoint).reached

theorem advance_zero {tables : Tables} {mode : Mode} {source : Source} {initial : State}
    (checkpoint : Checkpoint tables mode source initial) : advance 0 checkpoint = checkpoint := by
  rcases checkpoint with ⟨spent, observation, reached⟩
  simp [advance]

/-- Splitting a budget preserves the checkpoint itself, including its exact
events, outcome and accumulated source/machine position. -/
theorem advance_add {tables : Tables} {mode : Mode} {source : Source} {initial : State}
    (first extra : Nat) (checkpoint : Checkpoint tables mode source initial) :
    advance extra (advance first checkpoint) = advance (first + extra) checkpoint := by
  rcases checkpoint with ⟨spent, observation, reached⟩
  simp only [advance, Nat.add_assoc]
  congr 1
  exact ((BorrowedProofCursor.eventMachine tables mode source).continueRun_add first extra observation).symm

theorem events_prefix {tables : Tables} {mode : Mode} {source : Source} {initial : State}
    (extra : Nat) (checkpoint : Checkpoint tables mode source initial) :
    checkpoint.observation.1.IsPrefix (advance extra checkpoint).observation.1 :=
  (BorrowedProofCursor.eventMachine tables mode source).continueRun_events_prefix extra checkpoint.observation

/-- Only a completed stream exposes a result. A pending unifier, exhausted
budget or missing/stale source has no completed result. -/
def result {tables : Tables} {mode : Mode} {source : Source} {initial : State}
    (checkpoint : Checkpoint tables mode source initial) : Option (Option State) :=
  match checkpoint.observation.2 with
  | .finished state => some state
  | _ => none

theorem result_reached {tables : Tables} {mode : Mode} {source : Source} {initial : State}
    (checkpoint : Checkpoint tables mode source initial) (state : Option State)
    (observed : result checkpoint = some state) :
    ∃ fuel events, (BorrowedProofCursor.eventMachine tables mode source).run fuel (start source initial) =
      (events, .finished state) := by
  cases outcome : checkpoint.observation.2 with
  | finished actual =>
      have same : actual = state := by simpa [result, outcome] using observed
      subst actual
      exact ⟨checkpoint.spent, checkpoint.observation.1,
        checkpoint.reached.symm.trans (Prod.ext rfl outcome)⟩
  | _ => simp [result, outcome] at observed

/-- Starting from any reached checkpoint, a completed result is eventually
observable exactly when the original stream executor returns it. Previously
spent budget changes neither completion nor the result. -/
theorem eventual_result_iff (tables : Tables) (mode : Mode) (source : Source)
    (initial : State) (commands : List ProofCmd) (read : Reads source 0 commands)
    (checkpoint : Checkpoint tables mode source initial) (value : Option State) :
    (∃ extra, result (advance extra checkpoint) = some value) ↔
      MMB.run tables mode initial commands = value := by
  constructor
  · rintro ⟨extra, observed⟩
    exact (finished_iff_run tables mode source initial commands read value).mp
      (result_reached (advance extra checkpoint) value observed)
  · intro executed
    obtain ⟨fuel, events, completed⟩ :=
      (finished_iff_run tables mode source initial commands read value).mpr executed
    have continued : (advance fuel checkpoint).observation = (events, .finished value) := by
      rw [advance_reached, Nat.add_comm checkpoint.spent fuel,
        BorrowedProofCursor.run_add, completed]
      rfl
    exact ⟨fuel, by simp [result, continued]⟩

/-- Source labels, an externally supplied cursor or a Boolean are not
accepted as completed execution. This observer uses only a reached result. -/
def assertionVerdict {tables : Tables} {source : Source} {initial : State}
    (entry : ThmEntry) (isAxiom : Bool) (checkpoint : Checkpoint tables .assertion source initial) :
    Option Bool :=
  match result checkpoint with
  | none => none
  | some none => some false
  | some (some after) => some (finishAssertion tables entry after isAxiom)

theorem assertionVerdict_sound (tables : Tables) (source : Source)
    (commands : List ProofCmd) (read : Reads source 0 commands)
    (entry : ThmEntry) (loaded : State)
    (initialized : loadArgs tables.sorts entry.args = some loaded)
    (checkpoint : Checkpoint tables .assertion source loaded) (isAxiom verdict : Bool)
    (observed : assertionVerdict entry isAxiom checkpoint = some verdict) :
    checkAssertion tables entry commands isAxiom = verdict := by
  cases completed : result checkpoint with
  | none => simp [assertionVerdict, completed] at observed
  | some value =>
      have executed := (finished_iff_run tables .assertion source loaded commands read value).mp
        (result_reached checkpoint value completed)
      cases value with
      | none =>
          have same : false = verdict := by simpa [assertionVerdict, completed] using observed
          simpa [checkAssertion, initialized, executed] using same
      | some after =>
          have same : finishAssertion tables entry after isAxiom = verdict := by
            simpa [assertionVerdict, completed] using observed
          exact (checkAssertion_of_run tables entry commands isAxiom loaded after initialized executed).trans same

/-- The logical observer is justified by the existing MM0 kernel theorem.
The proof stream is not promoted to its own axiom basis or source statement. -/
theorem assertion_derives
    {signature : Kernel.TermSignature} {definitions : Kernel.Definition.Signature}
    {theorems : Kernel.TheoremSignature} {tables : Tables}
    (declarations : MeTTa.ExecutedSoundness.KernelDeclarations
      signature definitions theorems tables)
    (source : Source) (commands : List ProofCmd) (read : Reads source 0 commands)
    (entry : ThmEntry) (declaration : Kernel.TheoremDecl)
    (declared : Statements.theoremDecl tables.terms entry = some declaration)
    (loaded : State) (initialized : loadArgs tables.sorts entry.args = some loaded)
    (checkpoint : Checkpoint tables .assertion source loaded)
    (accepted : assertionVerdict entry false checkpoint = some true) :
    Kernel.Derives signature definitions theorems
      (Statements.context entry.args ++
        (MeTTa.MMBStateScopeSoundness.dummySorts commands).map Kernel.Binder.bound)
      declaration.hypotheses declaration.conclusion := by
  cases observed : result checkpoint with
  | none => simp [assertionVerdict, observed] at accepted
  | some value =>
      cases value with
      | none => simp [assertionVerdict, observed] at accepted
      | some after =>
          have checked : finishAssertion tables entry after false = true := by
            simpa [assertionVerdict, observed] using accepted
          exact finished_assertion_derives declarations source commands read entry declaration declared
            loaded after initialized (result_reached checkpoint (some after) observed) checked

namespace Controls

private def scope : Scope := ⟨7, 19, 3⟩
private def initial : State := ⟨[], [], [], [], 0, 0⟩
private def firstSource : Source := .ofCommands scope [.term 0, .thm 0]
private def differentSource : Source := .ofCommands scope [.term 1, .thm 0]
private def differentTables : Tables := { MMB.Controls.tables with thms := [] }
private def entry : ThmEntry := ⟨[], [.term 0]⟩

theorem begin_has_no_verdict :
    assertionVerdict entry false (begin MMB.Controls.tables .assertion firstSource initial) = none := by
  rfl

theorem suspended_unifier_has_no_verdict :
    assertionVerdict entry false
      (advance 2 (begin MMB.Controls.tables .assertion firstSource initial)) = none := by
  rfl

theorem resumed_theorem_accepted :
    assertionVerdict entry false
      (advance 4 (advance 2 (begin MMB.Controls.tables .assertion firstSource initial))) = some true := by
  rfl

theorem exact_split_checkpoint :
    advance 4 (advance 2 (begin MMB.Controls.tables .assertion firstSource initial)) =
      advance 6 (begin MMB.Controls.tables .assertion firstSource initial) :=
  advance_add _ _ _

theorem labels_do_not_identify_provider : firstSource.scope = differentSource.scope := rfl

/-- A different provider with the same labels cannot be passed to advance as
if it were the captured provider. The theorem also exhibits the actual read
difference that the labels omit. -/
theorem different_provider_refused_at_type_boundary : firstSource ≠ differentSource := by
  fail_if_success
    have wrong : Checkpoint MMB.Controls.tables .assertion differentSource initial :=
      advance 1 (begin MMB.Controls.tables .assertion firstSource initial)
  intro same
  have commands := congrArg (fun source : Source => source.read 0) same
  cases commands

theorem different_tables_refused_at_type_boundary : MMB.Controls.tables ≠ differentTables := by
  fail_if_success
    have wrong : Checkpoint differentTables .assertion firstSource initial :=
      advance 1 (begin MMB.Controls.tables .assertion firstSource initial)
  intro same
  have lengths := congrArg (fun tables : Tables => tables.thms.length) same
  cases lengths

theorem another_mode_refused_at_type_boundary : Mode.assertion ≠ Mode.definition := by
  fail_if_success
    have wrong : Checkpoint MMB.Controls.tables .definition firstSource initial :=
      advance 1 (begin MMB.Controls.tables .assertion firstSource initial)
  decide

private def changedInitial : State := { initial with nextBound := 1 }

theorem another_initial_state_refused_at_type_boundary : initial ≠ changedInitial := by
  fail_if_success
    have wrong : Checkpoint MMB.Controls.tables .assertion firstSource changedInitial :=
      advance 1 (begin MMB.Controls.tables .assertion firstSource initial)
  decide

private def missingSource : Source := ⟨scope, 1, fun _ => none⟩

theorem missing_source_has_no_completed_verdict :
    assertionVerdict entry false
      (advance 10 (begin MMB.Controls.tables .assertion missingSource initial)) = none := by
  rfl

theorem stopped_checkpoint_does_not_restart :
    (advance 10 (advance 10 (begin MMB.Controls.tables .assertion missingSource initial))).observation =
      (advance 10 (begin MMB.Controls.tables .assertion missingSource initial)).observation := by
  rfl

end Controls

end Mettapedia.Languages.MM0.Formats.MMB.CheckedProofCursor
