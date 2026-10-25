import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.ClassAdvance
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Canonical
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.RunnerSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.SearchRunner
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.QuoteDropNormal
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.ModelNormal
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.StandardWire
import Mettapedia.OSLF.MeTTaIL.Complete.ClassesChecked

/-!
# Whole runs over steps modulo equations, in standard, canonical, reflective or model form

`gslt:runner:*` runs `ResumableSearchRunner.Machine` over `Complete.Normalized.search`, the
search modulo equations that commits each receipt's target in the standard form of the plan's
declared laws, in the canonical form of that, in the canonical form of the quote-drop normal form of
a reflective presentation, or in the canonical form of the model normal form, which also applies the
wrapper laws of the declared collection algebra (`Complete.Normalized.Commit`). A tick resumes the
retained search; its first published receipt is committed and a fresh search begins at the
committed target; with nothing published, a complete search ends the run. Every reached search is
ready, its published targets are checked well-sorted, so a name table of the plan covers them, and
a committed form keeps the target's free names, so each tick, each page of ticks and the trace
print the model's machine.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.MeTTaIL.Complete.Footprint (Scope Declared KeyReady ClassReady)
open Mettapedia.Machines.ResumableSearchRunner (Phase Status Machine)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit
open DescentCodec
open StandardWire
open CanonicalCompare (Covered)

/-- A fact of the canonical library at values, in the runner's runtime. -/
syntax "canonical_lifted% " "[" str,* "] " term:max : term
macro_rules
  | `(canonical_lifted% [$names,*] $fact) =>
      `(canonical_runner_lifted% [$names,*] $fact)

/-- A fact of the laws library at values, in the runner's runtime. -/
syntax "laws_lifted% " "[" str,* "] " term:max : term
macro_rules
  | `(laws_lifted% [$names,*] $fact) => `(canonical_lifted% [$names,*]
      (Library.lift_call canonical_checked (by decide +kernel) (by decide) (by decide +kernel) (by decide) [$names,*]
        (by decide) (by rfl) (by decide +kernel) $fact))

/-- A fact of the complete machine at values, in the runner's runtime. -/
syntax "runner_lifted% " "[" str,* "] " term:max : term
macro_rules
  | `(runner_lifted% [$names,*] $fact) => `(laws_lifted% [$names,*]
      (Library.lift_call laws_checked (by decide +kernel) (by decide) (by decide +kernel) (by decide) [$names,*]
        (by decide) (by rfl) (by decide +kernel) $fact))

/-- Walk a body of the runner library. -/
syntax "runner_eval" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| runner_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call runner_checked; metta_eval [$facts,*] with runner_checked
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?, pattern_symbol_unmatched, $extra,*]))

/-- How a machine's phase is written. -/
def classPhaseSymbol : Phase → String
  | .running => "ClassRunning"
  | .done => "ClassDone"
  | .blocked => "ClassBlocked"

variable (plan : GeneralExecutionAdmission.Plan)

/-- A machine of the search modulo equations. -/
abbrev ClassMachine := Machine Pattern (Complete.Classes.State plan) GeneralOccurrenceSemantics.Receipt

def classMachineTerm (machine : ClassMachine plan) : Term :=
  .application "ClassMachine" [.symbol (classPhaseSymbol machine.phase),
    InferenceCettaWire.encodePattern machine.state, classStateTerm plan machine.program,
    encodeList InferenceCettaWire.encodePattern machine.states, encodeList classReceiptTerm machine.receipts]

/-- The trace: the phase, then the states in chronological order. -/
def classTraceTerm (machine : ClassMachine plan) : Term :=
  .application "RunTrace" [.symbol (classPhaseSymbol machine.phase),
    encodeList InferenceCettaWire.encodePattern machine.states.reverse]

variable {plan}

theorem key_licensed_of_ready {bound : List TypeExpr} {expected : TypeExpr} {footprint : List String}
    {key : Complete.Classes.Key} {deep : Complete.Deep.State (Complete.Classes.family plan key)}
    (ready : KeyReady plan bound expected footprint key deep) : KeyLicensed plan bound expected key := by
  cases key with
  | rule rep job => exact ready.1
  | forward rep lane => exact ready.1
  | backward rep candidate lane => exact ready.1

/-- A search that is ready and whose published targets are checked. -/
def SearchReady (bound : List TypeExpr) (expected : TypeExpr) (footprint : List String)
    (search : Complete.Classes.State plan) : Prop :=
  ClassReady plan bound expected footprint search ∧ Complete.Classes.LogChecked plan bound expected search

theorem searchReady_rounds {bound : List TypeExpr} {expected : TypeExpr} {footprint : List String}
    (scope : Scope plan footprint) (work : Nat) {search : Complete.Classes.State plan}
    (ready : SearchReady bound expected footprint search) :
    SearchReady bound expected footprint (Complete.Classes.rounds plan bound expected work search) :=
  ⟨Complete.Footprint.ready_rounds scope work ready.1, Complete.Classes.logChecked_rounds work ready.2⟩

theorem searchReady_begin {bound : List TypeExpr} {expected : TypeExpr} {footprint : List String}
    (scope : Scope plan footprint) {source : Pattern} (inside : ∀ name ∈ source.freeFvarNames, name ∈ footprint) :
    SearchReady bound expected footprint (Complete.Classes.begin plan bound expected source) :=
  ⟨Complete.Footprint.ready_begin scope inside, Complete.Classes.logChecked_begin source⟩

/-- A machine whose retained search is ready. -/
def RunnerReady (bound : List TypeExpr) (expected : TypeExpr) (footprint : List String)
    (machine : ClassMachine plan) : Prop :=
  SearchReady bound expected footprint machine.program

theorem runner_ready_tick {bound : List TypeExpr} {expected : TypeExpr} {footprint : List String}
    (scope : Scope plan footprint) (mode : Complete.Normalized.Commit) {machine : ClassMachine plan}
    (ready : RunnerReady bound expected footprint machine) (quantum : Nat) :
    RunnerReady bound expected footprint
      (Machine.tick (Complete.Normalized.search plan bound expected mode) machine quantum) := by
  obtain ⟨phase, current, program, states, receipts⟩ := machine
  have resumed := searchReady_rounds scope quantum ready
  cases phase with
  | done => exact ready
  | blocked => exact ready
  | running =>
    unfold RunnerReady
    simp only [Machine.tick, Complete.Normalized.search, Complete.Classes.search]
    cases published : (Complete.Classes.rounds plan bound expected quantum program).log with
    | nil => exact resumed
    | cons receipt rest =>
      exact searchReady_begin scope
        (Complete.Normalized.target_within plan bound expected receipt footprint
          (resumed.1.log receipt (by simp [published])) mode)

variable (plan)

/-- What a pattern needs for a run to commit it: in a sorted form, its names are in the table. -/
def CommitReady (mode : Complete.Normalized.Commit) (names : List String) (pattern : Pattern) : Prop :=
  mode ≠ .standard → CanonicalCompare.Covered names pattern

theorem commitReady_of_checked {mode : Complete.Normalized.Commit} {names : List String} (named : TableFor plan names)
    {bound : List TypeExpr} {expected : TypeExpr} {pattern : Pattern}
    (checked : Complete.Classes.Checked plan bound expected pattern) : CommitReady mode names pattern :=
  fun _ => named.covered checked

@[metta_head "gslt:runner:standard"]
theorem runner_standard_returns (state : State) (mode : Complete.Normalized.Commit) (names : List String)
    (named : TableFor plan names) (pattern : Pattern) (ready : CommitReady mode names pattern) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:runner:standard" [encoded (commitTerm plan mode names), patternValue pattern]) state
      (patternValue (Complete.Normalized.commit plan mode pattern)) := by
  cases mode with
  | standard =>
    have standard := laws_lifted% ["laws", "extrusions", "pattern"]
      (standard_returns state (Complete.Normalized.laws plan) (Complete.Normalized.extrusions plan) pattern)
    runner_eval [standard] unfolding [commitTerm, standardTerm, Complete.Normalized.commit, Complete.Normalized.standard,
      lawsValue, extrusionsValue]
  | canonical =>
    have canonical := canonical_lifted% ["names", "laws", "extrusions", "pattern"]
      (canonical_returns state named.ordered (Complete.Normalized.laws plan) (Complete.Normalized.extrusions plan)
        pattern (ready (by decide)))
    runner_eval [canonical] unfolding [commitTerm, canonicalTerm, Complete.Normalized.commit,
      Complete.Normalized.standard, lawsValue, extrusionsValue, tableValue]
  | reflective declaration =>
    have normalized := runner_lifted% ["quote", "drop", "pattern"]
      (complete_normalize_returns state declaration pattern)
    have canonical := canonical_lifted% ["names", "laws", "extrusions", "pattern"]
      (canonical_returns state named.ordered (Complete.Normalized.laws plan) (Complete.Normalized.extrusions plan)
        (ReflectiveSubstitution.normalizeReflective declaration pattern)
        (covered_normal declaration (ready fun same => Complete.Normalized.Commit.noConfusion same)))
    runner_eval [normalized, canonical] unfolding [commitTerm, reflectiveTerm, Complete.Normalized.commit,
      Complete.Normalized.standard, lawsValue, extrusionsValue, tableValue]
  | model declaration =>
    have normalized := canonical_lifted% ["names", "quote", "drop", "laws", "pattern"]
      (model_normal_returns state named.ordered declaration (Complete.Normalized.laws plan) named.units pattern
        (ready fun same => Complete.Normalized.Commit.noConfusion same))
    have canonical := canonical_lifted% ["names", "laws", "extrusions", "pattern"]
      (canonical_returns state named.ordered (Complete.Normalized.laws plan) (Complete.Normalized.extrusions plan)
        (Wrappers.modelNormal (Complete.Normalized.laws plan) declaration pattern)
        (covered_modelNormal declaration named.units (ready fun same => Complete.Normalized.Commit.noConfusion same)))
    runner_eval [normalized, canonical] unfolding [commitTerm, modelTerm, Complete.Normalized.commit,
      Complete.Normalized.standard, lawsValue, extrusionsValue, tableValue]

/-! ## The native search-backend boundary -/

/-- How a generic search status is written by the native backend. -/
def searchStatusAtom : Status → Atom
  | .complete => .symbol "SearchComplete"
  | .blocked => .symbol "SearchBlocked"
  | .pending => .symbol "SearchPending"

/-- A zero-work native run only initializes the class search, so it needs declaration
coverage but no executable round. -/
theorem search_run_zero_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (declared : Declared plan footprint) (source : Pattern)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ footprint) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:search:run" [classSearchBackend, planValue plan table bound expected,
        patternValue source, number 0]) state
      (encoded (classStateTerm plan ((Complete.Classes.search plan bound expected).run source 0))) := by
  have started := runner_lifted% ["plan", "source"]
    (classes_begin_returns plan state table bound expected footprint tabled declared source inside)
  have idle := runner_lifted% ["plan", "quantum", "program"]
    (classes_rounds_zero_returns plan state table bound expected
      (Complete.Classes.begin plan bound expected source))
  runner_eval [started, idle]
    unfolding [classSearchBackend, Complete.Classes.search, Complete.Classes.rounds]

/-- **The class backend's native `run` is the Lean class search's `run`.** -/
@[metta_head "gslt:search:run"]
theorem search_run_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (scope : Scope plan footprint) (source : Pattern)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ footprint) (work : Nat) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:search:run" [classSearchBackend, planValue plan table bound expected,
        patternValue source, number work]) state
      (encoded (classStateTerm plan ((Complete.Classes.search plan bound expected).run source work))) := by
  have started := runner_lifted% ["plan", "source"]
    (classes_begin_returns plan state table bound expected footprint tabled scope.declared source inside)
  have ready := Complete.Footprint.ready_begin (bound := bound) (expected := expected) scope inside
  have resumed := runner_lifted% ["plan", "quantum", "program"]
    (classes_rounds_returns plan state table bound expected footprint tabled scope work
      (Complete.Classes.begin plan bound expected source) ready)
  runner_eval [started, resumed]
    unfolding [classSearchBackend, Complete.Classes.search, Complete.Classes.rounds]

/-- **The class backend's native `resume` is the Lean class search's `resume`.** -/
@[metta_head "gslt:search:resume"]
theorem search_resume_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (scope : Scope plan footprint) (run : Complete.Classes.State plan)
    (ready : SearchReady bound expected footprint run) (work : Nat) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:search:resume" [classSearchBackend, planValue plan table bound expected,
        encoded (classStateTerm plan run), number work]) state
      (encoded (classStateTerm plan ((Complete.Classes.search plan bound expected).resume run work))) := by
  have resumed := runner_lifted% ["plan", "quantum", "program"]
    (classes_rounds_returns plan state table bound expected footprint tabled scope work run ready.1)
  runner_eval [resumed] unfolding [classSearchBackend, Complete.Classes.search]

/-- **The class backend publishes exactly the retained class log.** -/
@[metta_head "gslt:search:publication"]
theorem search_publication_returns (state : State) (run : Complete.Classes.State plan) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:search:publication" [classSearchBackend, encoded (classStateTerm plan run)]) state
      (encoded (encodeList classReceiptTerm run.log)) := by
  obtain ⟨round, reps, entries, log⟩ := run
  runner_eval unfolding [classSearchBackend, classStateTerm, Complete.Classes.search]

/-- **The class backend reports the Lean class search's status.** -/
@[metta_head "gslt:search:status"]
theorem search_status_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (run : Complete.Classes.State plan)
    (licensed : ∀ entry ∈ run.entries, KeyLicensed plan bound expected entry.1) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:search:status" [classSearchBackend, planValue plan table bound expected,
        encoded (classStateTerm plan run)]) state
      (searchStatusAtom ((Complete.Classes.search plan bound expected).status run)) := by
  obtain ⟨round, reps, entries, log⟩ := run
  have done := runner_lifted% ["plan", "entries"]
    (classes_entries_complete_returns plan state table bound expected entries licensed)
  cases finished : entries.all fun entry => entry.2.complete <;>
    runner_eval [done]
      unfolding [classSearchBackend, classStateTerm, Complete.Classes.search, Complete.Classes.status,
        Complete.Classes.complete, searchStatusAtom, finished]

/-- **The class backend's native target is the committed Lean receipt target.** -/
@[metta_head "gslt:search:target"]
theorem search_target_returns (state : State) (mode : Complete.Normalized.Commit) (names : List String)
    (named : TableFor plan names) (bound : List TypeExpr) (expected : TypeExpr)
    (receipt : GeneralOccurrenceSemantics.Receipt) (checked : Complete.Classes.Checked plan bound expected receipt.target) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:search:target" [classSearchBackend, encoded (commitTerm plan mode names),
        encoded (classReceiptTerm receipt)]) state
      (patternValue ((Complete.Normalized.search plan bound expected mode).target receipt)) := by
  have standard := runner_standard_returns plan state mode names named receipt.target
    (commitReady_of_checked plan (mode := mode) named checked)
  runner_eval [standard] unfolding [classSearchBackend, classReceiptTerm,
    ScopedRuleJobReadoutExecution.receiptTerm, GeneralOccurrenceSemantics.Receipt.target,
    Complete.Normalized.search]

/-- The established search realizes the common native search algebra on its
existing footprint and checked-target invariants. -/
def classRealization (mode : Complete.Normalized.Commit) (names : List String)
    (named : TableFor plan names) (table : List (String × TypeExpr))
    (bound : List TypeExpr) (expected : TypeExpr) (footprint : List String)
    (tabled : table = plan.snapshot.free.entriesOn footprint) (scope : Scope plan footprint) :
    SearchRunner.Realization (Complete.Normalized.search plan bound expected mode) where
  lawful := Complete.Normalized.search_lawful plan bound expected mode
  stable := Complete.Settled.normalized_stable plan bound expected mode
  backend := classSearchBackend
  plan := planValue plan table bound expected
  standard := encoded (commitTerm plan mode names)
  runTerm := classStateTerm plan
  receiptTerm := classReceiptTerm
  SourceReady source := ∀ name ∈ source.freeFvarNames, name ∈ footprint
  RunReady := SearchReady bound expected footprint
  ReceiptReady receipt := Complete.Classes.Checked plan bound expected receipt.target
  run_ready _ inside work :=
    searchReady_rounds scope work (searchReady_begin scope inside)
  resume_ready _ ready work := searchReady_rounds scope work ready
  publication_ready _ ready receipt member := ready.2 receipt member
  target_ready receipt ready :=
    Complete.Normalized.target_within plan bound expected receipt footprint
      (Complete.Footprint.sorted_within scope.declared ready) mode
  run_returns state source inside work :=
    search_run_returns plan state table bound expected footprint tabled scope source inside work
  resume_returns state run ready work :=
    search_resume_returns plan state table bound expected footprint tabled scope run ready work
  publication_returns state run := search_publication_returns plan state run
  status_returns state run ready :=
    search_status_returns plan state table bound expected run
      (fun entry member => key_licensed_of_ready (ready.1.entries entry member))
  target_returns state receipt ready :=
    search_target_returns plan state mode names named bound expected receipt ready

@[metta_head "gslt:runner:target"]
theorem runner_target_returns (state : State) (mode : Complete.Normalized.Commit) (names : List String)
    (named : TableFor plan names) (bound : List TypeExpr) (expected : TypeExpr)
    (receipt : GeneralOccurrenceSemantics.Receipt) (checked : Complete.Classes.Checked plan bound expected receipt.target) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:runner:target" [CompleteExecution.classSearchBackend, encoded (commitTerm plan mode names), encoded (classReceiptTerm receipt)]) state
      (patternValue ((Complete.Normalized.search plan bound expected mode).target receipt)) := by
  have target := search_target_returns plan state mode names named bound expected receipt checked
  runner_eval [target] unfolding [classSearchBackend]

/-- **A run starts at the source's standard form.** -/
@[metta_head "gslt:runner:begin"]
theorem runner_begin_returns (state : State) (mode : Complete.Normalized.Commit) (names : List String)
    (named : TableFor plan names) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (declared : Declared plan footprint) (source : Pattern)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ footprint) (ready : CommitReady mode names source) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:runner:begin" [CompleteExecution.classSearchBackend, planValue plan table bound expected, encoded (commitTerm plan mode names),
        patternValue source])
      state (encoded (classMachineTerm plan
        (Machine.begin (Complete.Normalized.search plan bound expected mode)
          (Complete.Normalized.commit plan mode source)))) := by
  have standard := runner_standard_returns plan state mode names named source ready
  have started := search_run_zero_returns plan state table bound expected footprint tabled declared
    (Complete.Normalized.commit plan mode source)
    (Complete.Normalized.commit_within plan mode source footprint inside)
  runner_eval [standard, started]
    unfolding [classMachineTerm, Machine.begin, Complete.Normalized.search, Complete.Classes.search,
      classSearchBackend, Complete.Classes.rounds, classPhaseSymbol, encodeList, patternValue]

@[metta_head "gslt:runner:tick"]
theorem runner_tick_returns (state : State) (mode : Complete.Normalized.Commit) (names : List String)
    (named : TableFor plan names) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (scope : Scope plan footprint) (machine : ClassMachine plan)
    (ready : RunnerReady bound expected footprint machine) (quantum : Nat) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:runner:tick" [CompleteExecution.classSearchBackend, planValue plan table bound expected, encoded (commitTerm plan mode names),
        encoded (classMachineTerm plan machine), number quantum])
      state (encoded (classMachineTerm plan
        (Machine.tick (Complete.Normalized.search plan bound expected mode) machine quantum))) := by
  exact SearchRunner.tick_returns
    (classRealization plan mode names named table bound expected footprint tabled scope)
    state machine ready quantum

@[metta_head "gslt:runner:advance"]
theorem runner_advance_returns (state : State) (mode : Complete.Normalized.Commit) (names : List String)
    (named : TableFor plan names) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (scope : Scope plan footprint) (quantum : Nat) :
    ∀ (ticks : Nat) (machine : ClassMachine plan), RunnerReady bound expected footprint machine →
      PureReturns runnerLibrary.runtime [] state
        (apply "gslt:runner:advance" [CompleteExecution.classSearchBackend, planValue plan table bound expected, encoded (commitTerm plan mode names),
          number ticks, number quantum, encoded (classMachineTerm plan machine)])
        state (encoded (classMachineTerm plan
          (Machine.advance (Complete.Normalized.search plan bound expected mode) ticks quantum machine)))
  | ticks, machine, ready => by
      exact SearchRunner.advance_returns
        (classRealization plan mode names named table bound expected footprint tabled scope)
        state quantum ticks machine ready

@[metta_head "gslt:runner:reverse-onto"]
theorem runner_reverse_onto_returns (state : State) : ∀ (items tail : List Term),
    PureReturns runnerLibrary.runtime [] state (apply "gslt:runner:reverse-onto" [terms items, terms tail]) state
      (terms (items.reverseAux tail))
  | [], tail => by
    runner_eval unfolding [terms, List.reverseAux]
  | item :: rest, tail => by
    have later := runner_reverse_onto_returns state rest (item :: tail)
    runner_eval [later] unfolding [terms, List.reverseAux]

@[metta_head "gslt:runner:trace"]
theorem runner_trace_returns (state : State) (machine : ClassMachine plan) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:runner:trace" [encoded (classMachineTerm plan machine)]) state
      (encoded (classTraceTerm plan machine)) := by
  obtain ⟨phase, current, program, states, receipts⟩ := machine
  have reversed := runner_reverse_onto_returns state (states.map InferenceCettaWire.encodePattern) []
  rw [List.reverseAux_eq, List.append_nil, ← List.map_reverse, ← terms_map, ← terms_map] at reversed
  cases phase <;>
    runner_eval [reversed] unfolding [classMachineTerm, classTraceTerm, classPhaseSymbol]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
