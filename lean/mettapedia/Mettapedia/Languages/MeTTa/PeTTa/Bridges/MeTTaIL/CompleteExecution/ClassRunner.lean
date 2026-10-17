import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.ClassAdvance
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Laws
import Mettapedia.OSLF.MeTTaIL.Complete.Normalized

/-!
# Whole runs over steps modulo equations, in standard form

`gslt:runner:*` runs `ResumableSearchRunner.Machine` over `Complete.Normalized.search`, the
search modulo equations that commits each receipt's target in the standard form of the plan's
declared laws. A tick resumes the retained search; its first published receipt is committed and
a fresh search begins at the target's standard form; with nothing published, a complete search
ends the run. Every reached search is ready, and a standard form keeps the target's free names,
so each tick, each page of ticks and the trace print the model's machine.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.MeTTaIL.Complete.Footprint (Scope Declared KeyReady ClassReady)
open Mettapedia.Machines.ResumableSearchRunner (Phase Machine)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit
open DescentCodec
open StandardWire

/-- A fact of the complete machine at values, in the runner's runtime. -/
syntax "runner_lifted% " "[" str,* "] " term:max : term
macro_rules
  | `(runner_lifted% [$names,*] $fact) => `(Library.lift_call runner_checked (by decide +kernel) (by decide)
      (by decide +kernel) (by decide) [$names,*] (by decide) (by rfl) (by decide +kernel)
      (Library.lift_call laws_checked (by decide +kernel) (by decide) (by decide +kernel) (by decide) [$names,*]
        (by decide) (by rfl) (by decide +kernel) $fact))

/-- A fact of the laws library at values, in the runner's runtime. -/
syntax "laws_lifted% " "[" str,* "] " term:max : term
macro_rules
  | `(laws_lifted% [$names,*] $fact) => `(Library.lift_call runner_checked (by decide +kernel) (by decide)
      (by decide +kernel) (by decide) [$names,*] (by decide) (by rfl) (by decide +kernel) $fact)

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

/-- A machine whose retained search is ready. -/
def RunnerReady (bound : List TypeExpr) (expected : TypeExpr) (footprint : List String)
    (machine : ClassMachine plan) : Prop :=
  ClassReady plan bound expected footprint machine.program

theorem runner_ready_tick {bound : List TypeExpr} {expected : TypeExpr} {footprint : List String}
    (scope : Scope plan footprint) {machine : ClassMachine plan}
    (ready : RunnerReady bound expected footprint machine) (quantum : Nat) :
    RunnerReady bound expected footprint
      (Machine.tick (Complete.Normalized.search plan bound expected) machine quantum) := by
  obtain ⟨phase, current, program, states, receipts⟩ := machine
  have resumed := Complete.Footprint.ready_rounds scope quantum ready
  cases phase with
  | done => exact ready
  | blocked => exact ready
  | running =>
    unfold RunnerReady
    simp only [Machine.tick, Complete.Normalized.search, Complete.Classes.search]
    cases published : (Complete.Classes.rounds plan bound expected quantum program).log with
    | nil => exact resumed
    | cons receipt rest =>
      exact Complete.Footprint.ready_begin scope
        (Complete.Normalized.target_within plan bound expected receipt footprint
          (resumed.log receipt (by simp [published])))

variable (plan)

@[metta_head "gslt:runner:standard"]
theorem runner_standard_returns (state : State) (pattern : Pattern) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:runner:standard" [encoded (standardTerm plan), patternValue pattern]) state
      (patternValue (Complete.Normalized.standard plan pattern)) := by
  have standard := laws_lifted% ["laws", "extrusions", "pattern"]
    (standard_returns state (Complete.Normalized.laws plan) (Complete.Normalized.extrusions plan) pattern)
  runner_eval [standard] unfolding [standardTerm, Complete.Normalized.standard, lawsValue, extrusionsValue]

@[metta_head "gslt:runner:target"]
theorem runner_target_returns (state : State) (bound : List TypeExpr) (expected : TypeExpr)
    (receipt : GeneralOccurrenceSemantics.Receipt) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:runner:target" [encoded (standardTerm plan), encoded (classReceiptTerm receipt)]) state
      (patternValue ((Complete.Normalized.search plan bound expected).target receipt)) := by
  have standard := runner_standard_returns plan state receipt.target
  runner_eval [standard] unfolding [classReceiptTerm, ScopedRuleJobReadoutExecution.receiptTerm,
    GeneralOccurrenceSemantics.Receipt.target, Complete.Normalized.search]

/-- **A run starts at the source's standard form.** -/
@[metta_head "gslt:runner:begin"]
theorem runner_begin_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (declared : Declared plan footprint) (source : Pattern)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ footprint) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:runner:begin" [planValue plan table bound expected, encoded (standardTerm plan),
        patternValue source])
      state (encoded (classMachineTerm plan
        (Machine.begin (Complete.Normalized.search plan bound expected)
          (Complete.Normalized.standard plan source)))) := by
  have standard := runner_standard_returns plan state source
  have started := runner_lifted% ["plan", "source"]
    (classes_begin_returns plan state table bound expected footprint tabled declared
      (Complete.Normalized.standard plan source)
      (Complete.Normalized.standard_within plan source footprint inside))
  runner_eval [standard, started]
    unfolding [classMachineTerm, Machine.begin, Complete.Normalized.search, Complete.Classes.search,
      Complete.Classes.rounds, classPhaseSymbol, encodeList, patternValue]

@[metta_head "gslt:runner:tick"]
theorem runner_tick_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (scope : Scope plan footprint) (machine : ClassMachine plan)
    (ready : RunnerReady bound expected footprint machine) (quantum : Nat) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:runner:tick" [planValue plan table bound expected, encoded (standardTerm plan),
        encoded (classMachineTerm plan machine), number quantum])
      state (encoded (classMachineTerm plan
        (Machine.tick (Complete.Normalized.search plan bound expected) machine quantum))) := by
  obtain ⟨phase, current, program, states, receipts⟩ := machine
  cases phase with
  | done =>
    runner_eval unfolding [classMachineTerm, classPhaseSymbol, Machine.tick]
  | blocked =>
    runner_eval unfolding [classMachineTerm, classPhaseSymbol, Machine.tick]
  | running =>
    have programReady : ClassReady plan bound expected footprint program := ready
    have resumedReady := Complete.Footprint.ready_rounds scope quantum programReady
    have resumed := runner_lifted% ["plan", "quantum", "program"]
      (classes_rounds_returns plan state table bound expected footprint tabled scope quantum program programReady)
    rcases hresumed : Complete.Classes.rounds plan bound expected quantum program with ⟨round, reps, entries, log⟩
    rw [hresumed] at resumed resumedReady
    cases log with
    | cons receipt rest =>
      have inside := Complete.Normalized.target_within plan bound expected receipt footprint
        (resumedReady.log receipt (by simp))
      have target := runner_target_returns plan state bound expected receipt
      have fresh := runner_lifted% ["plan", "source"]
        (classes_begin_returns plan state table bound expected footprint tabled scope.declared
          ((Complete.Normalized.search plan bound expected).target receipt) inside)
      runner_eval [resumed, target, fresh]
        unfolding [classMachineTerm, classPhaseSymbol, Machine.tick, Complete.Normalized.search,
          Complete.Classes.search, hresumed, classStateTerm, encodeList, Complete.Classes.rounds, patternValue]
    | nil =>
      have licensed : ∀ entry ∈ entries, KeyLicensed plan bound expected entry.1 := fun entry member =>
        key_licensed_of_ready (resumedReady.entries entry member)
      have done := runner_lifted% ["plan", "entries"]
        (classes_entries_complete_returns plan state table bound expected entries licensed)
      cases finished : entries.all fun entry => entry.2.complete
      · runner_eval [resumed, done]
          unfolding [classMachineTerm, classPhaseSymbol, Machine.tick, Complete.Normalized.search,
            Complete.Classes.search, hresumed, classStateTerm, encodeList, Complete.Classes.status,
            Complete.Classes.complete, finished, Mettapedia.Machines.ResumableSearchRunner.phaseOf]
      · runner_eval [resumed, done]
          unfolding [classMachineTerm, classPhaseSymbol, Machine.tick, Complete.Normalized.search,
            Complete.Classes.search, hresumed, classStateTerm, encodeList, Complete.Classes.status,
            Complete.Classes.complete, finished, Mettapedia.Machines.ResumableSearchRunner.phaseOf]

@[metta_head "gslt:runner:advance"]
theorem runner_advance_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (scope : Scope plan footprint) (quantum : Nat) :
    ∀ (ticks : Nat) (machine : ClassMachine plan), RunnerReady bound expected footprint machine →
      PureReturns runnerLibrary.runtime [] state
        (apply "gslt:runner:advance" [planValue plan table bound expected, encoded (standardTerm plan),
          number ticks, number quantum, encoded (classMachineTerm plan machine)])
        state (encoded (classMachineTerm plan
          (Machine.advance (Complete.Normalized.search plan bound expected) ticks quantum machine)))
  | 0, machine, _ => by
    runner_eval unfolding [Machine.advance]
  | ticks + 1, machine, ready => by
    have once := runner_tick_returns plan state table bound expected footprint tabled scope machine ready quantum
    have later := runner_advance_returns state table bound expected footprint tabled scope quantum ticks
      (Machine.tick (Complete.Normalized.search plan bound expected) machine quantum)
      (runner_ready_tick scope ready quantum)
    runner_eval [once, later] unfolding [Machine.advance]

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
