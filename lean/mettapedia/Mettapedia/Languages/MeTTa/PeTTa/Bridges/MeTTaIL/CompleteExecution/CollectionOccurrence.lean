import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.SearchRunner

/-!
# Retained collection occurrences in the shared search dictionary

The descriptor selects the existing occurrence search operations. Its
representation and readiness proofs fill the same realization used by the
generic runner, explorer and graph readout. Source coverage and permission to
select this descriptor during emission remain separate admission obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.CollectionOccurrence

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr} {expected : TypeExpr}

def backendTerm (names : List String) (depth : Nat) : Term :=
  .application "CollectionOccurrenceSearch" [encodeList Term.string names, .natural depth]

syntax "occurrence_runner_eval" (" [" term,* "]")?
    (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| occurrence_runner_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call runner_checked; metta_eval [$facts,*] with runner_checked
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?, backendTerm, $extra,*]))

@[metta_head "gslt:search:run"]
theorem run_returns (host : Effects.State) (names : List String) (named : StandardWire.TableFor plan names)
    (footprint : List String) (scope : Complete.Footprint.Scope plan footprint)
    (admitted : ∀ declaration ∈ plan.rules,
      RuleBinding.admittedFor declaration.rule declaration.binding.spec = true)
    (depth : Nat) (input : Pattern) (checked : Complete.Classes.Checked plan bound expected input)
    (work : Nat) :
    PureReturns runnerLibrary.runtime [] host
      (apply "gslt:search:run"
        [encoded (backendTerm names depth),
          encoded (CompletePlanWire.planTerm plan (plan.snapshot.free.entriesOn footprint) bound expected),
          patternValue input, number work])
      host (encoded (CollectionOccurrenceSearchExecution.runTerm (plan.snapshot.free.entriesOn footprint)
        ((CollectionOccurrenceSearch.search plan bound expected depth).run input work))) := by
  have typed := CanonicalBags.openPatternWellSorted_canon
    (WellSorted.checkOpenPatternWellSorted_sound checked)
  have begun := CollectionOccurrenceSearchExecution.begin_ready (bound := bound) (expected := expected)
    names named footprint scope.declared admitted (CanonicalBags.canon input) typed.2.1
  have native := CollectionOccurrenceSearchExecution.run_returns host names named.ordered
    footprint scope.declared scope.finite scope.provider depth work input (named.covered checked)
    (Complete.Footprint.sorted_within scope.declared (WellSorted.checkOpenPatternWellSorted_complete typed)) begun
  have executed := by metta_lift runner_checked ["names", "depth", "plan", "source", "work"] native
  occurrence_runner_eval [executed]

@[metta_head "gslt:search:resume"]
theorem resume_returns (host : Effects.State) (names : List String) (named : StandardWire.TableFor plan names)
    (footprint : List String) (scope : Complete.Footprint.Scope plan footprint)
    (depth : Nat) (planData : Atom) (run : CollectionOccurrenceSearch.Run plan bound expected)
    (ready : CollectionOccurrenceSearchExecution.Ready names footprint depth run) (work : Nat) :
    PureReturns runnerLibrary.runtime [] host
      (apply "gslt:search:resume"
        [encoded (backendTerm names depth), planData,
          encoded (CollectionOccurrenceSearchExecution.runTerm (plan.snapshot.free.entriesOn footprint) run),
          number work])
      host (encoded (CollectionOccurrenceSearchExecution.runTerm (plan.snapshot.free.entriesOn footprint)
        ((CollectionOccurrenceSearch.search plan bound expected depth).resume run work))) := by
  have native := CollectionOccurrenceSearchExecution.resume_returns host names named.ordered
    footprint scope.declared scope.finite scope.provider depth work run ready
  have resumed := by metta_lift runner_checked ["names", "depth", "run", "work"] native
  occurrence_runner_eval [resumed]

@[metta_head "gslt:search:publication"]
theorem publication_returns (host : Effects.State) (names : List String) (depth : Nat)
    (table : List (String × TypeExpr)) (run : CollectionOccurrenceSearch.Run plan bound expected) :
    PureReturns runnerLibrary.runtime [] host
      (apply "gslt:search:publication"
        [encoded (backendTerm names depth), encoded (CollectionOccurrenceSearchExecution.runTerm table run)])
      host (encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm
        ((CollectionOccurrenceSearch.search plan bound expected depth).publication run))) := by
  have native := CollectionOccurrenceSearchExecution.publication_returns host table run depth
  have published := by metta_lift runner_checked ["run"] native
  occurrence_runner_eval [published]

@[metta_head "gslt:search:status"]
theorem status_returns (host : Effects.State) (names : List String) (depth : Nat) (planData : Atom)
    (table : List (String × TypeExpr)) (run : CollectionOccurrenceSearch.Run plan bound expected) :
    PureReturns runnerLibrary.runtime [] host
      (apply "gslt:search:status"
        [encoded (backendTerm names depth), planData, encoded (CollectionOccurrenceSearchExecution.runTerm table run)])
      host (SearchRunner.statusAtom (CollectionOccurrenceSearch.status run)) := by
  have native := CollectionOccurrenceSearchExecution.status_returns host table run
  have status := by metta_lift runner_checked ["run"] native
  occurrence_runner_eval [status] unfolding
    [SearchRunner.statusAtom, CollectionOccurrenceSearchExecution.statusAtom]

@[metta_head "gslt:search:target"]
theorem target_returns (host : Effects.State) (names : List String) (named : StandardWire.TableFor plan names)
    (depth : Nat) (standard : Atom) (receipt : GeneralRuleJobs.Receipt)
    (checked : Complete.Classes.Checked plan bound expected receipt.target) :
    PureReturns runnerLibrary.runtime [] host
      (apply "gslt:search:target" [encoded (backendTerm names depth), standard,
        encoded (ScopedRuleJobReadoutExecution.receiptTerm receipt)])
      host (patternValue (CanonicalBags.canon receipt.target)) := by
  have native := CollectionOccurrenceSearchExecution.target_returns host names named.ordered
    receipt (named.covered checked)
  have target := by metta_lift runner_checked ["names", "receipt"] native
  occurrence_runner_eval [target]

def realization (names : List String) (named : StandardWire.TableFor plan names)
    (footprint : List String) (scope : Complete.Footprint.Scope plan footprint)
    (admitted : ∀ declaration ∈ plan.rules,
      RuleBinding.admittedFor declaration.rule declaration.binding.spec = true)
    (depth : Nat) :
    SearchRunner.Realization (CollectionOccurrenceSearch.search plan bound expected depth) where
  lawful := CollectionOccurrenceSearch.search_lawful plan bound expected depth
  stable := CollectionOccurrenceSearch.search_stable plan bound expected depth
  backend := encoded (backendTerm names depth)
  plan := encoded (CompletePlanWire.planTerm plan (plan.snapshot.free.entriesOn footprint) bound expected)
  standard := encoded (.application "Canonical" [.symbol "LNil", .symbol "LNil", encodeList Term.string names])
  runTerm := CollectionOccurrenceSearchExecution.runTerm (plan.snapshot.free.entriesOn footprint)
  receiptTerm := ScopedRuleJobReadoutExecution.receiptTerm
  SourceReady := Complete.Classes.Checked plan bound expected
  RunReady := CollectionOccurrenceSearchExecution.Ready names footprint depth
  ReceiptReady receipt := Complete.Classes.Checked plan bound expected receipt.target
  run_ready input checked work := CollectionOccurrenceSearchExecution.run_ready
    names named footprint scope admitted depth input checked work
  resume_ready run ready work := CollectionOccurrenceSearchExecution.resume_ready
    names footprint scope.finite scope.provider depth run ready work
  publication_ready run ready _ member :=
    CollectionOccurrenceSearchExecution.publication_checked names footprint depth run ready member
  target_ready _ checked := WellSorted.checkOpenPatternWellSorted_complete
    (CanonicalBags.openPatternWellSorted_canon (WellSorted.checkOpenPatternWellSorted_sound checked))
  run_returns host input checked work := run_returns host names named footprint scope admitted depth input checked work
  resume_returns host run ready work := resume_returns host names named footprint scope depth _ run ready work
  publication_returns host run := publication_returns host names depth _ run
  status_returns host run _ := status_returns host names depth _ _ run
  target_returns host receipt checked := target_returns host names named depth _ receipt checked

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.CollectionOccurrence
