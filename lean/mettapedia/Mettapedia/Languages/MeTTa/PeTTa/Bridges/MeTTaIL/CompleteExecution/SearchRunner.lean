import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.RunnerSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Positions
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.SearchWire
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgeEval

/-!
# The native runner for a certified search realization

The five operations are those of `ResumableSearchRunner.Search`. This module
records their wire correspondence and the domain on which that correspondence
holds. The driver proof uses those operations without inspecting search states
or receipts. Readiness closure is explicit; operational coverage of a source
calculus remains a separate obligation.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.SearchRunner

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Machines.ResumableSearchRunner (Search Status Phase Machine phaseOf)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval BridgeKit WireKit

def statusAtom : Status → Atom
  | .complete => .symbol "SearchComplete"
  | .blocked => .symbol "SearchBlocked"
  | .pending => .symbol "SearchPending"

variable {Run Receipt : Type}

/-- A representation and its five computations, qualified by the source,
retained-run and receipt invariants required by that representation. -/
structure Realization (search : Search Pattern Run Receipt) where
  lawful : search.Lawful
  stable : Complete.Settled.Stable search
  backend : Atom
  plan : Atom
  standard : Atom
  runTerm : Run → Term
  receiptTerm : Receipt → Term
  SourceReady : Pattern → Prop
  RunReady : Run → Prop
  ReceiptReady : Receipt → Prop
  run_ready : ∀ source, SourceReady source → ∀ work, RunReady (search.run source work)
  resume_ready : ∀ run, RunReady run → ∀ work, RunReady (search.resume run work)
  publication_ready : ∀ run, RunReady run →
    ∀ receipt ∈ search.publication run, ReceiptReady receipt
  target_ready : ∀ receipt, ReceiptReady receipt → SourceReady (search.target receipt)
  run_returns : ∀ state source, SourceReady source → ∀ work,
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:search:run" [backend, plan, patternValue source, number work])
      state (encoded (runTerm (search.run source work)))
  resume_returns : ∀ state run, RunReady run → ∀ work,
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:search:resume" [backend, plan, encoded (runTerm run), number work])
      state (encoded (runTerm (search.resume run work)))
  publication_returns : ∀ state run,
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:search:publication" [backend, encoded (runTerm run)])
      state (encoded (encodeList receiptTerm (search.publication run)))
  status_returns : ∀ state run, RunReady run →
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:search:status" [backend, plan, encoded (runTerm run)])
      state (statusAtom (search.status run))
  target_returns : ∀ state receipt, ReceiptReady receipt →
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:search:target" [backend, standard, encoded (receiptTerm receipt)])
      state (patternValue (search.target receipt))

variable {search : Search Pattern Run Receipt}

abbrev Realization.machineTerm (realization : Realization search)
    (machine : Machine Pattern Run Receipt) : Term :=
  SearchWire.machineTerm realization.runTerm realization.receiptTerm machine

def Ready (realization : Realization search) (machine : Machine Pattern Run Receipt) : Prop :=
  realization.RunReady machine.program

theorem tick_ready (realization : Realization search) (machine : Machine Pattern Run Receipt)
    (ready : Ready realization machine) (quantum : Nat) :
    Ready realization (Machine.tick search machine quantum) := by
  obtain ⟨phase, source, run, states, receipts⟩ := machine
  cases phase with
  | done => exact ready
  | blocked => exact ready
  | running =>
      have resumed := realization.resume_ready run ready quantum
      unfold Ready Machine.tick
      dsimp only
      cases published : search.publication (search.resume run quantum) with
      | nil => exact resumed
      | cons receipt rest =>
          exact realization.run_ready _ (realization.target_ready receipt
            (realization.publication_ready _ resumed receipt (by simp [published]))) 0

syntax "search_runner_eval" (" [" term,* "]")?
    (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| search_runner_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic|
      (metta_call_in runnerProof_checked using runnerProof_agreement
       metta_eval [$facts,*] with runnerProof_checked in runnerProof_agreement
         unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil,
           Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
           Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
           Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
           Realization.machineTerm, SearchWire.machineTerm, SearchWire.phaseSymbol,
           encodeList, $extra,*]))

/-- Preparing the initial source and starting the selected search realizes
the generic machine's `begin`; the source preparation is independently proved. -/
theorem begin_returns (realization : Realization search) (state : Effects.State)
    (source start : Pattern) (ready : realization.SourceReady start)
    (prepared : PureReturns runnerLibrary.runtime [] state
      (apply "gslt:runner:standard" [realization.standard, patternValue source])
      state (patternValue start)) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:runner:begin"
        [realization.backend, realization.plan, realization.standard, patternValue source])
      state (encoded (realization.machineTerm (Machine.begin search start))) := by
  have started := realization.run_returns state start ready 0
  search_runner_eval [prepared, started] unfolding [Machine.begin]

/-- A native tick executes the same commit/resume decision for every realization. -/
theorem tick_returns (realization : Realization search) (state : Effects.State)
    (machine : Machine Pattern Run Receipt) (ready : Ready realization machine)
    (quantum : Nat) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:runner:tick"
        [realization.backend, realization.plan, realization.standard,
          encoded (realization.machineTerm machine), number quantum])
      state (encoded (realization.machineTerm (Machine.tick search machine quantum))) := by
  obtain ⟨phase, source, run, states, receipts⟩ := machine
  cases phase with
  | done => search_runner_eval unfolding [Machine.tick]
  | blocked => search_runner_eval unfolding [Machine.tick]
  | running =>
      have nextReady := realization.resume_ready run ready quantum
      have resumed := realization.resume_returns state run ready quantum
      have published := realization.publication_returns state (search.resume run quantum)
      cases publication : search.publication (search.resume run quantum) with
      | cons receipt rest =>
          rw [publication] at published
          have receiptReady := realization.publication_ready _ nextReady receipt
            (by simp [publication])
          have target := realization.target_returns state receipt receiptReady
          have fresh := realization.run_returns state (search.target receipt)
            (realization.target_ready receipt receiptReady) 0
          search_runner_eval [resumed, published, target, fresh]
            unfolding [Machine.tick, publication]
      | nil =>
          rw [publication] at published
          have status := realization.status_returns state (search.resume run quantum) nextReady
          cases finished : search.status (search.resume run quantum) <;>
            simp only [finished, statusAtom] at status <;>
            search_runner_eval [resumed, published, status]
              unfolding [Machine.tick, publication, finished, phaseOf]

theorem advance_returns (realization : Realization search) (state : Effects.State)
    (quantum : Nat) :
    ∀ (ticks : Nat) (machine : Machine Pattern Run Receipt), Ready realization machine →
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:runner:advance"
        [realization.backend, realization.plan, realization.standard,
          number ticks, number quantum, encoded (realization.machineTerm machine)])
      state (encoded (realization.machineTerm (Machine.advance search ticks quantum machine)))
  | 0, machine, _ => by
      search_runner_eval unfolding [Machine.advance]
  | ticks + 1, machine, ready => by
      have once := tick_returns realization state machine ready quantum
      have later := advance_returns realization state quantum ticks
        (Machine.tick search machine quantum) (tick_ready realization machine ready quantum)
      search_runner_eval [once, later] unfolding [Machine.advance]

theorem reverse_onto_returns (state : Effects.State) : ∀ (items tail : List Term),
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:runner:reverse-onto" [terms items, terms tail])
      state (terms (items.reverseAux tail))
  | [], tail => by search_runner_eval unfolding [terms, List.reverseAux]
  | item :: rest, tail => by
      have later := reverse_onto_returns state rest (item :: tail)
      search_runner_eval [later] unfolding [terms, List.reverseAux]

theorem trace_returns (realization : Realization search) (state : Effects.State)
    (machine : Machine Pattern Run Receipt) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:runner:trace" [encoded (realization.machineTerm machine)])
      state (encoded (SearchWire.traceTerm machine)) := by
  obtain ⟨phase, current, program, states, receipts⟩ := machine
  have reversed := reverse_onto_returns state (states.map InferenceCettaWire.encodePattern) []
  rw [List.reverseAux_eq, List.append_nil, ← List.map_reverse, ← terms_map, ← terms_map] at reversed
  cases phase <;>
    search_runner_eval [reversed]
      unfolding [SearchWire.traceTerm]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.SearchRunner
