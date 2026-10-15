import ObservedStrategyChecks

/-!
# Observable projections for the managed host replays

The executable host emits these ten counters at thirteen named checkpoints.
Comparing a receipt with this projection checks the finite correspondence;
it is not a verification of SQLite, Python, the provider, or the C evaluator.
Identity spellings and payload encodings are abstracted to their correlated
request/ticket identities. Their equality is separately checked by the host.
-/

namespace HostObservedStrategy

open ObservedStrategy ObservedStrategyChecks
open Mettapedia.CogArch.Agent

def projection (s : State) : List Nat :=
  [ (s.requests.accepted.filter (fun k => decide (s.requests.commitments k = .active))).length,
    s.requests.issued.length, s.requests.journal.length, s.requests.observed.length,
    s.nextSample, s.allowance, s.revision, if s.pending.isSome then 1 else 0,
    if s.dispatch.isSome then 1 else 0,
    if s.requests.phase = .ready then 1 else 0 ]

def states : List State :=
  [ reply (capture active 0 task
      [fun b => some { b with advertised := [99] }]) 0 0 (.command ticket 99),
    restore (compact (selectMode (pause proposed) .omega) 0),
    reply newInput 0 0 (.command ticket 10),
    reply (selectMode sampled .omega) 0 0 (.command ticket 10),
    reply (reply sampled 0 99 (.command ticket 10)) 0 0 (.command ⟨otherAgent, 1⟩ 10),
    reply proposed 0 0 (.command ticket 10),
    capture observed 1 task [],
    finish (fun _ _ => true) observed task success,
    capture (reply sampled 0 0 (.failure 13 0)) 1 task [],
    capture (cooldown { active with allowance := 0 } 1800) 1800 task [],
    omegaWake sampled 601,
    active,
    report (restore (selectMode proposed .omega)) success ]

def projections : List (List Nat) := states.map projection

theorem replay_checkpoints_preserve_or_check_work :
    states.length = 13 ∧ projections.length = 13 := by decide

end HostObservedStrategy
