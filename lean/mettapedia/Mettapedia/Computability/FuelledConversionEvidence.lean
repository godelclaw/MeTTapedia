import Mettapedia.GSLT.LanguageDef.EffectiveKernelSearch
import Mettapedia.Computability.UniversalEffectiveEvidence
import Mettapedia.GSLT.LanguageDef.ProofSystems
import Mettapedia.Machines.ExecutionHints

/-!
# Completed results and exhaustion of finite-code checking

This module observes the actual `Nat.Partrec.Code.evaln` interpreter. Output one
denotes acceptance; another completed output denotes refusal. Exhaustion makes
neither claim. The evaluator bound is not an original-machine clock, a Lean
heartbeat count, or a bound on the running time of evaluating `evaln`.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.FuelledConversionEvidence
open Nat.Partrec (Code)
open Mettapedia.GSLT.LanguageDef

inductive Observation where
  | exhausted
  | accepted
  | refused (output : Nat)
  deriving DecidableEq, Repr

def completed (output : Nat) : Observation :=
  if output = 1 then .accepted else .refused output

def observe (code : Code) (bound input : Nat) : Observation :=
  match code.evaln bound input with
  | none => .exhausted
  | some output => completed output

theorem observe_of_result (code : Code) (bound input output : Nat)
    (result : code.evaln bound input = some output) : observe code bound input = completed output := by
  simp only [observe, result]

theorem accepted_iff (code : Code) (bound input : Nat) :
    observe code bound input = .accepted ↔ code.evaln bound input = some 1 := by
  cases result : code.evaln bound input with
  | none => simp [observe, result]
  | some output =>
      by_cases same : output = 1 <;> simp [observe, result, completed, same]

theorem refused_iff (code : Code) (bound input output : Nat) :
    observe code bound input = .refused output ↔ output ≠ 1 ∧ code.evaln bound input = some output := by
  cases result : code.evaln bound input with
  | none => simp [observe, result]
  | some actual =>
      by_cases same : actual = 1
      · simp [observe, result, completed, same, eq_comm]
      · simp only [observe, result, completed, if_neg same, Observation.refused.injEq, Option.some.injEq]
        constructor
        · intro equality
          exact ⟨by simpa only [← equality] using same, equality⟩
        · exact fun evidence => evidence.2

theorem exhausted_iff (code : Code) (bound input : Nat) :
    observe code bound input = .exhausted ↔ code.evaln bound input = none := by
  cases result : code.evaln bound input with
  | none => simp [observe, result]
  | some actual =>
      by_cases same : actual = 1 <;> simp [observe, result, completed, same]

theorem accepted_sound (code : Code) (bound input : Nat)
    (accepted : observe code bound input = .accepted) : 1 ∈ code.eval input :=
  Code.evaln_sound (by simpa only [Option.mem_def] using (accepted_iff code bound input).mp accepted)

theorem refused_sound (code : Code) (bound input output : Nat)
    (refused : observe code bound input = .refused output) :
    output ≠ 1 ∧ output ∈ code.eval input := by
  obtain ⟨different, result⟩ := (refused_iff code bound input output).mp refused
  exact ⟨different, Code.evaln_sound (by simpa only [Option.mem_def] using result)⟩

theorem result_mono (code : Code) (input first second output : Nat)
    (increased : first ≤ second) (result : code.evaln first input = some output) :
    code.evaln second input = some output := by
  exact Code.evaln_mono increased result

theorem accepted_mono (code : Code) (input first second : Nat)
    (increased : first ≤ second) (accepted : observe code first input = .accepted) :
    observe code second input = .accepted :=
  (accepted_iff code second input).mpr (result_mono code input first second 1 increased
    ((accepted_iff code first input).mp accepted))

theorem refused_mono (code : Code) (input first second output : Nat)
    (increased : first ≤ second) (refused : observe code first input = .refused output) :
    observe code second input = .refused output := by
  obtain ⟨different, result⟩ := (refused_iff code first input output).mp refused
  exact (refused_iff code second input output).mpr
    ⟨different, result_mono code input first second output increased result⟩

/-- Eventual completeness is for the exact partial program, including completed
refusals. No termination theorem for that program is assumed. -/
theorem eventual_result (code : Code) (input output : Nat) (result : output ∈ code.eval input) :
    ∃ bound, ∀ later, bound ≤ later → observe code later input = completed output := by
  obtain ⟨bound, evaluated⟩ := Code.evaln_complete.mp result
  refine ⟨bound, fun later increased => ?_⟩
  exact observe_of_result code later input output
    (result_mono code input bound later output increased evaluated)

theorem eventual_accepted_iff (code : Code) (input : Nat) :
    (∃ bound, observe code bound input = .accepted) ↔ 1 ∈ code.eval input := by
  constructor
  · rintro ⟨bound, accepted⟩
    exact accepted_sound code bound input accepted
  · intro accepted
    obtain ⟨bound, evaluated⟩ := Code.evaln_complete.mp accepted
    exact ⟨bound, (accepted_iff code bound input).mpr evaluated⟩

theorem clockedCheck_iff (code : Code) (claim certificate bound : Nat) :
    EffectiveKernelSearch.clockedCheck code claim (certificate, bound) = true ↔
      observe code bound (Nat.pair claim certificate) = .accepted := by
  simp only [EffectiveKernelSearch.clockedCheck, decide_eq_true_eq, accepted_iff]

theorem universalEvidence_iff (code : Code) (input bound : Nat) :
    UniversalEffectiveEvidence.check code input 1 bound = true ↔ observe code bound input = .accepted := by
  simp only [UniversalEffectiveEvidence.check, decide_eq_true_eq, Option.mem_def, accepted_iff]

namespace Controls

theorem exhausted_small_bound : observe .right 0 (Nat.pair 0 1) = .exhausted := by
  simp [observe, Code.evaln]

theorem accepted_larger_bound : observe .right 10 (Nat.pair 0 1) = .accepted := by
  have small : Nat.pair 0 1 ≤ 9 := by decide
  simp [observe, Code.evaln, completed, small, Nat.unpair_pair]

theorem completed_wrong_output : observe .right 10 (Nat.pair 0 2) = .refused 2 := by
  have small : Nat.pair 0 2 ≤ 9 := by decide
  simp [observe, Code.evaln, completed, small, Nat.unpair_pair]

theorem exhaustion_is_not_refusal : observe .right 0 (Nat.pair 0 1) ≠ .refused 0 := by
  simp [exhausted_small_bound]

end Controls
end Mettapedia.Computability.FuelledConversionEvidence

namespace Mettapedia.Computability.FuelledConversionEvidence.StrategyChecking

open Mettapedia.GSLT.LanguageDef KernelAuthority ProofSystems
open Mettapedia.Machines.ExecutionHints

universe u v
variable {State : Type u} {View : Type v} [DecidableEq View]

def fuelledChecker (tick : State → State) (view : State → View) : Checker (State × View) Nat where
  check claim budget := decide (view (tick^[budget] claim.1) = claim.2)

def checkpointChecker (tick : State → State) (view : State → View) :
    Checker (State × View) (List (Checkpoint View)) where
  check := check tick view

def traceChecker (tick : State → State) (view : State → View) :
    Checker (State × View) (List (Checkpoint View)) where
  check claim points := points.all (fun point => point.steps == 1) && check tick view claim points

/-- Trace materialization is an edge in the existing elaboration theory,
preserving acceptance and refusal of every supplied fuel value. -/
def fuelledElaboration (tick : State → State) (view : State → View) :
    Elaboration (fuelledChecker tick view) (traceChecker tick view) where
  elaborate claim budget := some (fullTrace tick view claim.1 budget)
  exact claim budget := by
    simp only [fuelledChecker, Option.some.injEq]
    have unit : (fullTrace tick view claim.1 budget).all (fun point => point.steps == 1) = true := by
      exact List.all_eq_true.mpr (fun point member => by
        simpa using fullTrace_unit tick view claim.1 budget point member)
    simp [traceChecker, unit, check_fullTrace]

/-- Full trace expansion preserves the actual endpoint and tick-call count.
Checkpoints alone do not make the intervening computation cheaper. -/
theorem expand_checked (tick : State → State) (view : State → View)
    (claim : State × View) (points : List (Checkpoint View))
    (accepted : check tick view claim points = true) :
    (traceChecker tick view).check claim (fullTrace tick view claim.1 (fuel points)) = true ∧
      (fullTrace tick view claim.1 (fuel points)).length =
        (replay tick view claim.1 points).1 := by
  have reached := check_sound tick view claim points accepted
  have unit := fullTrace_unit tick view claim.1 (fuel points)
  constructor
  · change (_ && check tick view claim (fullTrace tick view claim.1 (fuel points))) = true
    rw [Bool.and_eq_true]
    constructor
    · exact List.all_eq_true.mpr (fun point member => by simpa using unit point member)
    · rw [check_fullTrace]
      simpa only [decide_eq_true_eq] using reached
  · obtain ⟨target, replayed, _⟩ := Option.map_eq_some_iff.mp (of_decide_eq_true accepted)
    rw [fullTrace_length, (replay_result tick view points claim.1 target replayed).2]

end Mettapedia.Computability.FuelledConversionEvidence.StrategyChecking
