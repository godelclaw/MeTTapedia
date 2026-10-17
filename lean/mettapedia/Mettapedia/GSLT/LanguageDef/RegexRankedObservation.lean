import Mettapedia.GSLT.LanguageDef.RegexObservationTrace

/-!
# Earned structural admission for nested observations

This rank-fenced reference derives its assertion-depth allowance from the
admitted program certificate. A user work budget is not an assertion-depth
argument. Ordinary execution cannot leave the caller's admitted rank region;
each observation body starts strictly below it. The intrinsic-call kernel in
`RegexObservationKernel` has a separate certificate-independence theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexRankedObservation

open Mettapedia.Computability.RegularLanguages
open RegexDependentObservation
open RegexObservationTrace (ObservedAction)

def actionTargets {α : Type} : ObservedAction α → List α
  | .accept | .dead => []
  | .next target _ => [target]
  | .branch first second => [first, second]

theorem observed_targets_authorized {states groups length : Nat}
    (interpretation : Interpretation) (input : Fin length → Nat) (direction : Direction)
    (program : Fin states → Instruction states groups)
    (body : LookKind → Fin states → Configuration states groups length → Option (Winner states groups length))
    (first last : Configuration states groups length)
    (edge : last ∈ actionTargets
      (RegexObservationTrace.observedAction interpretation input direction program body first)) :
    last.pc ∈ ordinaryTargets (program first.pc) := by
  cases instruction : program first.pc with
  | accept | dead =>
      simp [RegexObservationTrace.observedAction, action, instruction, actionTargets] at edge
  | jump next | branch left right | «open» group next | close group next =>
      simp_all [RegexObservationTrace.observedAction, action, actionTargets, ordinaryTargets]
      all_goals rcases edge with rfl | rfl <;> simp
  | consume contains next =>
      cases read : consumed input direction first.position <;>
        cases moved : advance direction first.position
      all_goals simp only [RegexObservationTrace.observedAction, instruction, action, read, moved] at edge
      all_goals try split_ifs at edge
      all_goals simp_all [actionTargets, ordinaryTargets]
  | assertion holds next =>
      cases allowed : holds first.position <;>
        simp_all [RegexObservationTrace.observedAction, action, actionTargets, ordinaryTargets]
  | backref group comparison next =>
      cases recalled : backreference interpretation input direction comparison first.captures group first.position <;>
        simp_all [RegexObservationTrace.observedAction, action, actionTargets, ordinaryTargets]
  | look kind entry next =>
      cases negative : kind.negative <;> cases selected : body kind entry first <;>
        simp_all [RegexObservationTrace.observedAction, RegexObservationTrace.observedLook, actionTargets, ordinaryTargets]

theorem observed_target_rank {states groups length : Nat}
    (interpretation : Interpretation) (input : Fin length → Nat) (direction : Direction)
    (program : RankedProgram states groups)
    (body : LookKind → Fin states → Configuration states groups length → Option (Winner states groups length))
    (first last : Configuration states groups length)
    (edge : last ∈ actionTargets
      (RegexObservationTrace.observedAction interpretation input direction program.instruction body first)) :
    program.rank last.pc ≤ program.rank first.pc :=
  program.ordinary first.pc last.pc
    (observed_targets_authorized interpretation input direction program.instruction body first last edge)

def nodeTargets {α : Type} : RegexTaggedGraph.Node α Unit Unit Unit → List α
  | .accept _ | .dead => []
  | .jump next | .save _ next | .consume _ next | .assertion _ next => [next]
  | .choice first second => [first, second]

def stateRank {states groups length bound : Nat} (program : RankedProgram states groups) :
    RegexObservationTrace.State (Configuration states groups length) bound → Nat
  | .main configuration | .spool configuration _ => program.rank configuration.pc
  | .dead => 0

theorem expanded_target_rank {states groups length : Nat}
    (program : RankedProgram states groups)
    (step : Configuration states groups length → ObservedAction (Configuration states groups length))
    (nonincreasing : ∀ first last, last ∈ actionTargets (step first) →
      program.rank last.pc ≤ program.rank first.pc)
    (first last : RegexObservationTrace.State (Configuration states groups length) (RegexObservationTrace.maxWord step))
    (edge : last ∈ nodeTargets (RegexObservationTrace.graph step first)) :
    stateRank program last ≤ stateRank program first := by
  cases first with
  | dead => simp [RegexObservationTrace.graph, nodeTargets] at edge
  | main configuration =>
      cases instruction : step configuration with
      | accept | dead => simp [RegexObservationTrace.graph, instruction, nodeTargets] at edge
      | next target bits =>
          simp [RegexObservationTrace.graph, instruction, nodeTargets] at edge
          subst last
          exact le_refl _
      | branch left right =>
          simp [RegexObservationTrace.graph, instruction, nodeTargets] at edge
          rcases edge with rfl | rfl
          · exact nonincreasing configuration left (by simp [instruction, actionTargets])
          · exact nonincreasing configuration right (by simp [instruction, actionTargets])
  | spool origin index =>
      cases instruction : step origin with
      | accept | dead | branch _ _ => simp [RegexObservationTrace.graph, instruction, nodeTargets] at edge
      | next target bits =>
          simp only [RegexObservationTrace.graph, instruction] at edge
          split at edge
          · split at edge <;> simp only [nodeTargets, List.mem_cons, List.not_mem_nil, or_false] at edge
            all_goals rcases edge with rfl | rfl <;> simp [stateRank]
          · simp only [nodeTargets, List.mem_singleton] at edge
            subst last
            exact nonincreasing origin target (by simp [instruction, actionTargets])

theorem reachable_rank {states groups length : Nat}
    (program : RankedProgram states groups)
    (step : Configuration states groups length → ObservedAction (Configuration states groups length))
    (nonincreasing : ∀ first last, last ∈ actionTargets (step first) →
      program.rank last.pc ≤ program.rank first.pc)
    (first last : RegexObservationTrace.State (Configuration states groups length) (RegexObservationTrace.maxWord step))
    (path : Relation.ReflTransGen (fun first last =>
      last ∈ nodeTargets (RegexObservationTrace.graph step first)) first last) :
    stateRank program last ≤ stateRank program first := by
  induction path with
  | refl => exact le_refl _
  | tail path edge ih => exact (expanded_target_rank program step nonincreasing _ _ edge).trans ih

theorem caller_fence_cannot_truncate_reachable_code {states groups length : Nat}
    (program : RankedProgram states groups)
    (step : Configuration states groups length → ObservedAction (Configuration states groups length))
    (nonincreasing : ∀ first last, last ∈ actionTargets (step first) →
      program.rank last.pc ≤ program.rank first.pc)
    (first last : Configuration states groups length)
    (path : Relation.ReflTransGen (fun source target =>
      target ∈ nodeTargets (RegexObservationTrace.graph step source)) (.main first) (.main last)) :
    program.rank last.pc < program.rank first.pc + 1 := by
  have bounded := reachable_rank program step nonincreasing _ _ path
  change program.rank last.pc ≤ program.rank first.pc at bounded
  omega

private def evaluateAtRank {states groups length : Nat}
    (interpretation : Interpretation) (input : Fin length → Nat)
    (program : RankedProgram states groups) (rank : Nat) : Evaluator states groups length :=
  fun direction eligible first =>
    let recursive : Evaluator states groups length := fun direction eligible first =>
      if _smaller : program.rank first.pc < rank then
        evaluateAtRank interpretation input program (program.rank first.pc) direction eligible first
      else none
    let body := bodyWinner recursive
    RegexObservationTrace.complete
      (RegexObservationTrace.observedAction interpretation input direction program.instruction body) eligible first
termination_by rank

/-- Canonical admitted reference entry. Its recursive argument is the actual
program rank, not a caller-selected allowance. Rank zero still executes the
entire ordinary graph; only nested observations recurse on smaller ranks. -/
def evaluate {states groups length : Nat}
    (interpretation : Interpretation) (input : Fin length → Nat)
    (program : RankedProgram states groups) (direction : Direction)
    (eligible : Configuration states groups length → Bool)
    (first : Configuration states groups length) : Option (Winner states groups length) :=
  evaluateAtRank interpretation input program (program.rank first.pc) direction eligible first

theorem initial_fence_is_admitted {states groups length : Nat}
    (program : RankedProgram states groups) (first : Configuration states groups length) :
    program.rank first.pc < program.rank first.pc + 1 := Nat.lt_succ_self _

theorem body_fence_is_admitted {states groups : Nat} (program : RankedProgram states groups)
    (pc entry next : Fin states) (kind : LookKind)
    (instruction : program.instruction pc = .look kind entry next) :
    program.rank entry + 1 ≤ program.rank pc := by
  have lower := program.body pc kind entry next instruction
  omega

theorem recursive_call_is_admitted {states groups length : Nat}
    (program : RankedProgram states groups)
    (first caller : Configuration states groups length) (kind : LookKind) (entry next : Fin states)
    (ordinary : program.rank caller.pc ≤ program.rank first.pc)
    (observation : program.instruction caller.pc = .look kind entry next) :
    program.rank entry < program.rank first.pc :=
  lt_of_lt_of_le (program.body caller.pc kind entry next observation) ordinary

namespace Controls

private def interpretation : Interpretation := ⟨id⟩
private def emptyInput : Fin 0 → Nat := Fin.elim0

private def accepts : RankedProgram 1 0 where
  instruction := fun _ => .accept
  rank := fun _ => 0
  ordinary := by intro pc next edge; simp [ordinaryTargets] at edge
  body := by intro pc kind entry next equation; cases equation

private def jumps : RankedProgram 2 0 where
  instruction := fun pc => if pc.val = 0 then .jump 1 else .accept
  rank := fun _ => 0
  ordinary := by intros; exact le_refl _
  body := by
    intro pc kind entry next equation
    split at equation <;> cases equation

private def rejects : RankedProgram 1 0 where
  instruction := fun _ => .dead
  rank := fun _ => 0
  ordinary := by intro pc next edge; simp [ordinaryTargets] at edge
  body := by intro pc kind entry next equation; cases equation

theorem rank_zero_executes_acceptance :
    (evaluate interpretation emptyInput accepts .forward (fun _ => true) ⟨0, 0, Fin.elim0⟩).isSome = true := by
  simp [evaluate, evaluateAtRank, RegexObservationTrace.complete, RegexObservationTrace.run,
    RegexObservationTrace.initial, RegexObservationTrace.fuel, RegexMemoizedSearch.taggedSearch,
    RegexMemoizedSearch.search, RegexSelectionCorrespondence.action, RegexObservationTrace.graph,
    RegexObservationTrace.observedAction, action, accepts, RegexObservationTrace.mainEligible]

theorem rank_zero_executes_an_ordinary_continuation :
    (evaluate interpretation emptyInput jumps .forward (fun _ => true) ⟨0, 0, Fin.elim0⟩).isSome = true := by
  let body : LookKind → Fin 2 → Configuration 2 0 0 → Option (Winner 2 0 0) :=
    bodyWinner (fun _ _ _ => none)
  let step := RegexObservationTrace.observedAction interpretation emptyInput .forward jumps.instruction body
  let first : Configuration 2 0 0 := ⟨0, 0, Fin.elim0⟩
  simp only [evaluate, evaluateAtRank, jumps, Nat.lt_irrefl, ↓reduceDIte]
  change (RegexObservationTrace.complete step (fun _ => true) first).isSome = true
  rw [Option.isSome_iff_ne_none]
  intro absent
  apply (RegexObservationTrace.complete_none_iff step (fun _ => true) first).mp absent
  let initial := RegexObservationTrace.initial step first
  let middle := initial.at (.spool first 0)
  let final := middle.at (.main ⟨1, 0, Fin.elim0⟩)
  refine ⟨[], [initial.point, middle.point, final.point], final, (), ?_⟩
  exact .next (by rfl) (.next (by rfl) (.done (by rfl) (by rfl)))

theorem rank_zero_does_not_invent_acceptance :
    (evaluate interpretation emptyInput rejects .forward (fun _ => true) ⟨0, 0, Fin.elim0⟩).isSome = false := by
  simp [evaluate, evaluateAtRank, RegexObservationTrace.complete, RegexObservationTrace.run,
    RegexObservationTrace.initial, RegexObservationTrace.fuel, RegexMemoizedSearch.taggedSearch,
    RegexMemoizedSearch.search, RegexSelectionCorrespondence.action, RegexObservationTrace.graph,
    RegexObservationTrace.observedAction, action, rejects]

end Controls

end Mettapedia.GSLT.LanguageDef.RegexRankedObservation
