import Mettapedia.GSLT.LanguageDef.RegexRankedObservation
import Mettapedia.GSLT.LanguageDef.RegexOrdinaryReachability

/-!
# Certificate-independent observation recursion

The recursive-call relation is determined by ordinary instruction reachability
followed by an observation entry. A rank assignment proves that this relation
is well founded; it is not part of the regex observation itself. Matching is
performed on the actual ordinary-reachable configuration subgraph, so each
recursive call carries its control-flow license.

`RegexRankedObservation.evaluate` is the earlier rank-fenced reference. Its
equivalence to this intrinsic-call kernel is a separate transport obligation;
the certificate-independence theorem below concerns this kernel itself.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexObservationKernel

open Mettapedia.Computability.RegularLanguages
open RegexDependentObservation
open RegexObservationTrace (ObservedAction)

def OrdinaryReach {states groups : Nat} (code : Fin states → Instruction states groups)
    (first last : Fin states) : Prop :=
  Relation.ReflTransGen (fun source target => target ∈ ordinaryTargets (code source)) first last

instance {states groups : Nat} (code : Fin states → Instruction states groups) (first last : Fin states) :
    Decidable (OrdinaryReach code first last) :=
  RegexOrdinaryReachability.decidableReach code first last

/-- This relation depends only on the authored control graph, never on ranks. -/
def DirectBodyCall {states groups : Nat} (code : Fin states → Instruction states groups)
    (entry root : Fin states) : Prop :=
  ∃ caller kind next, OrdinaryReach code root caller ∧ code caller = .look kind entry next

structure Certificate {states groups : Nat} (code : Fin states → Instruction states groups) where
  rank : Fin states → Nat
  ordinary : ∀ pc next, next ∈ ordinaryTargets (code pc) → rank next ≤ rank pc
  body : ∀ pc kind entry next, code pc = .look kind entry next → rank entry < rank pc

def Certificate.ofRanked {states groups : Nat} (program : RankedProgram states groups) :
    Certificate program.instruction := ⟨program.rank, program.ordinary, program.body⟩

theorem ordinary_rank {states groups : Nat} {code : Fin states → Instruction states groups}
    (certificate : Certificate code) {first last : Fin states}
    (path : OrdinaryReach code first last) : certificate.rank last ≤ certificate.rank first := by
  induction path with
  | refl => exact le_refl _
  | tail path edge ih => exact (certificate.ordinary _ _ edge).trans ih

theorem call_rank {states groups : Nat} {code : Fin states → Instruction states groups}
    (certificate : Certificate code) {entry root : Fin states} (called : DirectBodyCall code entry root) :
    certificate.rank entry < certificate.rank root := by
  obtain ⟨caller, kind, next, path, observation⟩ := called
  exact lt_of_lt_of_le (certificate.body caller kind entry next observation) (ordinary_rank certificate path)

theorem calls_wellFounded {states groups : Nat} {code : Fin states → Instruction states groups}
    (certificate : Certificate code) : WellFounded (DirectBodyCall code) :=
  Subrelation.wf (fun called => call_rank certificate called) (measure certificate.rank).wf

abbrev Licensed {states groups : Nat} (code : Fin states → Instruction states groups)
    (length : Nat) (root : Fin states) :=
  { configuration : Configuration states groups length // OrdinaryReach code root configuration.pc }

instance {states groups length : Nat} (code : Fin states → Instruction states groups)
    (root : Fin states) : Fintype (Licensed code length root) := inferInstance

abbrev Observation (states groups length : Nat) :=
  Direction → (Configuration states groups length → Bool) →
    Fin (length + 1) → Captures groups length → Option (Winner states groups length)

def localWinner {states groups length : Nat} (recurse : Observation states groups length)
    (kind : LookKind) (caller : Configuration states groups length) : Option (Winner states groups length) :=
  match kind with
  | .ahead | .notAhead => recurse .forward (fun _ => true) caller.position caller.captures
  | .behind | .notBehind =>
      best (((List.finRange (length + 1)).filter fun position => position ≤ caller.position).filterMap fun position =>
        recurse .forward (fun final => final.position == caller.position) position caller.captures)
  | .reverseBehind | .reverseNotBehind => recurse .reverse (fun _ => true) caller.position caller.captures

def controlAction {states groups length : Nat} (interpretation : Interpretation)
    (input : Fin length → Nat) (direction : Direction)
    (code : Fin states → Instruction states groups) (root : Fin states)
    (recurse : ∀ entry, DirectBodyCall code entry root → Observation states groups length)
    (configuration : Licensed code length root) : ObservedAction (Configuration states groups length) :=
  match instruction : code configuration.val.pc with
  | .look kind entry next =>
      let licensed : DirectBodyCall code entry root :=
        ⟨configuration.val.pc, kind, next, configuration.property, instruction⟩
      RegexObservationTrace.observedLook kind configuration.val
        (localWinner (recurse entry licensed) kind configuration.val) next
  | _ => RegexObservationTrace.observedAction interpretation input direction code
      (fun _ _ _ => none) configuration.val

private theorem observedLook_target {states groups length : Nat} (kind : LookKind)
    (caller last : Configuration states groups length) (next : Fin states)
    (selected : Option (Winner states groups length))
    (edge : last ∈ RegexRankedObservation.actionTargets
      (RegexObservationTrace.observedLook kind caller selected next)) : last.pc = next := by
  cases negative : kind.negative <;> cases selected <;>
    simp_all [RegexObservationTrace.observedLook, RegexRankedObservation.actionTargets]

theorem control_targets {states groups length : Nat} (interpretation : Interpretation)
    (input : Fin length → Nat) (direction : Direction)
    (code : Fin states → Instruction states groups) (root : Fin states)
    (recurse : ∀ entry, DirectBodyCall code entry root → Observation states groups length)
    (first : Licensed code length root) (last : Configuration states groups length)
    (edge : last ∈ RegexRankedObservation.actionTargets
      (controlAction interpretation input direction code root recurse first)) :
    OrdinaryReach code root last.pc := by
  apply first.property.tail
  unfold controlAction at edge
  split at edge
  · rename_i kind entry next instruction
    simp only [instruction, ordinaryTargets, List.mem_singleton]
    exact observedLook_target kind first.val last next _ edge
  all_goals
    exact RegexRankedObservation.observed_targets_authorized interpretation input direction code
      (fun _ _ _ => none) first.val last edge

def liftAction {states groups length : Nat} {code : Fin states → Instruction states groups} {root : Fin states}
    (action : ObservedAction (Configuration states groups length))
    (licensed : ∀ target ∈ RegexRankedObservation.actionTargets action, OrdinaryReach code root target.pc) :
    ObservedAction (Licensed code length root) :=
  match action with
  | .accept => .accept
  | .dead => .dead
  | .next target bits => .next ⟨target, licensed target (by simp [RegexRankedObservation.actionTargets])⟩ bits
  | .branch first second =>
      .branch ⟨first, licensed first (by simp [RegexRankedObservation.actionTargets])⟩
        ⟨second, licensed second (by simp [RegexRankedObservation.actionTargets])⟩

def complete {states groups length : Nat}
    (code : Fin states → Instruction states groups) (root : Fin states)
    (step : Licensed code length root → ObservedAction (Licensed code length root))
    (eligible : Configuration states groups length → Bool)
    (first : Licensed code length root) : Option (Winner states groups length) :=
  match returned : RegexObservationTrace.run step (fun state => eligible state.val) first with
  | .absent _ => none
  | .incomplete => False.elim (RegexObservationTrace.run_ne_incomplete step _ first returned)
  | .found last tag =>
      have selected : RegexObservationTrace.run step (fun state => eligible state.val) first = .found last () := by
        cases tag; exact returned
      have terminal := ((RegexObservationTrace.run_selected_iff step _ first last).mp selected).2
      match location : last.point.1 with
      | .main configuration => some ⟨configuration.val, last.choices, first.val.position⟩
      | .spool _ _ | .dead => False.elim (by
          obtain ⟨state, main⟩ := RegexObservationTrace.terminal_is_main step last terminal
          rw [location] at main
          contradiction)

theorem complete_none_iff {states groups length : Nat}
    (code : Fin states → Instruction states groups) (root : Fin states)
    (step : Licensed code length root → ObservedAction (Licensed code length root))
    (eligible : Configuration states groups length → Bool)
    (first : Licensed code length root) :
    complete code root step eligible first = none ↔
      ¬ ∃ word points last tag,
        RegexSelectionCorrespondence.Trace (RegexObservationTrace.graph step) RegexDependentObservation.probe
          (fun thread => RegexObservationTrace.mainEligible step (fun state => eligible state.val) thread.point)
          (RegexObservationTrace.initial step first) word points last tag := by
  have closed := RegexObservationTrace.run_absent_iff step (fun state => eligible state.val) first
  have terminated := RegexObservationTrace.run_ne_incomplete step (fun state => eligible state.val) first
  unfold complete
  split
  · simp_all
  · contradiction
  · rename_i last tag returned
    cases tag
    have terminal := ((RegexObservationTrace.run_selected_iff step (fun state => eligible state.val) first last).mp returned).2
    obtain ⟨state, main⟩ := RegexObservationTrace.terminal_is_main step last terminal
    split
    · simp_all
    · rename_i _ _ location
      rw [location] at main
      contradiction
    · rename_i location
      rw [location] at main
      contradiction

def layer {states groups length : Nat}
    (interpretation : Interpretation) (input : Fin length → Nat)
    (code : Fin states → Instruction states groups) (root : Fin states)
    (recurse : ∀ entry, DirectBodyCall code entry root → Observation states groups length) :
    Observation states groups length :=
  fun direction eligible position captures =>
    let first : Licensed code length root := ⟨⟨root, position, captures⟩, .refl⟩
    let step := fun state =>
      liftAction (controlAction interpretation input direction code root recurse state)
        (control_targets interpretation input direction code root recurse state)
    complete code root step eligible first

/-- The kernel recursively performs actual local observation and graph
matching. The certificate occurs only as a proof that its intrinsic call
relation is well founded. -/
def evaluate {states groups length : Nat}
    (interpretation : Interpretation) (input : Fin length → Nat)
    (code : Fin states → Instruction states groups) (certificate : Certificate code)
    (root : Fin states) : Observation states groups length :=
  (calls_wellFounded certificate).fix (layer interpretation input code) root

theorem evaluate_equation {states groups length : Nat}
    (interpretation : Interpretation) (input : Fin length → Nat)
    (code : Fin states → Instruction states groups) (certificate : Certificate code)
    (root : Fin states) :
    evaluate interpretation input code certificate root =
      layer interpretation input code root
        (fun entry _ => evaluate interpretation input code certificate entry) :=
  (calls_wellFounded certificate).fix_eq _ root

/-- Rank numbers cannot change an observation: they supply only the
termination proof for the same nontrivial graph-and-observation kernel. -/
theorem certificate_independent {states groups length : Nat}
    (interpretation : Interpretation) (input : Fin length → Nat)
    (code : Fin states → Instruction states groups)
    (first second : Certificate code) (root : Fin states) :
    evaluate interpretation input code first root = evaluate interpretation input code second root := by
  unfold evaluate
  congr

namespace Controls

private def interpretation : Interpretation := ⟨id⟩
private def emptyInput : Fin 0 → Nat := Fin.elim0
private def accepts (_ : Fin 1) : Instruction 1 0 := .accept
private def rejects (_ : Fin 1) : Instruction 1 0 := .dead

private def acceptsCertificate (value : Nat) : Certificate accepts where
  rank := fun _ => value
  ordinary := by intro pc next edge; simp [accepts, ordinaryTargets] at edge
  body := by intro pc kind entry next equation; cases equation

private def rejectsCertificate (value : Nat) : Certificate rejects where
  rank := fun _ => value
  ordinary := by intro pc next edge; simp [rejects, ordinaryTargets] at edge
  body := by intro pc kind entry next equation; cases equation

theorem distinct_rank_assignments_cannot_change_acceptance :
    evaluate interpretation emptyInput accepts (acceptsCertificate 0) 0 =
      evaluate interpretation emptyInput accepts (acceptsCertificate 17) 0 :=
  certificate_independent _ _ _ _ _ _

theorem accept_program_returns_winner :
    (evaluate interpretation emptyInput accepts (acceptsCertificate 0) 0
      .forward (fun _ => true) 0 Fin.elim0).isSome = true := by
  rw [evaluate_equation]
  simp [layer, complete, liftAction, controlAction, accepts, RegexObservationTrace.observedAction,
    action, RegexObservationTrace.run, RegexObservationTrace.fuel, RegexObservationTrace.initial,
    RegexObservationTrace.mainEligible, RegexObservationTrace.graph, RegexMemoizedSearch.taggedSearch,
    RegexMemoizedSearch.search, RegexSelectionCorrespondence.action]

theorem dead_program_does_not_invent_an_answer :
    (evaluate interpretation emptyInput rejects (rejectsCertificate 0) 0
      .forward (fun _ => true) 0 Fin.elim0).isSome = false := by
  rw [evaluate_equation]
  simp [layer, complete, liftAction, controlAction, rejects, RegexObservationTrace.observedAction,
    action, RegexObservationTrace.run, RegexObservationTrace.fuel, RegexObservationTrace.initial,
    RegexObservationTrace.graph, RegexMemoizedSearch.taggedSearch, RegexMemoizedSearch.search,
    RegexSelectionCorrespondence.action]

end Controls

end Mettapedia.GSLT.LanguageDef.RegexObservationKernel
