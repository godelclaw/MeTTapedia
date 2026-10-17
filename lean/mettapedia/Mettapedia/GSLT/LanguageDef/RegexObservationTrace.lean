import Mettapedia.GSLT.LanguageDef.RegexLookaroundObservation
import Mettapedia.Computability.RegularLanguages.RegexPikeSelection

/-!
# Retaining local observation priorities in the outer path

A completed positive observation contributes its local branch word before
continuation choices. This word is not erased when lookbehind compares
candidates from different starts. A finite sequence of forced branches embeds
the word into the existing proved ordered graph semantics.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexObservationTrace

open Mettapedia.Computability.RegularLanguages
open RegexSelectionCorrespondence (Action)

universe u
variable {α : Type u}

inductive ObservedAction (α : Type u) where
  | accept | dead
  | next (target : α) (word : List Bool)
  | branch (first second : α)

def word {α : Type u} : ObservedAction α → List Bool
  | .next _ bits => bits
  | _ => []

def maxWord [Fintype α] (step : α → ObservedAction α) : Nat :=
  Finset.univ.sup fun state => (word (step state)).length

theorem word_bounded [Fintype α] (step : α → ObservedAction α) (state : α) :
    (word (step state)).length ≤ maxWord step :=
  Finset.le_sup (f := fun state => (word (step state)).length) (Finset.mem_univ state)

inductive State (α : Type u) (bound : Nat) where
  | main (state : α)
  | spool (origin : α) (index : Fin (bound + 1))
  | dead
  deriving DecidableEq, Fintype

def graph [Fintype α] (step : α → ObservedAction α) :
    State α (maxWord step) → RegexTaggedGraph.Node (State α (maxWord step)) Unit Unit Unit
  | .dead => .dead
  | .main state => match step state with
      | .accept => .accept ()
      | .dead => .dead
      | .next _ _ => .jump (.spool state 0)
      | .branch first second => .choice (.main first) (.main second)
  | .spool origin index => match step origin with
      | .next target bits =>
          if within : index.val < bits.length then
            let next : State α (maxWord step) :=
              .spool origin ⟨(index.val + 1) % (maxWord step + 1), Nat.mod_lt _ (by omega)⟩
            if bits[index.val] then .choice .dead next else .choice next .dead
          else .jump (.main target)
      | _ => .dead

/-- Independent local word transport. The unused alternative is explicitly a
dead state; the chosen bits are actual graph branch observations. -/
inductive WordPath {α : Type u} (graph : α → RegexTaggedGraph.Node α Unit Unit Unit)
    (dead : α) : α → List Bool → α → Prop where
  | done {first last} : graph first = .jump last → WordPath graph dead first [] last
  | zero {first next bits last} : graph first = .choice next dead →
      WordPath graph dead next bits last → WordPath graph dead first (false :: bits) last
  | one {first next bits last} : graph first = .choice dead next →
      WordPath graph dead next bits last → WordPath graph dead first (true :: bits) last

theorem spool_wordPath [Fintype α] (step : α → ObservedAction α) (origin target : α)
    (bits : List Bool) (selected : step origin = .next target bits)
    (index : Fin (maxWord step + 1)) (within : index.val ≤ bits.length) :
    WordPath (graph step) .dead (.spool origin index) (bits.drop index.val) (.main target) := by
  generalize remaining : bits.length - index.val = count
  induction count using Nat.strong_induction_on generalizing index with
  | h count ih =>
      by_cases atEnd : index.val = bits.length
      · have rest : bits.drop index.val = [] := by simp [atEnd]
        rw [rest]
        exact .done (by simp [graph, selected, atEnd])
      · have before : index.val < bits.length := by omega
        have bounded := word_bounded step origin
        simp only [selected, word] at bounded
        let after : Fin (maxWord step + 1) := ⟨index.val + 1, by omega⟩
        have noWrap : (index.val + 1) % (maxWord step + 1) = index.val + 1 := Nat.mod_eq_of_lt (by omega)
        have tail := ih (bits.length - after.val) (by dsimp [after]; omega) after (by dsimp [after]; omega) rfl
        have decomposition : bits.drop index.val = bits[index.val] :: bits.drop (index.val + 1) :=
          List.drop_eq_getElem_cons before
        rw [decomposition]
        cases bit : bits[index.val]
        · exact .zero (by simp [graph, selected, before, bit, after, noWrap]) tail
        · exact .one (by simp [graph, selected, before, bit, after, noWrap]) tail

theorem WordPath.prefix {α : Type u}
    {graph : α → RegexTaggedGraph.Node α Unit Unit Unit} {dead first last : α}
    {bits : List Bool} (path : WordPath graph dead first bits last)
    (thread : RegexTaggedGraph.Thread α 0) (starts : thread.point.1 = first) :
    ∃ points final,
      RegexPikeSelection.Prefix graph RegexDependentObservation.probe thread bits points final ∧
      final.point.1 = last ∧ final.choices = thread.choices ++ bits := by
  induction path generalizing thread with
  | @done first last step =>
      let final := thread.at last
      have actual : RegexSelectionCorrespondence.action graph RegexDependentObservation.probe thread = .next final := by
        simp [RegexSelectionCorrespondence.action, starts, step, final]
      refine ⟨[thread.point], final, .next actual (.nil final), rfl, ?_⟩
      simp [final, RegexTaggedGraph.Thread.at]
  | @zero first next bits last step path ih =>
      let following := thread.branch next false
      obtain ⟨points, final, history, endpoint, choices⟩ := ih following rfl
      have actual : RegexSelectionCorrespondence.action graph RegexDependentObservation.probe thread =
          .branch following (thread.branch dead true) := by
        simp [RegexSelectionCorrespondence.action, starts, step, following]
      refine ⟨thread.point :: points, final, .left actual history, endpoint, ?_⟩
      simpa [following, RegexTaggedGraph.Thread.branch, List.append_assoc] using choices
  | @one first next bits last step path ih =>
      let following := thread.branch next true
      obtain ⟨points, final, history, endpoint, choices⟩ := ih following rfl
      have actual : RegexSelectionCorrespondence.action graph RegexDependentObservation.probe thread =
          .branch (thread.branch dead false) following := by
        simp [RegexSelectionCorrespondence.action, starts, step, following]
      refine ⟨thread.point :: points, final, .right actual history, endpoint, ?_⟩
      simpa [following, RegexTaggedGraph.Thread.branch, List.append_assoc] using choices

def observedLook {states groups length : Nat}
    (kind : RegexDependentObservation.LookKind)
    (caller : RegexDependentObservation.Configuration states groups length)
    (selected : Option (RegexDependentObservation.Winner states groups length)) (next : Fin states) :
    ObservedAction (RegexDependentObservation.Configuration states groups length) :=
  match kind.negative, selected with
  | false, some winner => .next { caller with pc := next, captures := winner.configuration.captures } winner.choices
  | true, none => .next { caller with pc := next } []
  | _, _ => .dead

theorem positive_retains_local_priority {states groups length : Nat}
    (caller : RegexDependentObservation.Configuration states groups length)
    (selected : RegexDependentObservation.Winner states groups length) (next : Fin states) :
    word (observedLook .ahead caller (some selected) next) = selected.choices := rfl

theorem negative_has_no_local_capture_trace {states groups length : Nat}
    (caller : RegexDependentObservation.Configuration states groups length) (next : Fin states) :
    observedLook .notAhead caller none next = .next { caller with pc := next } [] := rfl

def observedAction {states groups length : Nat}
    (interpretation : RegexDependentObservation.Interpretation) (input : Fin length → Nat)
    (direction : RegexDependentObservation.Direction)
    (program : Fin states → RegexDependentObservation.Instruction states groups)
    (body : RegexDependentObservation.LookKind → Fin states →
      RegexDependentObservation.Configuration states groups length →
      Option (RegexDependentObservation.Winner states groups length))
    (configuration : RegexDependentObservation.Configuration states groups length) :
    ObservedAction (RegexDependentObservation.Configuration states groups length) :=
  match program configuration.pc with
  | .look kind entry next => observedLook kind configuration (body kind entry configuration) next
  | _ =>
      match RegexDependentObservation.action interpretation input direction program
          (fun kind entry caller => (body kind entry caller).map RegexDependentObservation.Winner.configuration)
          configuration with
      | .accept _ => .accept
      | .dead => .dead
      | .next target => .next target []
      | .branch first second => .branch first second

def mainEligible [Fintype α] (step : α → ObservedAction α) (eligible : α → Bool) :
    OrderedGraphSearch.Point (State α (maxWord step)) 0 → Bool
  | (.main state, _) => eligible state
  | _ => false

def initial [Fintype α] (step : α → ObservedAction α) (first : α) :
    RegexTaggedGraph.Thread (State α (maxWord step)) 0 :=
  ⟨(.main first, 0), fun _ => none, []⟩

def fuel [Fintype α] (step : α → ObservedAction α) : Nat :=
  Fintype.card (OrderedGraphSearch.Point (State α (maxWord step)) 0) + 2

def run [Fintype α] [DecidableEq α] (step : α → ObservedAction α)
    (eligible : α → Bool) (first : α) :=
  RegexMemoizedSearch.taggedSearch (graph step) RegexDependentObservation.probe
    (mainEligible step eligible) (fuel step) (initial step first)

theorem run_ne_incomplete [Fintype α] [DecidableEq α] (step : α → ObservedAction α)
    (eligible : α → Bool) (first : α) : run step eligible first ≠ .incomplete :=
  RegexMemoizedSearch.taggedSearch_ne_incomplete _ _ _ _ _ (by simp [fuel])

theorem run_selected_iff [Fintype α] [DecidableEq α] (step : α → ObservedAction α)
    (eligible : α → Bool) (first : α)
    (last : RegexTaggedGraph.Thread (State α (maxWord step)) 0) :
    run step eligible first = .found last () ↔
      RegexSelectionCorrespondence.LeastSimple (graph step) RegexDependentObservation.probe
        (fun thread => mainEligible step eligible thread.point) (initial step first) last ∧
      RegexPikeVM.terminal (graph step) last = some () :=
  RegexMemoizedSearch.taggedSearch_leastSimple _ _ _ _ _ _ _ (by simp [fuel])

theorem run_absent_iff [Fintype α] [DecidableEq α] (step : α → ObservedAction α)
    (eligible : α → Bool) (first : α) :
    (∃ seen, run step eligible first = .absent seen) ↔
      ¬ ∃ code points last tag,
        RegexSelectionCorrespondence.Trace (graph step) RegexDependentObservation.probe
          (fun thread => mainEligible step eligible thread.point) (initial step first) code points last tag :=
  RegexMemoizedSearch.taggedSearch_absent_iff _ _ _ _ _ (by simp [fuel])

theorem terminal_is_main [Fintype α] (step : α → ObservedAction α)
    (last : RegexTaggedGraph.Thread (State α (maxWord step)) 0)
    (terminal : RegexPikeVM.terminal (graph step) last = some ()) :
    ∃ state, last.point.1 = .main state := by
  cases location : last.point.1 with
  | main state => exact ⟨state, rfl⟩
  | dead => simp [RegexPikeVM.terminal, location, graph] at terminal
  | spool origin index =>
      cases instruction : step origin <;>
        simp only [RegexPikeVM.terminal, location, graph, instruction] at terminal
      all_goals first
        | contradiction
        | split at terminal <;> split_ifs at *

def complete {states groups length : Nat}
    (step : RegexDependentObservation.Configuration states groups length →
      ObservedAction (RegexDependentObservation.Configuration states groups length))
    (eligible : RegexDependentObservation.Configuration states groups length → Bool)
    (first : RegexDependentObservation.Configuration states groups length) :
    Option (RegexDependentObservation.Winner states groups length) :=
  match returned : run step eligible first with
  | .absent _ => none
  | .incomplete => False.elim (run_ne_incomplete step eligible first returned)
  | .found last tag =>
      have selected : run step eligible first = .found last () := by cases tag; exact returned
      have terminal := ((run_selected_iff step eligible first last).mp selected).2
      match location : last.point.1 with
      | .main configuration => some ⟨configuration, last.choices, first.position⟩
      | .spool _ _ | .dead => False.elim (by
          obtain ⟨state, main⟩ := terminal_is_main step last terminal
          rw [location] at main
          contradiction)

theorem complete_none_iff {states groups length : Nat}
    (step : RegexDependentObservation.Configuration states groups length →
      ObservedAction (RegexDependentObservation.Configuration states groups length))
    (eligible : RegexDependentObservation.Configuration states groups length → Bool)
    (first : RegexDependentObservation.Configuration states groups length) :
    complete step eligible first = none ↔
      ¬ ∃ code points last tag,
        RegexSelectionCorrespondence.Trace (graph step) RegexDependentObservation.probe
          (fun thread => mainEligible step eligible thread.point) (initial step first) code points last tag := by
  have closed := run_absent_iff step eligible first
  have terminated := run_ne_incomplete step eligible first
  unfold complete
  split
  · simp_all
  · contradiction
  · rename_i last tag returned
    cases tag
    have terminal := ((run_selected_iff step eligible first last).mp returned).2
    obtain ⟨state, main⟩ := terminal_is_main step last terminal
    split
    · simp_all
    · rename_i _ _ location
      rw [location] at main
      contradiction
    · rename_i location
      rw [location] at main
      contradiction

theorem complete_some_iff {states groups length : Nat}
    (step : RegexDependentObservation.Configuration states groups length →
      ObservedAction (RegexDependentObservation.Configuration states groups length))
    (eligible : RegexDependentObservation.Configuration states groups length → Bool)
    (first : RegexDependentObservation.Configuration states groups length)
    (winner : RegexDependentObservation.Winner states groups length) :
    complete step eligible first = some winner ↔
      ∃ last : RegexTaggedGraph.Thread
          (State (RegexDependentObservation.Configuration states groups length) (maxWord step)) 0,
        RegexSelectionCorrespondence.LeastSimple (graph step) RegexDependentObservation.probe
          (fun thread => mainEligible step eligible thread.point) (initial step first) last ∧
        last.point.1 = .main winner.configuration ∧
        last.choices = winner.choices ∧ winner.start = first.position := by
  have terminated := run_ne_incomplete step eligible first
  constructor
  · intro selected
    unfold complete at selected
    split at selected
    · contradiction
    · contradiction
    · rename_i last tag returned
      cases tag
      have preferred := (run_selected_iff step eligible first last).mp returned
      split at selected
      · rename_i configuration location
        have same := Option.some.inj selected
        cases same
        exact ⟨last, preferred.1, location, rfl, rfl⟩
      · rename_i _ _ impossible
        obtain ⟨state, main⟩ := terminal_is_main step last preferred.2
        rw [impossible] at main
        contradiction
      · rename_i impossible
        obtain ⟨state, main⟩ := terminal_is_main step last preferred.2
        rw [impossible] at main
        contradiction
  · rintro ⟨last, preferred, location, choices, start⟩
    obtain ⟨code, points, tag, trace, _, _⟩ := preferred
    have terminal : RegexPikeVM.terminal (graph step) last = some () := by
      cases tag
      exact trace.sound.2.1
    have returned := (run_selected_iff step eligible first last).mpr ⟨by
      exact ⟨code, points, (), trace, by assumption, by assumption⟩, terminal⟩
    unfold complete
    split
    · rename_i seen absent
      cases returned.symm.trans absent
    · contradiction
    · rename_i other tag found
      cases tag
      have same := RegexMemoizedSearch.Result.found.inj (found.symm.trans returned)
      obtain ⟨rfl, _⟩ := same
      split
      · rename_i configuration atMain
        have sameConfiguration := State.main.inj (atMain.symm.trans location)
        subst configuration
        cases winner
        simp_all
      · rename_i _ _ impossible
        rw [impossible] at location
        contradiction
      · rename_i impossible
        rw [impossible] at location
        contradiction

def rankedEvaluator {states groups length : Nat}
    (interpretation : RegexDependentObservation.Interpretation) (input : Fin length → Nat)
    (program : RegexDependentObservation.RankedProgram states groups) :
    Nat → RegexDependentObservation.Evaluator states groups length
  | 0 => fun _ _ _ => none
  | depth + 1 => fun direction eligible first =>
      let body := RegexDependentObservation.bodyWinner (rankedEvaluator interpretation input program depth)
      complete (fun configuration =>
        if program.rank configuration.pc < depth + 1 then
          observedAction interpretation input direction program.instruction body configuration
        else .dead) eligible first

namespace Controls

private def emitZero (_ : Fin 1) : ObservedAction (Fin 1) := .next 0 [false]
private def emitOne (_ : Fin 1) : ObservedAction (Fin 1) := .next 0 [true]

theorem zero_local_priority_is_an_actual_left_branch :
    WordPath (graph emitZero) .dead (.spool 0 0) [false] (.main 0) :=
  spool_wordPath emitZero 0 0 [false] rfl 0 (by decide)

theorem one_local_priority_is_an_actual_right_branch :
    WordPath (graph emitOne) .dead (.spool 0 0) [true] (.main 0) :=
  spool_wordPath emitOne 0 0 [true] rfl 0 (by decide)

theorem local_priority_must_not_be_erased_to_a_jump :
    graph emitOne (.spool 0 0) ≠ RegexTaggedGraph.Node.jump (.main 0) := by
  intro same
  cases same

private def candidate (bits : List Bool) (start : Fin 5) : RegexDependentObservation.Winner 1 0 4 :=
  ⟨⟨0, 4, Fin.elim0⟩, bits, start⟩

theorem nested_observation_priority_can_change_the_preferred_start :
    (RegexDependentObservation.choose (candidate [false] 0) (candidate [true] 3)).start = 0 ∧
    (RegexDependentObservation.choose (candidate [] 0) (candidate [] 3)).start = 3 := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.RegexObservationTrace
