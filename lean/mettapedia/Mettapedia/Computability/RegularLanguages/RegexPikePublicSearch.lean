import Mettapedia.Computability.RegularLanguages.RegexPikeCorrespondence
import Mettapedia.Computability.RegularLanguages.RegexPublicSearch

/-!
# Actual Pike execution at ordered original-input search entries

The singleton Pike run and the global point-memo DFS implement the same
independent selected observation, including every capture register. Applying
the existing short-circuiting start observer therefore preserves minimum
successful start and original assertion context. This is not a refinement
proof for a native implementation which injects new starts into one frontier.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.RegexPikePublicSearch

open RegexTaggedGraph RegexSelectionCorrespondence RegexPublicSearch
open OrderedGraphSearch (Point Probe)

universe u v w z

variable {State : Type u} {Class : Type v} {Assertion : Type w} {Tag : Type z} {length : Nat}

theorem anchored_eq_dfs [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (first : Thread State length)
    (closureFuel inputFuel dfsFuel : Nat)
    (closureEnough : 3 * Fintype.card State + 1 ≤ closureFuel)
    (inputEnough : length + 1 ≤ inputFuel)
    (dfsEnough : Fintype.card (Point State length) + 1 < dfsFuel) :
    RegexPikeVM.run graph probe (fun thread => eligible thread.point) closureFuel inputFuel [first] =
      anchored graph probe eligible dfsFuel first := by
  cases executed : RegexPikeVM.run graph probe (fun thread => eligible thread.point)
      closureFuel inputFuel [first] with
  | incomplete =>
      exact False.elim (RegexPikeVM.run_ne_incomplete graph probe (fun thread => eligible thread.point)
        first closureFuel inputFuel closureEnough inputEnough executed)
  | finished selected =>
      cases selected with
      | none =>
          apply Eq.symm
          apply (anchored_absent_iff graph probe eligible first dfsFuel dfsEnough).mpr
          intro ⟨last, tag, least, _⟩
          obtain ⟨code, points, foundTag, trace, _, _⟩ := least
          exact (RegexPikeCoverage.run_none_iff_no_trace graph probe eligible closureFuel inputFuel
            closureEnough inputEnough first).mp executed ⟨code, points, last, foundTag, trace⟩
      | some pair =>
          obtain ⟨last, tag⟩ := pair
          exact ((anchored_found_iff graph probe eligible first last tag dfsFuel dfsEnough).mpr
            ((RegexPikeCorrespondence.run_leastSimple graph probe eligible first last tag
              closureFuel inputFuel closureEnough inputEnough).mp executed)).symm

/-- The same prepared graph and original-input probe are used at every start.
Only the explicitly requested pattern execution is repeated. -/
theorem scan_eq_search [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (state : State) (closureFuel inputFuel dfsFuel : Nat)
    (closureEnough : 3 * Fintype.card State + 1 ≤ closureFuel)
    (inputEnough : length + 1 ≤ inputFuel)
    (dfsEnough : Fintype.card (Point State length) + 1 < dfsFuel)
    (starts : List (Fin (length + 1))) :
    scan (fun position => RegexPikeVM.run graph probe (fun thread => eligible thread.point)
      closureFuel inputFuel [entry state position]) starts =
      RegexPublicSearch.search graph probe eligible state dfsFuel starts := by
  unfold RegexPublicSearch.search
  apply congrArg (fun attempt => scan attempt starts)
  funext position
  exact anchored_eq_dfs graph probe eligible (entry state position) closureFuel inputFuel dfsFuel
    closureEnough inputEnough dfsEnough

theorem minimum_start [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (state : State) (closureFuel inputFuel dfsFuel : Nat)
    (closureEnough : 3 * Fintype.card State + 1 ≤ closureFuel)
    (inputEnough : length + 1 ≤ inputFuel)
    (dfsEnough : Fintype.card (Point State length) + 1 < dfsFuel)
    (minimum : Nat) (position : Fin (length + 1)) (last : Thread State length) (tag : Tag) :
    scan (fun start => RegexPikeVM.run graph probe (fun thread => eligible thread.point)
      closureFuel inputFuel [entry state start]) (positions length minimum) =
        .finished (some ((position, last), tag)) ↔
      minimum ≤ position.val ∧ AcceptsAt graph probe eligible state position last tag ∧
        ∀ earlier : Fin (length + 1), minimum ≤ earlier.val → earlier.val < position.val →
          ¬ ∃ answer label, AcceptsAt graph probe eligible state earlier answer label := by
  rw [scan_eq_search graph probe eligible state closureFuel inputFuel dfsFuel
    closureEnough inputEnough dfsEnough]
  exact search_minimum_start graph probe eligible state dfsFuel dfsEnough minimum position last tag

theorem absent_iff [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (state : State) (closureFuel inputFuel dfsFuel : Nat)
    (closureEnough : 3 * Fintype.card State + 1 ≤ closureFuel)
    (inputEnough : length + 1 ≤ inputFuel)
    (dfsEnough : Fintype.card (Point State length) + 1 < dfsFuel)
    (starts : List (Fin (length + 1))) :
    scan (fun position => RegexPikeVM.run graph probe (fun thread => eligible thread.point)
      closureFuel inputFuel [entry state position]) starts = .finished none ↔
      ∀ position ∈ starts, ¬ ∃ code points last tag,
        Trace graph probe (fun thread => eligible thread.point) (entry state position) code points last tag := by
  rw [scan_eq_search graph probe eligible state closureFuel inputFuel dfsFuel
    closureEnough inputEnough dfsEnough]
  exact search_absent_iff graph probe eligible state dfsFuel dfsEnough starts

namespace Controls

private def probe : Probe Unit Unit 2 :=
  ⟨fun _ position => position.val < 2, fun _ position => position.val == 1⟩
private def graph : Fin 4 → Node (Fin 4) Unit Unit Nat := fun state =>
  match state.val with
  | 0 => .assertion () 1
  | 1 => .save 0 2
  | 2 => .consume () 3
  | _ => .accept 7

private def observed : RegexPikeVM.Result (Fin 3 × Thread (Fin 4) 2) Nat →
    Option (Nat × Nat × Option Nat)
  | .finished (some ((start, last), _)) =>
      some (start.val, last.point.2.val, (last.registers 0).map Fin.val)
  | _ => none

theorem later_start_retains_original_assertion_and_capture :
    observed (scan (fun position => RegexPikeVM.run graph probe (fun _ => true)
      20 3 [entry 0 position]) (positions 2 0)) = some (1, 2, some 1) := by decide

theorem full_eligibility_retains_original_input_end :
    observed (scan (fun position => RegexPikeVM.run graph probe
      RegexPikeVM.atInputEnd 20 3 [entry 0 position]) (positions 2 0)) = some (1, 2, some 1) := by decide

theorem incomplete_earlier_attempt_does_not_skip_to_later_start :
    scan (fun position => RegexPikeVM.run graph probe (fun _ => true)
      0 3 [entry 0 position]) (positions 2 0) = .incomplete := by rfl

end Controls

end Mettapedia.Computability.RegularLanguages.RegexPikePublicSearch
