import Mettapedia.Machines.SharedContinuation

/-!
# Callee-local admission and the retained call frontier

The reference filters equation candidates and schedules every match. The
scanner instead keeps one candidate until it sees another match. Register
entry is permitted only for a sole admitted candidate; otherwise the ready
call returns to the ordinary frontier. Unrelated heads need no determinacy
certificate. Return frames, caller alternatives and earlier publications
remain part of the state being transferred.

This is a law for matching and entry. It does not verify a native matcher,
register bytecode, pointer ownership or identify register work with source
fuel. The candidate visitor is pure; committed effects precede this entrance
and must not be repeated while the call is matched.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CalleeAdmission

inductive Selection (A : Type) where
  | empty
  | one (candidate : A)
  | multiple
  deriving DecidableEq, Repr

variable {Equation Context Control Frame Answer A : Type}

/-- The independent observation of the complete matching list. -/
def summarize : List A → Selection A
  | [] => .empty
  | [candidate] => .one candidate
  | _ :: _ :: _ => .multiple

/-- A native-style scan stops as soon as a second equation matches. -/
def scan (visit : Equation → Option A) : Option A → List Equation → Selection A
  | selected, [] => match selected with | none => .empty | some candidate => .one candidate
  | selected, equation :: later =>
      match visit equation with
      | none => scan visit selected later
      | some candidate =>
          match selected with
          | none => scan visit (some candidate) later
          | some _ => .multiple

theorem scan_refines (visit : Equation → Option A) (equations : List Equation)
    (selected : Option A) :
    scan visit selected equations =
      summarize (selected.toList ++ equations.filterMap visit) := by
  induction equations generalizing selected with
  | nil => cases selected <;> rfl
  | cons equation later ih =>
      cases found : visit equation with
      | none => simpa [scan, found] using ih selected
      | some candidate =>
          cases selected with
          | none => simpa [scan, found] using ih (some candidate)
          | some previous => simp [scan, found, summarize]

theorem sole_candidate (visit : Equation → Option A) (equations : List Equation)
    (candidate : A) :
    scan visit none equations = .one candidate ↔
      equations.filterMap visit = [candidate] := by
  rw [scan_refines]
  simp only [Option.toList_none, List.nil_append]
  cases foundCandidates : equations.filterMap visit with
  | nil => simp [summarize]
  | cons first later =>
      cases later with
      | nil => simp [summarize]
      | cons next rest => simp [summarize]

inductive Route (Context Control : Type) where
  | code (context : Context) (control : Control)
  | cursor
  deriving DecidableEq, Repr

def selectRoute (visit : Equation → Option (Context × Control))
    (eligible : Context → Control → Bool) (equations : List Equation) : Route Context Control :=
  match scan visit none equations with
  | .one candidate =>
      if eligible candidate.1 candidate.2 then .code candidate.1 candidate.2 else .cursor
  | _ => .cursor

/-- Written equation matching supplies the source's entire next frontier. -/
def sourceEntry (visit : Equation → Option (Context × Control)) (equations : List Equation)
    (returns : List Frame) (older : List (SharedContinuation.Task Context Control Frame))
    (published : List (Context × Answer)) : SharedContinuation.State Context Control Frame Answer :=
  ⟨(equations.filterMap visit).map (fun next => ⟨next.1, next.2, returns⟩) ++ older, published⟩

/-- A sole compiled candidate enters directly. Refusal retains the ready
call's candidates; it does not retain only the scanner's first match. -/
def targetEntry (visit : Equation → Option (Context × Control))
    (eligible : Context → Control → Bool) (equations : List Equation)
    (returns : List Frame) (older : List (SharedContinuation.Task Context Control Frame))
    (published : List (Context × Answer)) : SharedContinuation.State Context Control Frame Answer :=
  match selectRoute visit eligible equations with
  | .code context control => ⟨⟨context, control, returns⟩ :: older, published⟩
  | .cursor =>
      ⟨(equations.filterMap visit).map (fun next => ⟨next.1, next.2, returns⟩) ++ older, published⟩

theorem entry_frontier_exact (visit : Equation → Option (Context × Control))
    (eligible : Context → Control → Bool) (equations : List Equation)
    (returns : List Frame) (older : List (SharedContinuation.Task Context Control Frame))
    (published : List (Context × Answer)) :
    targetEntry visit eligible equations returns older published =
      sourceEntry visit equations returns older published := by
  unfold targetEntry selectRoute
  cases selected : scan visit none equations with
  | empty => rfl
  | multiple => rfl
  | one candidate =>
      have foundCandidates := (sole_candidate visit equations candidate).mp selected
      by_cases accepted : eligible candidate.1 candidate.2 = true <;>
        simp [accepted, sourceEntry, foundCandidates]

/-- Later bounded execution starts from the complete retained state,
including previous publications and every caller's return frame. -/
theorem bounded_frontier_exact {Call : Type}
    (program : SharedContinuation.Program Context Control Call Frame Answer)
    (visit : Equation → Option (Context × Control)) (eligible : Context → Control → Bool)
    (equations : List Equation) (returns : List Frame)
    (older : List (SharedContinuation.Task Context Control Frame))
    (published : List (Context × Answer)) (allowance : Nat) :
    (SharedContinuation.step program)^[allowance]
        (targetEntry visit eligible equations returns older published) =
      (SharedContinuation.step program)^[allowance]
        (sourceEntry visit equations returns older published) := by
  rw [entry_frontier_exact]

namespace Controls

def visit (head : Nat) (equation : Nat × Nat) : Option (Nat × Nat) :=
  if equation.1 = head then some (head, equation.2) else none

/-- An ambiguous unrelated head does not veto this unique callee. -/
theorem unrelated_ambiguity_does_not_veto :
    selectRoute (visit 0) (fun _ _ => true) [(0, 10), (1, 20), (1, 30)] = .code 0 10 ∧
    selectRoute (visit 1) (fun _ _ => true) [(0, 10), (1, 20), (1, 30)] = .cursor := by
  decide

/-- Duplicate occurrences are multiple answers, even when their bodies agree. -/
theorem duplicates_require_frontier :
    selectRoute (visit 1) (fun _ _ => true) [(1, 20), (1, 20)] = .cursor ∧
    (targetEntry (visit 1) (fun _ _ => true) [(1, 20), (1, 20)]
      ([] : List Nat) [] ([] : List (Nat × Nat))).frontier.length = 2 := by
  decide

theorem refused_body_keeps_candidate :
    selectRoute (visit 1) (fun _ _ => false) [(1, 20)] = .cursor ∧
    (targetEntry (visit 1) (fun _ _ => false) [(1, 20)] [7]
      ([] : List (SharedContinuation.Task Nat Nat Nat)) ([] : List (Nat × Nat))).frontier =
      [⟨1, 20, [7]⟩] := by
  exact ⟨rfl, rfl⟩

theorem caller_and_publication_survive :
    (targetEntry (visit 1) (fun _ _ => true) [(1, 20), (1, 30)] [7]
      [⟨8, 90, [6]⟩] [(4, 5)]).frontier =
        [⟨1, 20, [7]⟩, ⟨1, 30, [7]⟩, ⟨8, 90, [6]⟩] ∧
    (targetEntry (visit 1) (fun _ _ => true) [(1, 20), (1, 30)] [7]
      [⟨8, 90, [6]⟩] [(4, 5)]).emitted = [(4, 5)] := by
  exact ⟨rfl, rfl⟩

end Controls
end Mettapedia.Machines.CalleeAdmission

#print axioms Mettapedia.Machines.CalleeAdmission.scan_refines
#print axioms Mettapedia.Machines.CalleeAdmission.sole_candidate
#print axioms Mettapedia.Machines.CalleeAdmission.entry_frontier_exact
#print axioms Mettapedia.Machines.CalleeAdmission.bounded_frontier_exact
#print axioms Mettapedia.Machines.CalleeAdmission.Controls.unrelated_ambiguity_does_not_veto
#print axioms Mettapedia.Machines.CalleeAdmission.Controls.duplicates_require_frontier
#print axioms Mettapedia.Machines.CalleeAdmission.Controls.refused_body_keeps_candidate
#print axioms Mettapedia.Machines.CalleeAdmission.Controls.caller_and_publication_survive
