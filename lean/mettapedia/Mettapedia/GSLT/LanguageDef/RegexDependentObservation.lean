import Mettapedia.Computability.RegularLanguages.RegexMemoizedSearch
import Mathlib.Data.Fintype.Pi

/-!
# Capture-dependent regex observations

Captures in this machine are part of the control state. A remembered substring
can determine whether an edge exists, so the ordinary point-only quotient is
not used. Every position and capture boundary belongs to the original input.
The finite-state bound is a completeness witness, not a default user budget.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexDependentObservation

open Mettapedia.Computability.RegularLanguages
open RegexSelectionCorrespondence (Action)

inductive Direction where
  | forward | reverse
  deriving DecidableEq, Repr

inductive Comparison where
  | exact | asciiFold | unicodeFold
  deriving DecidableEq, Repr

inductive Capture (length : Nat) where
  | unmatched
  | opened (position : Fin (length + 1))
  | closed (low high : Fin (length + 1))
  deriving DecidableEq, Repr, Fintype

abbrev Captures (groups length : Nat) := Fin groups → Capture length

structure Configuration (states groups length : Nat) where
  pc : Fin states
  position : Fin (length + 1)
  captures : Captures groups length
  deriving DecidableEq, Fintype

def openCapture {groups length : Nat} (captures : Captures groups length)
    (group : Fin groups) (position : Fin (length + 1)) : Captures groups length :=
  Function.update captures group (.opened position)

def closeCapture {groups length : Nat} (captures : Captures groups length)
    (group : Fin groups) (position : Fin (length + 1)) : Captures groups length :=
  match captures group with
  | .opened start => Function.update captures group (.closed (min start position) (max start position))
  | _ => captures

@[simp] theorem open_same {groups length : Nat} (captures : Captures groups length)
    (group : Fin groups) (position : Fin (length + 1)) :
    openCapture captures group position group = .opened position := by simp [openCapture]

theorem close_normalizes {groups length : Nat} (captures : Captures groups length)
    (group : Fin groups) (start finish : Fin (length + 1))
    (opened : captures group = .opened start) :
    closeCapture captures group finish group = .closed (min start finish) (max start finish) := by
  simp [closeCapture, opened]

theorem close_other {groups length : Nat} (captures : Captures groups length)
    (group other : Fin groups) (position : Fin (length + 1)) (different : other ≠ group) :
    closeCapture captures group position other = captures other := by
  cases captured : captures group <;> simp [closeCapture, captured, different]

def asciiCanonical (scalar : Nat) : Nat :=
  if 65 ≤ scalar ∧ scalar ≤ 90 then scalar + 32 else scalar

structure Interpretation where
  unicodeCanonical : Nat → Nat

def equivalent (interpretation : Interpretation) (comparison : Comparison) (first second : Nat) : Bool :=
  match comparison with
  | .exact => first == second
  | .asciiFold => asciiCanonical first == asciiCanonical second
  | .unicodeFold => interpretation.unicodeCanonical first == interpretation.unicodeCanonical second

def piece {length : Nat} (input : Fin length → Nat) (start count : Nat) : List Nat :=
  ((List.finRange length).filter fun index => start ≤ index.val && index.val < start + count).map input

def pairwiseEquivalent (interpretation : Interpretation) (comparison : Comparison)
    (first second : List Nat) : Bool :=
  List.all₂ (equivalent interpretation comparison) first second

def backreference {groups length : Nat} (interpretation : Interpretation)
    (input : Fin length → Nat) (direction : Direction) (comparison : Comparison)
    (captures : Captures groups length) (group : Fin groups)
    (position : Fin (length + 1)) : Option (Fin (length + 1)) := do
  let .closed low high := captures group | none
  let count := high.val - low.val
  match direction with
  | .forward =>
      if bounds : low ≤ high ∧ position.val + count ≤ length then
        if pairwiseEquivalent interpretation comparison (piece input low.val count) (piece input position.val count) then
          some ⟨position.val + count, by omega⟩
        else none
      else none
  | .reverse =>
      if _bounds : low ≤ high ∧ count ≤ position.val then
        if pairwiseEquivalent interpretation comparison (piece input low.val count) (piece input (position.val - count) count) then
          some ⟨position.val - count, by omega⟩
        else none
      else none

theorem backreference_unmatched {groups length : Nat} (interpretation : Interpretation)
    (input : Fin length → Nat) (direction : Direction) (comparison : Comparison)
    (captures : Captures groups length) (group : Fin groups) (position : Fin (length + 1))
    (missing : captures group = .unmatched) :
    backreference interpretation input direction comparison captures group position = none := by
  simp [backreference, missing]

theorem backreference_open {groups length : Nat} (interpretation : Interpretation)
    (input : Fin length → Nat) (direction : Direction) (comparison : Comparison)
    (captures : Captures groups length) (group : Fin groups) (position start : Fin (length + 1))
    (opened : captures group = .opened start) :
    backreference interpretation input direction comparison captures group position = none := by
  simp [backreference, opened]

theorem piece_zero {length : Nat} (input : Fin length → Nat) (start : Nat) :
    piece input start 0 = [] := by
  simp only [piece, Nat.add_zero, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro position _
  simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
  omega

theorem backreference_empty {groups length : Nat} (interpretation : Interpretation)
    (input : Fin length → Nat) (direction : Direction) (comparison : Comparison)
    (captures : Captures groups length) (group : Fin groups) (position start : Fin (length + 1))
    (closed : captures group = .closed start start) :
    backreference interpretation input direction comparison captures group position = some position := by
  have within : position.val ≤ length := by omega
  cases direction <;> simp [backreference, closed, piece_zero, pairwiseEquivalent, within]

inductive LookKind where
  | ahead | notAhead | behind | notBehind | reverseBehind | reverseNotBehind
  deriving DecidableEq, Repr

def LookKind.negative : LookKind → Bool
  | .notAhead | .notBehind | .reverseNotBehind => true
  | _ => false

def LookKind.direction : LookKind → Direction
  | .reverseBehind | .reverseNotBehind => .reverse
  | _ => .forward

inductive Instruction (states groups : Nat) where
  | accept | dead
  | jump (next : Fin states)
  | branch (left right : Fin states)
  | consume (contains : Nat → Bool) (next : Fin states)
  | assertion (holds : Nat → Bool) (next : Fin states)
  | open (group : Fin groups) (next : Fin states)
  | close (group : Fin groups) (next : Fin states)
  | backref (group : Fin groups) (comparison : Comparison) (next : Fin states)
  | look (kind : LookKind) (body next : Fin states)

def ordinaryTargets {states groups : Nat} : Instruction states groups → List (Fin states)
  | .accept | .dead => []
  | .branch left right => [left, right]
  | .jump next | .consume _ next | .assertion _ next | .open _ next | .close _ next |
    .backref _ _ next | .look _ _ next => [next]

structure RankedProgram (states groups : Nat) where
  instruction : Fin states → Instruction states groups
  rank : Fin states → Nat
  ordinary : ∀ pc next, next ∈ ordinaryTargets (instruction pc) → rank next ≤ rank pc
  body : ∀ pc kind entry next, instruction pc = .look kind entry next → rank entry < rank pc

theorem no_recursive_observation_cycle {states groups : Nat} (program : RankedProgram states groups)
    (pc : Fin states) (kind : LookKind) (next : Fin states) :
    program.instruction pc ≠ .look kind pc next := by
  intro self
  have impossible := program.body pc kind pc next self
  omega

abbrev BodyObservation (states groups length : Nat) :=
  LookKind → Fin states → Configuration states groups length → Option (Configuration states groups length)

def advance {length : Nat} (direction : Direction) (position : Fin (length + 1)) :
    Option (Fin (length + 1)) :=
  match direction with
  | .forward => if h : position.val < length then some ⟨position.val + 1, by omega⟩ else none
  | .reverse => if h : 0 < position.val then some ⟨position.val - 1, by omega⟩ else none

def consumed {length : Nat} (input : Fin length → Nat) (direction : Direction)
    (position : Fin (length + 1)) : Option Nat :=
  match direction with
  | .forward => if h : position.val < length then some (input ⟨position.val, h⟩) else none
  | .reverse => if h : 0 < position.val then some (input ⟨position.val - 1, by omega⟩) else none

def observe {states groups length : Nat} (kind : LookKind)
    (input : Configuration states groups length) (result : Option (Configuration states groups length))
    (next : Fin states) : Action (Configuration states groups length) Unit :=
  match kind.negative, result with
  | false, some selected => .next { input with pc := next, captures := selected.captures }
  | true, none => .next { input with pc := next }
  | _, _ => .dead

/-- Context bodies are supplied as completed observations. Work-bounded body
evaluation must retain its own incomplete constructor before using this map. -/
def action {states groups length : Nat} (interpretation : Interpretation)
    (input : Fin length → Nat) (direction : Direction)
    (program : Fin states → Instruction states groups) (body : BodyObservation states groups length)
    (configuration : Configuration states groups length) : Action (Configuration states groups length) Unit :=
  match program configuration.pc with
  | .accept => .accept ()
  | .dead => .dead
  | .jump next => .next { configuration with pc := next }
  | .branch first second =>
      .branch { configuration with pc := first } { configuration with pc := second }
  | .consume contains next =>
      match consumed input direction configuration.position, advance direction configuration.position with
      | some scalar, some position =>
          if contains scalar then .next { configuration with pc := next, position := position } else .dead
      | _, _ => .dead
  | .assertion holds next =>
      if holds configuration.position then .next { configuration with pc := next } else .dead
  | .open group next => .next { configuration with pc := next, captures := openCapture configuration.captures group configuration.position }
  | .close group next => .next { configuration with pc := next, captures := closeCapture configuration.captures group configuration.position }
  | .backref group comparison next =>
      match backreference interpretation input direction comparison configuration.captures group configuration.position with
      | some position => .next { configuration with pc := next, position := position }
      | none => .dead
  | .look kind entry next => observe kind configuration (body kind entry configuration) next

theorem positive_observation_preserves_cursor {states groups length : Nat}
    (input selected : Configuration states groups length) (next : Fin states) :
    observe .ahead input (some selected) next =
      .next ⟨next, input.position, selected.captures⟩ := rfl

theorem negative_observation_exports_no_captures {states groups length : Nat}
    (input : Configuration states groups length) (next : Fin states) :
    observe .notAhead input none next = .next ⟨next, input.position, input.captures⟩ := rfl

/-- Lift the complete finite control state to an existing verified graph.
Input position is already inside Configuration; the auxiliary graph position
has exactly one value. No capture or position is erased by the memo key. -/
def graph {states groups length : Nat}
    (step : Configuration states groups length → Action (Configuration states groups length) Unit) :
    Configuration states groups length → RegexTaggedGraph.Node (Configuration states groups length) Unit Unit Unit :=
  fun configuration => match step configuration with
    | .accept tag => .accept tag
    | .dead => .dead
    | .next next => .jump next
    | .branch first second => .choice first second

def probe : OrderedGraphSearch.Probe Unit Unit 0 := ⟨fun _ _ => false, fun _ _ => false⟩

def initial {states groups length : Nat} (configuration : Configuration states groups length) :
    RegexTaggedGraph.Thread (Configuration states groups length) 0 :=
  ⟨(configuration, 0), fun _ => none, []⟩

def run {states groups length : Nat}
    (step : Configuration states groups length → Action (Configuration states groups length) Unit)
    (eligible : Configuration states groups length → Bool) (fuel : Nat)
    (configuration : Configuration states groups length) :=
  RegexMemoizedSearch.taggedSearch (graph step) probe (fun point => eligible point.1) fuel (initial configuration)

theorem run_selected_iff {states groups length : Nat}
    (step : Configuration states groups length → Action (Configuration states groups length) Unit)
    (eligible : Configuration states groups length → Bool)
    (first : Configuration states groups length)
    (last : RegexTaggedGraph.Thread (Configuration states groups length) 0) (fuel : Nat)
    (enough : Fintype.card (OrderedGraphSearch.Point (Configuration states groups length) 0) + 1 < fuel) :
    run step eligible fuel first = .found last () ↔
      RegexSelectionCorrespondence.LeastSimple (graph step) probe
        (fun thread => eligible thread.point.1) (initial first) last ∧
      RegexPikeVM.terminal (graph step) last = some () :=
  RegexMemoizedSearch.taggedSearch_leastSimple _ _ _ _ _ _ _ enough

theorem run_absent_iff {states groups length : Nat}
    (step : Configuration states groups length → Action (Configuration states groups length) Unit)
    (eligible : Configuration states groups length → Bool)
    (first : Configuration states groups length) (fuel : Nat)
    (enough : Fintype.card (OrderedGraphSearch.Point (Configuration states groups length) 0) + 1 < fuel) :
    (∃ seen, run step eligible fuel first = .absent seen) ↔
      ¬ ∃ code points last tag,
        RegexSelectionCorrespondence.Trace (graph step) probe (fun thread => eligible thread.point.1)
          (initial first) code points last tag :=
  RegexMemoizedSearch.taggedSearch_absent_iff _ _ _ _ _ enough

theorem run_ne_incomplete {states groups length : Nat}
    (step : Configuration states groups length → Action (Configuration states groups length) Unit)
    (eligible : Configuration states groups length → Bool)
    (first : Configuration states groups length) (fuel : Nat)
    (enough : Fintype.card (OrderedGraphSearch.Point (Configuration states groups length) 0) + 1 < fuel) :
    run step eligible fuel first ≠ .incomplete :=
  RegexMemoizedSearch.taggedSearch_ne_incomplete _ _ _ _ _ enough

namespace Controls

private def interpretation : Interpretation := ⟨id⟩
private def input : Fin 2 → Nat := fun index => if index.val = 0 then 97 else 98
private def capturedA : Captures 1 2 := fun _ => .closed 0 1
private def capturedB : Captures 1 2 := fun _ => .closed 1 2

theorem backreference_reads_capture :
    backreference interpretation input .forward .exact capturedA 0 0 = some 1 ∧
    backreference interpretation input .forward .exact capturedB 0 0 = none := by decide

theorem same_point_different_futures :
    (Configuration.mk (0 : Fin 1) (0 : Fin 3) capturedA).pc =
      (Configuration.mk (0 : Fin 1) (0 : Fin 3) capturedB).pc ∧
    (Configuration.mk (0 : Fin 1) (0 : Fin 3) capturedA).position =
      (Configuration.mk (0 : Fin 1) (0 : Fin 3) capturedB).position ∧
    backreference interpretation input .forward .exact capturedA 0 0 ≠
      backreference interpretation input .forward .exact capturedB 0 0 := by decide

theorem reverse_backreference_keeps_original_text_order :
    backreference interpretation input .reverse .exact (fun _ : Fin 1 => .closed 0 2) 0 2 = some 0 := by decide

theorem reverse_capture_is_normalized :
    closeCapture (openCapture capturedA 0 2) 0 0 0 = .closed 0 2 := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.RegexDependentObservation
