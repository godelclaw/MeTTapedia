import Mettapedia.OSLF.NativeTypes.Certificates.FiniteTree
import Mettapedia.Machines.ProductiveCoreAdapters
import Mettapedia.GSLT.Distinction.SimulationComposition

/-!
# Retained checking of the original finite proof trees

Each transition checks one original rule conclusion and schedules its ordered
child occurrences. No inference rule, judgment or binding operation is changed.
A refused head and its suffix remain available; completed work has an empty
schedule. The cost account counts inspected proof occurrences. Comparing a
judgment and constructing its child schedule have their own representation
costs, so one occurrence is not claimed to take constant physical time.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Certificates.TreeExecution

open Mettapedia.Machines
open Mettapedia.GSLT.Distinction.ProductiveBlocks

variable {P : Presentation.{0}} [DecidableEq P.Judgment]

def nodes : Tree P → Nat
  | .node _ children => 1 + (List.ofFn fun position => nodes (children position)).sum

omit [DecidableEq P.Judgment] in
 theorem nodes_pos (tree : Tree P) : 0 < nodes tree := by
  cases tree
  simp [nodes]

structure Task (P : Presentation.{0}) where
  tree : Tree P
  wanted : P.Judgment

def children (rule : P.Rule) (trees : Fin (P.premises rule).length → Tree P) : List (Task P) :=
  List.ofFn fun position => ⟨trees position, (P.premises rule).get position⟩

def Task.check (task : Task P) : Bool := task.tree.check task.wanted

def pendingNodes (tasks : List (Task P)) : Nat := (tasks.map (fun task => nodes task.tree)).sum

structure Work (P : Presentation.{0}) where
  pending : List (Task P)
  inspected : Nat
  refused : Bool

def start (tree : Tree P) (wanted : P.Judgment) : Work P := ⟨[⟨tree, wanted⟩], 0, false⟩

def Work.settled (work : Work P) : Bool := work.refused || work.pending.isEmpty

def Work.accepted (work : Work P) : Bool := !work.refused && work.pending.isEmpty

def Work.meaning (work : Work P) : Bool := !work.refused && work.pending.all Task.check

/-- Completed and refused states are fixed points of the specified strategy. -/
def tick (work : Work P) : Work P :=
  if work.refused then work else
    match work.pending with
    | [] => work
    | ⟨.node rule trees, wanted⟩ :: rest =>
        if P.conclusion rule = wanted then
          ⟨children rule trees ++ rest, work.inspected + 1, false⟩
        else ⟨work.pending, work.inspected + 1, true⟩

theorem children_check (rule : P.Rule) (trees : Fin (P.premises rule).length → Tree P) :
    (children rule trees).all Task.check =
      decide (∀ position, (trees position).check ((P.premises rule).get position) = true) := by
  apply Bool.eq_iff_iff.mpr
  simp [children, List.all_eq_true, List.mem_ofFn, Task.check]

theorem tick_meaning (work : Work P) : (tick work).meaning = work.meaning := by
  rcases work with ⟨pending, inspected, refused⟩
  cases refused with
  | true => rfl
  | false =>
      cases pending with
      | nil => rfl
      | cons task rest =>
          rcases task with ⟨tree, wanted⟩
          cases tree with
          | node rule trees =>
              by_cases correct : P.conclusion rule = wanted
              · simp [tick, correct, Work.meaning, Task.check, Tree.check,
                  List.all_append, children_check]
              · simp [tick, correct, Work.meaning, Task.check, Tree.check]

theorem tick_settled (work : Work P) (settled : work.settled = true) : tick work = work := by
  rcases work with ⟨pending, inspected, refused⟩
  cases refused with
  | true => rfl
  | false =>
      cases pending with
      | nil => rfl
      | cons task rest => simp [Work.settled] at settled

omit [DecidableEq P.Judgment] in
 theorem pendingNodes_eq_zero (tasks : List (Task P)) : pendingNodes tasks = 0 ↔ tasks = [] := by
  cases tasks with
  | nil => simp [pendingNodes]
  | cons task rest =>
      have positive := nodes_pos task.tree
      simp only [pendingNodes, List.map_cons, List.sum_cons]
      constructor
      · intro impossible
        omega
      · intro impossible
        cases impossible

theorem tick_nodes (work : Work P) (openWork : work.settled = false) :
    (tick work).settled = true ∨
      pendingNodes (tick work).pending + 1 = pendingNodes work.pending := by
  rcases work with ⟨pending, inspected, refused⟩
  cases refused with
  | true => simp [Work.settled] at openWork
  | false =>
      cases pending with
      | nil => simp [Work.settled] at openWork
      | cons task rest =>
          rcases task with ⟨tree, wanted⟩
          cases tree with
          | node rule trees =>
              by_cases correct : P.conclusion rule = wanted
              · right
                simp [tick, correct, pendingNodes, children, nodes, List.map_ofFn,
                  List.sum_append, Function.comp_def, Nat.add_comm, Nat.add_left_comm]
              · left
                simp [tick, correct, Work.settled]

def advance (budget : Nat) (work : Work P) : Work P := tick^[budget] work

theorem advance_add (first second : Nat) (work : Work P) :
    advance (first + second) work = advance second (advance first work) := by
  change tick^[first + second] work = tick^[second] (tick^[first] work)
  rw [Nat.add_comm first second, Function.iterate_add_apply]

theorem advance_meaning (budget : Nat) (work : Work P) :
    (advance budget work).meaning = work.meaning := by
  induction budget generalizing work with
  | zero => rfl
  | succ budget ih =>
      change (tick^[budget] (tick work)).meaning = work.meaning
      exact (ih (tick work)).trans (tick_meaning work)

theorem advance_settled (budget : Nat) (work : Work P) (settled : work.settled = true) :
    advance budget work = work :=
  Function.iterate_fixed (tick_settled work settled) budget

/-- Every finite tree settles after at most one inspection per occurrence.
Refusal may settle sooner while retaining the unprocessed suffix. -/
theorem settled_within (budget : Nat) (work : Work P)
    (enough : pendingNodes work.pending ≤ budget) : (advance budget work).settled = true := by
  induction budget generalizing work with
  | zero =>
      have empty := (pendingNodes_eq_zero work.pending).mp (Nat.eq_zero_of_le_zero enough)
      simp [advance, Work.settled, empty]
  | succ budget ih =>
      cases settled : work.settled with
      | true => rw [advance_settled _ _ settled]; exact settled
      | false =>
          change (advance budget (tick work)).settled = true
          rcases tick_nodes work settled with finished | smaller
          · rw [advance_settled _ _ finished]; exact finished
          · exact ih (tick work) (by omega)

theorem settled_meaning (work : Work P) (settled : work.settled = true) :
    work.accepted = work.meaning := by
  rcases work with ⟨pending, inspected, refused⟩
  cases refused with
  | true => simp [Work.accepted, Work.meaning]
  | false =>
      have empty : pending = [] := by simpa [Work.settled] using settled
      simp [empty, Work.accepted, Work.meaning]

/-- Exactness relates the independent recursive checker to the actual
worklist strategy, with no trusted whole-proof check hidden inside a tick. -/
theorem accepted_iff (tree : Tree P) (wanted : P.Judgment) :
    (advance (nodes tree) (start tree wanted)).accepted = tree.check wanted := by
  rw [settled_meaning _ (settled_within _ _ (by simp [pendingNodes, start])), advance_meaning]
  simp [start, Work.meaning, Task.check]

def core : AnswerMachineCore (Tree P × P.Judgment) (Work P) where
  State := Work P
  load input := start input.1 input.2
  step work := if work.settled then none else some (tick work)
  answer work := if work.settled then some work else none
  answer_final := by intro work result; split <;> simp_all

/-- An object of the existing checking-machine category at the original
occurrence and residual-work interface. -/
def object : ObservedMachine (ProductiveCoreAdapters.Occurrence (Work P)) (Work P) Empty :=
  ObservedMachine.of (ProductiveCoreAdapters.answerMachine (core (P := P)))

theorem retainedTick_eq : ProductiveCoreAdapters.retainedTick (core (P := P)).toMachineCore = tick := by
  funext work
  cases settled : work.settled with
  | false => simp [ProductiveCoreAdapters.retainedTick, core, settled]; rfl
  | true => simp [ProductiveCoreAdapters.retainedTick, core, settled, tick_settled work settled]; rfl

/-- Actual productive-block execution returns the same verdict as recursive
tree checking within the occurrence budget plus one finishing transition. -/
theorem machine_completes (tree : Tree P) (wanted : P.Judgment) :
    ∃ fuel events report, fuel ≤ nodes tree + 1 ∧
      (object (P := P)).machine.run fuel (start tree wanted) = (events, .finished report) ∧
      report.accepted = tree.check wanted := by
  let final := advance (nodes tree) (start tree wanted)
  have settled : final.settled = true := settled_within _ _ (by simp [start, pendingNodes])
  have observed : (core (P := P)).answer final = some final := by simp [core, settled]
  have finalTick : (ProductiveCoreAdapters.retainedTick (core (P := P)).toMachineCore)^[nodes tree]
      (start tree wanted) = final := by rw [retainedTick_eq]; rfl
  obtain ⟨fuel, events, bounded, finished⟩ := ProductiveCoreAdapters.retainedTick_finished
    (core (P := P)) (nodes tree) (start tree wanted) final (by simpa [finalTick] using observed)
  exact ⟨fuel, events, final, bounded, finished, accepted_iff tree wanted⟩

theorem finished_accepted (tree : Tree P) (wanted : P.Judgment) {fuel : Nat}
    {events : List (ProductiveCoreAdapters.Occurrence (Work P))} {report : Work P}
    (finished : (object (P := P)).machine.run fuel (start tree wanted) = (events, .finished report)) :
    report.accepted = tree.check wanted := by
  obtain ⟨otherFuel, otherEvents, otherReport, _, otherFinished, exactCheck⟩ := machine_completes tree wanted
  have first : (core (P := P)).Produces (tree, wanted) report :=
    (ProductiveCoreAdapters.produces_iff_finished (core (P := P)) (tree, wanted) report).mpr
      ⟨fuel, events, finished⟩
  have second : (core (P := P)).Produces (tree, wanted) otherReport :=
    (ProductiveCoreAdapters.produces_iff_finished (core (P := P)) (tree, wanted) otherReport).mpr
      ⟨otherFuel, otherEvents, otherFinished⟩
  exact (congrArg Work.accepted ((core (P := P)).produces_unique first second)).trans exactCheck

end Mettapedia.OSLF.NativeTypes.Certificates.TreeExecution
