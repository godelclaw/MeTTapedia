import Mettapedia.Machines.CMemory.ExecutableStorage
import Mettapedia.GSLT.Distinction.ProductiveBlocks

/-!
# Scalar-cell primitive execution through a prefix/residual interface

The explicit state retains the primitive program, its executable memory and
pending allocation choices. Every accepted operation emits its dependent
response with the exact before/after records. A refused allocation identity
suspends for another choice; an unsafe primitive finishes with its complete
state. Neither case is silently replaced by a successful operation.

This is the existing memory primitive language, not the whole C11 abstract
machine. Its source meaning is the independently defined resource-action
semantics of `CMemory.CProg`. Source C expressions, calls and loops require
their own language transitions and representation contracts.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.ProductiveBlocks

open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open ExecutableStorage

variable {V Answer : Type}

structure State (V Answer : Type) where
  control : CProg V Answer
  storage : Storage V
  choices : List AllocationChoice

structure Finished (V Answer : Type) where
  answer : Answer
  storage : Storage V
  choices : List AllocationChoice

inductive Verdict (V Answer : Type) where
  | returned (result : Finished V Answer)
  | fault (saved : State V Answer)

structure Receipt (V : Type) where
  operation : Op V
  response : operation.Ret
  before : Storage V
  after : Storage V

structure AllocationRequest (V : Type) where
  operation : Op V
  rejected : AllocationChoice

/-- Nonallocating operations do not consume allocator choices. -/
def takeChoice (operation : Op V) (choices : List AllocationChoice) :
    AllocationChoice × List AllocationChoice :=
  match operation with
  | .malloc _ | .realloc _ _ =>
      match choices with
      | [] => (.failure, [])
      | choice :: rest => (choice, rest)
  | _ => (.failure, choices)

def prepareChoices (operation : Op V) (choice : AllocationChoice)
    (following : List AllocationChoice) : List AllocationChoice :=
  match operation with
  | .malloc _ | .realloc _ _ => choice :: following
  | _ => following

theorem prepared_tail (operation : Op V) (choice : AllocationChoice)
    (following : List AllocationChoice) :
    (takeChoice operation (prepareChoices operation choice following)).2 = following := by
  cases operation <;> rfl

theorem prepared_perform (storage : Storage V) (operation : Op V)
    (choice : AllocationChoice) (following : List AllocationChoice) :
    perform storage (takeChoice operation (prepareChoices operation choice following)).1 operation =
      perform storage choice operation := by
  cases operation <;> rfl

def advance (state : State V Answer) :
    Transition (State V Answer) (Receipt V) (Verdict V Answer) (AllocationRequest V) :=
  match state.control with
  | .ret answer => .finish (.returned ⟨answer, state.storage, state.choices⟩)
  | .call operation next =>
      let selected := takeChoice operation state.choices
      match perform state.storage selected.1 operation with
      | some (response, storage) =>
          .publish [⟨operation, response, state.storage, storage⟩]
            ⟨next response, storage, selected.2⟩
      | none =>
          match perform state.storage .failure operation with
          | none => .finish (.fault state)
          | some _ => .call ⟨operation, selected.1⟩ { state with choices := selected.2 }

def machine : Machine (State V Answer) (Receipt V) (Verdict V Answer) (AllocationRequest V) where
  step state := some (advance state)

/-- Allocate retries and unsafe memory preserve the complete saved program.
Successful finite runs have the actual source program's logical result and
the constructed complete resulting ownership heap. -/
theorem returned_sound (fuel : Nat) (initial : State V Answer) (final : Finished V Answer)
    (completed : (machine.run fuel initial).2 = .finished (.returned final)) :
    initial.control.Runs (act (L := Excl (Option V)))
      (heap initial.storage) final.answer (heap final.storage) := by
  induction fuel generalizing initial with
  | zero => simp [Machine.run] at completed
  | succ fuel ih =>
      rcases initial with ⟨control, storage, choices⟩
      cases control with
      | ret answer =>
          have identified : Finished.mk answer storage choices = final := by
            simpa [Machine.run, machine, advance] using completed
          cases identified
          exact ⟨rfl, rfl⟩
      | call operation next =>
          cases selected : takeChoice operation choices with
          | mk choice rest =>
              cases executed : perform storage choice operation with
              | none =>
                  cases fallback : perform storage .failure operation <;>
                    simp [Machine.run, machine, advance, selected, executed, fallback] at completed
              | some result =>
                  rcases result with ⟨response, saved⟩
                  have child :
                      (machine.run fuel (State.mk (next response) saved rest)).2 =
                        .finished (.returned final) := by
                    simpa [Machine.run, machine, advance, selected, executed] using completed
                  exact ⟨response, heap saved,
                    (perform_sound storage saved choice operation response executed).2,
                    ih ⟨next response, saved, rest⟩ child⟩

/-- An accepted primitive is one visible transition followed by precisely
its response-indexed child, updated memory and unused allocator choices. -/
theorem accepted_child (operation : Op V) (next : operation.Ret → CProg V Answer)
    (storage saved : Storage V) (choice : AllocationChoice) (response : operation.Ret)
    (following : List AllocationChoice) (fuel : Nat)
    (executed : perform storage choice operation = some (response, saved)) :
    (machine.run (fuel + 1)
      (State.mk (.call operation next) storage (prepareChoices operation choice following))).2 =
      (machine.run fuel (State.mk (next response) saved following)).2 := by
  simp [Machine.run, machine, advance, prepared_perform, prepared_tail, executed]

/-- Every safe finite source execution is realized by a constructed sequence
of allocator choices and this executable driver. Safety supplies authority
for each logical action; it is not a correspondence assumption. -/
theorem source_execution_realized (program : CProg V Answer) (storage : Storage V)
    (answer : Answer) (after : Heap (Excl (Option V)))
    (safe : program.Safe (act (L := Excl (Option V))) (heap storage))
    (ran : program.Runs (act (L := Excl (Option V))) (heap storage) answer after) :
    ∃ choices fuel final,
      final.answer = answer ∧ heap final.storage = after ∧
        (machine.run fuel (State.mk program storage choices)).2 =
          .finished (.returned final) := by
  induction program generalizing storage answer after with
  | ret value =>
      obtain ⟨sameAnswer, sameHeap⟩ := ran
      subst answer
      exact ⟨[], 1, ⟨value, storage, []⟩, rfl, sameHeap, rfl⟩
  | call operation next ih =>
      obtain ⟨localSafe, followingSafe⟩ := safe
      obtain ⟨response, intermediate, stepped, followingRun⟩ := ran
      obtain ⟨choice, saved, executed, represented⟩ :=
        perform_complete storage operation response intermediate localSafe stepped
      have childSafe : (next response).Safe (act (L := Excl (Option V))) (heap saved) := by
        rw [represented]
        exact followingSafe response intermediate stepped
      have childRun : (next response).Runs (act (L := Excl (Option V)))
          (heap saved) answer after := by
        rw [represented]
        exact followingRun
      obtain ⟨choices, fuel, final, correctAnswer, correctHeap, complete⟩ :=
        ih response saved answer after childSafe childRun
      refine ⟨prepareChoices operation choice choices, fuel + 1, final,
        correctAnswer, correctHeap, ?_⟩
      rw [accepted_child operation next storage saved choice response choices fuel executed]
      exact complete

def ValidReceipt (receipt : Receipt V) : Prop :=
  (act (L := Excl (Option V)) receipt.operation).Safe (heap receipt.before) ∧
    (act (L := Excl (Option V)) receipt.operation).Step
      (heap receipt.before) receipt.response (heap receipt.after)

/-- Each emitted occurrence has its own justified memory transition. -/
theorem run_receipts_valid (fuel : Nat) (initial : State V Answer) :
    ∀ receipt ∈ (machine.run fuel initial).1, ValidReceipt receipt := by
  induction fuel generalizing initial with
  | zero => simp [Machine.run]
  | succ fuel ih =>
      rcases initial with ⟨control, storage, choices⟩
      cases control with
      | ret answer => simp [Machine.run, machine, advance]
      | call operation next =>
          cases selected : takeChoice operation choices with
          | mk choice rest =>
              cases executed : perform storage choice operation with
              | none =>
                  cases fallback : perform storage .failure operation <;>
                    simp [Machine.run, machine, advance, selected, executed, fallback]
              | some result =>
                  rcases result with ⟨response, saved⟩
                  simp only [Machine.run, machine, advance, selected, executed,
                    List.singleton_append, List.mem_cons]
                  intro receipt occurrence
                  rcases occurrence with rfl | remaining
                  · exact perform_sound storage saved choice operation response executed
                  · exact ih ⟨next response, saved, rest⟩ receipt remaining

theorem resume_after_prefix (first second : Nat) (initial saved : State V Answer)
    (receipts : List (Receipt V))
    (paused : machine.run first initial = (receipts, .exhausted saved)) :
    machine.run (first + second) initial =
      (receipts ++ (machine.run second saved).1, (machine.run second saved).2) :=
  machine.established_and_pending first second initial saved receipts paused

def price (state : State V Answer) : Nat :=
  match state.control with
  | .ret _ => 0
  | .call _ _ => 1

/-- Administrative stuttering is absent at primitive-inspection granularity.
The internal work of finite record operations is priced separately. This is
not a termination theorem for ordinary C source programs. -/
def productive : (machine (V := V) (Answer := Answer)).Productive where
  rank _ := 0
  silent_decreases := by
    intro state following stepped
    rcases state with ⟨control, storage, choices⟩
    cases control with
    | ret answer => simp [machine, advance] at stepped
    | call operation next =>
        cases selected : takeChoice operation choices with
        | mk choice rest =>
            cases executed : perform storage choice operation with
            | none =>
                cases fallback : perform storage .failure operation <;>
                  simp [machine, advance, selected, executed, fallback] at stepped
            | some result =>
                rcases result with ⟨response, saved⟩
                simp [machine, advance, selected, executed] at stepped
  moves state := Option.some_ne_none (advance state)

end Mettapedia.Machines.CMemory.ProductiveBlocks
