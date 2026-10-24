import Mettapedia.GSLT.LanguageDef.ProofSystemExecution
import Mettapedia.OSLF.Syntax.BindingWireBinary
import Mettapedia.Logic.DerivationGraph
import Mettapedia.Computability.WordTemplateMachine
import Mettapedia.Computability.WordHomomorphismMachine
import Mettapedia.Computability.RetainedWordExecution
import Mettapedia.Computability.WordEqualityMachine
import Mettapedia.Computability.BinaryStackArithmetic
import Mettapedia.Computability.BinaryWordComparison
import Mettapedia.Computability.BinaryWordAddition

/-!
# Finite-machine resolution of shared binary references

The resolver compares complete binary keys against an ordered root table.
It restores the submitted key between rows and returns the first matching
physical reference. A missing key is refused after scanning the finite table.
The table encoder uses the same five-symbol alphabet and numeric delimiters
as the original certificate storage codec.

The composite finite-machine definitions are reducible and macro-inlined.
Instruction projections retain their original computation without allocating
unused finite-state enumeration tables at module initialization. Their fields,
counted executions and existing instruction-agreement theorems are unchanged.
-/
set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.SharedReferenceExecution
open _root_.Computability Turing StateTransition
open ProofSystems Polynomial
open Turing.TM2.Stmt

abbrev Alphabet := Mettapedia.OSLF.Binding.WireCodec.Binary.Alphabet

def bit (value : Bool) : Alphabet := if value then 1 else 0

def field (word : List Bool) : List Alphabet := word.map bit

def table : List (List Bool × List Bool) → List Alphabet
  | [] => [4]
  | (key, value) :: rest => 3 :: field key ++ 2 :: field value ++ 2 :: table rest

def packet (key : List Bool) (rows : List (List Bool × List Bool)) : List Alphabet :=
  field key ++ 2 :: table rows

def lookup (key : List Bool) : List (List Bool × List Bool) → Option (List Bool)
  | [] => none
  | (candidate, value) :: rest => if key = candidate then some value else lookup key rest

def output : Option (List Bool) → List Alphabet
  | none => [0]
  | some value => 1 :: field value ++ [2]

def isBit (value : Option Alphabet) : Bool := value == some 0 || value == some 1

set_option backward.isDefEq.respectTransparency false in
inductive Stack where
  | input | query | temporary | result
  deriving DecidableEq, Fintype

set_option backward.isDefEq.respectTransparency false in
inductive Phase where
  | scanQuery | restoreQuery | startRow | compareKey | finishKey | restoreKey | scanValue
  | acceptInput | acceptQuery | restoreOutput
  | rejectInput | rejectQuery | rejectTemporary | rejectResult
  deriving DecidableEq, Fintype

abbrev Control := Option Alphabet × Option Alphabet × Bool

def initial : Control := (none, none, true)

/-- All control registers range over finite sets. Binary fields remain on
stacks; no machine-word or unbounded numeric register is used. -/
def machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .input
  Γ _ := Alphabet
  Λ := Phase
  main := .scanQuery
  σ := Control
  initialState := initial
  m phase := match phase with
  | .scanQuery => pop .input (fun state value => (value, state.2))
      (branch (fun state => state.1 == some 2)
        (goto fun _ => .restoreQuery)
        (branch (fun state => isBit state.1)
          (push .temporary (fun state => state.1.getD 2) (goto fun _ => .scanQuery))
          (goto fun _ => .rejectInput)))
  | .restoreQuery => pop .temporary (fun state value => (value, state.2))
      (branch (fun state => state.1.isSome)
        (push .query (fun state => state.1.getD 2) (goto fun _ => .restoreQuery))
        (goto fun _ => .startRow))
  | .startRow => pop .input (fun _ value => (value, none, true))
      (branch (fun state => state.1 == some 3)
        (goto fun _ => .compareKey)
        (goto fun _ => .rejectInput))
  | .compareKey => pop .input (fun state value => (value, state.2))
      (branch (fun state => state.1 == some 2)
        (goto fun _ => .finishKey)
        (branch (fun state => isBit state.1)
          (pop .query (fun state value => (state.1, value, state.2.2 && state.1 == value))
            (branch (fun state => state.2.1.isSome)
              (push .temporary (fun state => state.2.1.getD 2) (goto fun _ => .compareKey))
              (goto fun _ => .compareKey)))
          (goto fun _ => .rejectInput)))
  | .finishKey => pop .query (fun state value => (value, state.2.1, state.2.2))
      (branch (fun state => state.1.isSome)
        (push .temporary (fun state => state.1.getD 2)
          (load (fun state => (none, state.2.1, false)) (goto fun _ => .finishKey)))
        (goto fun _ => .restoreKey))
  | .restoreKey => pop .temporary (fun state value => (value, state.2))
      (branch (fun state => state.1.isSome)
        (push .query (fun state => state.1.getD 2) (goto fun _ => .restoreKey))
        (load (fun state => (none, none, state.2.2)) (goto fun _ => .scanValue)))
  | .scanValue => pop .input (fun state value => (value, state.2))
      (branch (fun state => state.1 == some 2)
        (branch (fun state => state.2.2) (goto fun _ => .acceptInput) (goto fun _ => .startRow))
        (branch (fun state => isBit state.1)
          (branch (fun state => state.2.2)
            (push .result (fun state => state.1.getD 2) (goto fun _ => .scanValue))
            (goto fun _ => .scanValue))
          (goto fun _ => .rejectInput)))
  | .acceptInput => pop .input (fun state value => (value, state.2))
      (branch (fun state => state.1.isSome) (goto fun _ => .acceptInput) (goto fun _ => .acceptQuery))
  | .acceptQuery => pop .query (fun state value => (value, state.2))
      (branch (fun state => state.1.isSome) (goto fun _ => .acceptQuery)
        (push .input (fun _ => 2) (goto fun _ => .restoreOutput)))
  | .restoreOutput => pop .result (fun state value => (value, state.2))
      (branch (fun state => state.1.isSome)
        (push .input (fun state => state.1.getD 2) (goto fun _ => .restoreOutput))
        (push .input (fun _ => 1) (load (fun _ => initial) halt)))
  | .rejectInput => pop .input (fun state value => (value, state.2))
      (branch (fun state => state.1.isSome) (goto fun _ => .rejectInput) (goto fun _ => .rejectQuery))
  | .rejectQuery => pop .query (fun state value => (value, state.2))
      (branch (fun state => state.1.isSome) (goto fun _ => .rejectQuery) (goto fun _ => .rejectTemporary))
  | .rejectTemporary => pop .temporary (fun state value => (value, state.2))
      (branch (fun state => state.1.isSome) (goto fun _ => .rejectTemporary) (goto fun _ => .rejectResult))
  | .rejectResult => pop .result (fun state value => (value, state.2))
      (branch (fun state => state.1.isSome) (goto fun _ => .rejectResult)
        (push .input (fun _ => 0) (load (fun _ => initial) halt)))

def config (phase : Option Phase) (state : Control) (input query temporary result : List Alphabet) : machine.Cfg where
  l := phase
  var := state
  stk stack := match (show Stack from stack) with
    | .input => input | .query => query | .temporary => temporary | .result => result

private theorem isBit_bit (value : Bool) : isBit (some (bit value)) = true := by
  cases value <;> decide

private theorem bit_ne_end (value : Bool) : (some (bit value) == some (2 : Alphabet)) = false := by
  cases value <;> decide

private theorem bit_match (left right : Bool) : ((some (bit left) : Option Alphabet) == some (bit right)) = (left == right) := by
  cases left <;> cases right <;> decide

local macro "check_step" : tactic => `(tactic| (
  simp [FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux, Function.update]
  congr 2
  funext stack
  cases stack <;> simp [Function.update]))

theorem scan_bit (state : Control) (head : Bool) (tail query temporary result : List Alphabet) :
    machine.step (config (some .scanQuery) state (bit head :: tail) query temporary result) =
      some (config (some .scanQuery) (some (bit head), state.2) tail query (bit head :: temporary) result) := by
  have first := isBit_bit head
  have second := bit_ne_end head
  simp [first, second, FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux, Function.update]
  congr 2
  funext stack
  cases stack <;> simp [Function.update]

theorem scan_end (state : Control) (tail query temporary result : List Alphabet) :
    machine.step (config (some .scanQuery) state (2 :: tail) query temporary result) =
      some (config (some .restoreQuery) (some 2, state.2) tail query temporary result) := by check_step

theorem restore_query_cons (state : Control) (head : Alphabet) (input query tail result : List Alphabet) :
    machine.step (config (some .restoreQuery) state input query (head :: tail) result) =
      some (config (some .restoreQuery) (some head, state.2) input (head :: query) tail result) := by check_step

theorem restore_query_nil (state : Control) (input query result : List Alphabet) :
    machine.step (config (some .restoreQuery) state input query [] result) =
      some (config (some .startRow) (none, state.2) input query [] result) := by check_step

theorem start_row (state : Control) (input query : List Alphabet) :
    machine.step (config (some .startRow) state (3 :: input) query [] []) =
      some (config (some .compareKey) (some 3, none, true) input query [] []) := by check_step

theorem compare_cons (state : Control) (key query : Bool) (input queryTail temporary : List Alphabet) :
    machine.step (config (some .compareKey) state (bit key :: input) (bit query :: queryTail) temporary []) =
      some (config (some .compareKey) (some (bit key), some (bit query), state.2.2 && (key == query))
        input queryTail (bit query :: temporary) []) := by
  have first := isBit_bit key
  have second := bit_ne_end key
  have same := bit_match key query
  simp [first, second, same, FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux, Function.update]
  congr 2
  funext stack
  cases stack <;> simp [Function.update]

theorem compare_nil (state : Control) (key : Bool) (input temporary : List Alphabet) :
    machine.step (config (some .compareKey) state (bit key :: input) [] temporary []) =
      some (config (some .compareKey) (some (bit key), none, false) input [] temporary []) := by
  have first := isBit_bit key
  have second := bit_ne_end key
  simp [first, second, FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux, Function.update]
  congr 2
  funext stack
  cases stack <;> simp [Function.update]

theorem compare_end (state : Control) (input query temporary : List Alphabet) :
    machine.step (config (some .compareKey) state (2 :: input) query temporary []) =
      some (config (some .finishKey) (some 2, state.2) input query temporary []) := by check_step

theorem finish_key_cons (state : Control) (head : Alphabet) (input tail temporary : List Alphabet) :
    machine.step (config (some .finishKey) state input (head :: tail) temporary []) =
      some (config (some .finishKey) (none, state.2.1, false) input tail (head :: temporary) []) := by check_step

theorem finish_key_nil (state : Control) (input temporary : List Alphabet) :
    machine.step (config (some .finishKey) state input [] temporary []) =
      some (config (some .restoreKey) (none, state.2) input [] temporary []) := by check_step

theorem restore_key_cons (state : Control) (head : Alphabet) (input query tail : List Alphabet) :
    machine.step (config (some .restoreKey) state input query (head :: tail) []) =
      some (config (some .restoreKey) (some head, state.2) input (head :: query) tail []) := by check_step

theorem restore_key_nil (state : Control) (input query : List Alphabet) :
    machine.step (config (some .restoreKey) state input query [] []) =
      some (config (some .scanValue) (none, none, state.2.2) input query [] []) := by check_step

def finish_key_run (query temporary input : List Alphabet) (state : Control) :
    EvalsToInTime machine.step
      (config (some .finishKey) state input query temporary [])
      (some (config (some .restoreKey) (none, state.2.1, state.2.2 && decide (query = []))
        input [] (query.reverse ++ temporary) [])) (query.length + 1) := by
  induction query generalizing state temporary with
  | nil => simpa using SymbolMapMachine.oneStep (finish_key_nil state input temporary)
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (finish_key_cons state head input tail temporary)
      have rest := ih (head :: temporary) (none, state.2.1, false)
      have run := EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest
      simpa using run

def restore_key_run (temporary query input : List Alphabet) (state : Control) :
    EvalsToInTime machine.step
      (config (some .restoreKey) state input query temporary [])
      (some (config (some .scanValue) (none, none, state.2.2)
        input (temporary.reverse ++ query) [] [])) (temporary.length + 1) := by
  induction temporary generalizing state query with
  | nil => simpa using SymbolMapMachine.oneStep (restore_key_nil state input query)
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (restore_key_cons state head input query tail)
      have rest := ih (head :: query) (some head, state.2)
      have run := EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest
      simpa using run

/-- Comparing one row restores the complete query, including its unused
suffix. Equality is accumulated through actual finite bit comparisons. -/
def compare_key_run (key query : List Bool) (temporary input : List Alphabet) (state : Control) :
    EvalsToInTime machine.step
      (config (some .compareKey) state (field key ++ 2 :: input) (field query) temporary [])
      (some (config (some .scanValue) (none, none, state.2.2 && decide (query = key))
        input (temporary.reverse ++ field query) [] []))
      (key.length + 2 * query.length + 2 * temporary.length + 3) := by
  induction key generalizing query state temporary with
  | nil =>
      have first := SymbolMapMachine.oneStep (compare_end state input (field query) temporary)
      have middle := finish_key_run (field query) temporary input (some 2, state.2)
      have last := restore_key_run ((field query).reverse ++ temporary) [] input
        (none, state.2.1, state.2.2 && decide (field query = []))
      have run := EvalsToInTime.trans _ 1 ((field query).length + 1) _ _ _ first middle
      have joined := EvalsToInTime.trans _ ((field query).length + 1 + 1)
        (((field query).reverse ++ temporary).length + 1) _ _ _ run last
      have simplified : EvalsToInTime machine.step
          (config (some .compareKey) state (field [] ++ 2 :: input) (field query) temporary [])
          (some (config (some .scanValue) (none, none, state.2.2 && decide (query = []))
            input (temporary.reverse ++ field query) [] []))
          (2 * query.length + temporary.length + 3) := by
        convert joined using 1
        all_goals simp [field, List.reverse_append, Nat.add_assoc]
        all_goals omega
      exact BinaryReferenceMachine.within simplified (by omega)
  | cons head tail ih =>
      cases query with
      | nil =>
          have first := SymbolMapMachine.oneStep (compare_nil state head (field tail ++ 2 :: input) temporary)
          have rest := ih [] temporary (some (bit head), none, false)
          have run := EvalsToInTime.trans _ 1 (tail.length + 0 + 2 * temporary.length + 3) _ _ _ first rest
          simpa [field, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run
      | cons queryHead queryTail =>
          have first := SymbolMapMachine.oneStep (compare_cons state head queryHead
            (field tail ++ 2 :: input) (field queryTail) temporary)
          have rest := ih queryTail (bit queryHead :: temporary)
            (some (bit head), some (bit queryHead), state.2.2 && (head == queryHead))
          have sameEquality : decide ((queryHead :: queryTail) = (head :: tail)) =
              ((head == queryHead) && decide (queryTail = tail)) := by
            cases head <;> cases queryHead <;> simp

          have run := EvalsToInTime.trans _ 1
            (tail.length + 2 * queryTail.length + 2 * (bit queryHead :: temporary).length + 3) _ _ _ first rest
          simp only [sameEquality]
          convert run using 1
          all_goals simp [field, Bool.and_assoc, List.reverse_cons, List.append_assoc]
          all_goals omega

theorem value_cons (saved other : Option Alphabet) (matched : Bool) (head : Bool)
    (input query result : List Alphabet) :
    machine.step (config (some .scanValue) (saved, other, matched) (bit head :: input) query [] result) =
      some (config (some .scanValue) (some (bit head), other, matched) input query []
        (if matched then bit head :: result else result)) := by
  have first := isBit_bit head
  have second := bit_ne_end head
  cases matched <;>
    simp [first, second, FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux, Function.update] <;>
    congr 2 <;> funext stack <;> cases stack <;> simp [Function.update]

theorem value_end (saved other : Option Alphabet) (matched : Bool) (input query result : List Alphabet) :
    machine.step (config (some .scanValue) (saved, other, matched) (2 :: input) query [] result) =
      some (config (some (if matched then .acceptInput else .startRow)) (some 2, other, matched) input query [] result) := by
  cases matched <;> check_step

def value_run (value : List Bool) (input query result : List Alphabet)
    (saved other : Option Alphabet) (matched : Bool) :
    EvalsToInTime machine.step
      (config (some .scanValue) (saved, other, matched) (field value ++ 2 :: input) query [] result)
      (some (config (some (if matched then .acceptInput else .startRow)) (some 2, other, matched)
        input query [] (if matched then (field value).reverse ++ result else result))) (value.length + 1) := by
  induction value generalizing saved result with
  | nil => simpa [field] using SymbolMapMachine.oneStep (value_end saved other matched input query result)
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (value_cons saved other matched head (field tail ++ 2 :: input) query result)
      have rest := ih (if matched then bit head :: result else result) (some (bit head))
      have run := EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest
      cases matched <;> simpa [field] using run

theorem accept_input_cons (state : Control) (head : Alphabet) (input query result : List Alphabet) :
    machine.step (config (some .acceptInput) state (head :: input) query [] result) =
      some (config (some .acceptInput) (some head, state.2) input query [] result) := by check_step

theorem accept_input_nil (state : Control) (query result : List Alphabet) :
    machine.step (config (some .acceptInput) state [] query [] result) =
      some (config (some .acceptQuery) (none, state.2) [] query [] result) := by check_step

def accept_input_run (input query result : List Alphabet) (state : Control) :
    EvalsToInTime machine.step (config (some .acceptInput) state input query [] result)
      (some (config (some .acceptQuery) (none, state.2) [] query [] result)) (input.length + 1) := by
  induction input generalizing state with
  | nil => exact SymbolMapMachine.oneStep (accept_input_nil state query result)
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (accept_input_cons state head tail query result)
      have rest := ih (some head, state.2)
      simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

theorem accept_query_cons (state : Control) (head : Alphabet) (query result : List Alphabet) :
    machine.step (config (some .acceptQuery) state [] (head :: query) [] result) =
      some (config (some .acceptQuery) (some head, state.2) [] query [] result) := by check_step

theorem accept_query_nil (state : Control) (result : List Alphabet) :
    machine.step (config (some .acceptQuery) state [] [] [] result) =
      some (config (some .restoreOutput) (none, state.2) [2] [] [] result) := by check_step

def accept_query_run (query result : List Alphabet) (state : Control) :
    EvalsToInTime machine.step (config (some .acceptQuery) state [] query [] result)
      (some (config (some .restoreOutput) (none, state.2) [2] [] [] result)) (query.length + 1) := by
  induction query generalizing state with
  | nil => exact SymbolMapMachine.oneStep (accept_query_nil state result)
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (accept_query_cons state head tail result)
      have rest := ih (some head, state.2)
      simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

theorem restore_output_cons (state : Control) (head : Alphabet) (input tail : List Alphabet) :
    machine.step (config (some .restoreOutput) state input [] [] (head :: tail)) =
      some (config (some .restoreOutput) (some head, state.2) (head :: input) [] [] tail) := by check_step

theorem restore_output_nil (state : Control) (input : List Alphabet) :
    machine.step (config (some .restoreOutput) state input [] [] []) =
      some (config none initial (1 :: input) [] [] []) := by check_step

def restore_output_run (result input : List Alphabet) (state : Control) :
    EvalsToInTime machine.step (config (some .restoreOutput) state input [] [] result)
      (some (config none initial (1 :: result.reverse ++ input) [] [] [])) (result.length + 1) := by
  induction result generalizing state input with
  | nil => simpa using SymbolMapMachine.oneStep (restore_output_nil state input)
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (restore_output_cons state head input tail)
      have rest := ih (head :: input) (some head, state.2)
      simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

def accepted_run (input query result : List Alphabet) (state : Control) :
    EvalsToInTime machine.step (config (some .acceptInput) state input query [] result)
      (some (config none initial (1 :: result.reverse ++ [2]) [] [] []))
      (input.length + query.length + result.length + 3) := by
  have first := accept_input_run input query result state
  have middle := accept_query_run query result (none, state.2)
  have last := restore_output_run result [2] (none, state.2)
  have run := EvalsToInTime.trans _ (input.length + 1) (query.length + 1) _ _ _ first middle
  convert EvalsToInTime.trans _ ((query.length + 1) + (input.length + 1))
    (result.length + 1) _ _ _ run last using 1
  omega

theorem reject_input_nil (state : Control) (query : List Alphabet) :
    machine.step (config (some .rejectInput) state [] query [] []) =
      some (config (some .rejectQuery) (none, state.2) [] query [] []) := by check_step

theorem reject_query_cons (state : Control) (head : Alphabet) (query : List Alphabet) :
    machine.step (config (some .rejectQuery) state [] (head :: query) [] []) =
      some (config (some .rejectQuery) (some head, state.2) [] query [] []) := by check_step

theorem reject_query_nil (state : Control) :
    machine.step (config (some .rejectQuery) state [] [] [] []) =
      some (config (some .rejectTemporary) (none, state.2) [] [] [] []) := by check_step

theorem reject_temporary_nil (state : Control) :
    machine.step (config (some .rejectTemporary) state [] [] [] []) =
      some (config (some .rejectResult) (none, state.2) [] [] [] []) := by check_step

theorem reject_result_nil (state : Control) :
    machine.step (config (some .rejectResult) state [] [] [] []) =
      some (config none initial [0] [] [] []) := by check_step

def rejected_query_run (query : List Alphabet) (state : Control) :
    EvalsToInTime machine.step (config (some .rejectQuery) state [] query [] [])
      (some (config (some .rejectTemporary) (none, state.2) [] [] [] [])) (query.length + 1) := by
  induction query generalizing state with
  | nil => exact SymbolMapMachine.oneStep (reject_query_nil state)
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (reject_query_cons state head tail)
      have rest := ih (some head, state.2)
      simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

def rejected_run (query : List Alphabet) (state : Control) :
    EvalsToInTime machine.step (config (some .rejectInput) state [] query [] [])
      (some (config none initial [0] [] [] [])) (query.length + 4) := by
  have first := SymbolMapMachine.oneStep (reject_input_nil state query)
  have body := rejected_query_run query (none, state.2)
  have middle := SymbolMapMachine.oneStep (reject_temporary_nil (none, state.2))
  have last := SymbolMapMachine.oneStep (reject_result_nil (none, state.2))
  have run := EvalsToInTime.trans _ 1 (query.length + 1) _ _ _ first body
  have joined := EvalsToInTime.trans _ ((query.length + 1) + 1) 1 _ _ _ run middle
  convert EvalsToInTime.trans _ (1 + ((query.length + 1) + 1)) 1 _ _ _ joined last using 1; omega

theorem start_missing (state : Control) (query : List Alphabet) :
    machine.step (config (some .startRow) state [4] query [] []) =
      some (config (some .rejectInput) (some 4, none, true) [] query [] []) := by check_step

/-- The search cost charges every scanned row and the restored binary key.
Successful lookup also drains the unread table before returning its result. -/
def searchBudget (query : List Bool) (rows : List (List Bool × List Bool)) : Nat :=
  (rows.length + 1) * (2 * query.length + 5) + 2 * (table rows).length + query.length + 6

def search_run (rows : List (List Bool × List Bool)) (query : List Bool) (state : Control) :
    EvalsToInTime machine.step (config (some .startRow) state (table rows) (field query) [] [])
      (some (config none initial (output (lookup query rows)) [] [] [])) (searchBudget query rows) := by
  induction rows generalizing state with
  | nil =>
      have first := SymbolMapMachine.oneStep (start_missing state (field query))
      have rest := rejected_run (field query) (some 4, none, true)
      have run := EvalsToInTime.trans _ 1 ((field query).length + 4) _ _ _ first rest
      have same : EvalsToInTime machine.step (config (some .startRow) state (table []) (field query) [] [])
          (some (config none initial (output (lookup query [])) [] [] [])) (query.length + 5) := by
        convert run using 1
        all_goals simp [table, lookup, output, field]
      exact BinaryReferenceMachine.within same (by simp [searchBudget, table]; omega)
  | cons row rest ih =>
      rcases row with ⟨key, value⟩
      have first := SymbolMapMachine.oneStep (start_row state (field key ++ 2 :: field value ++ 2 :: table rest) (field query))
      have compared := compare_key_run key query [] (field value ++ 2 :: table rest) (some 3, none, true)
      have compareJoined := EvalsToInTime.trans _ 1 (key.length + 2 * query.length + 0 + 3) _ _ _ first (by simpa [List.append_assoc] using compared)
      by_cases matched : query = key
      · have values := value_run value (table rest) (field query) [] none none true
        have accepted := accepted_run (table rest) (field query) (field value).reverse (some 2, none, true)
        have branch := EvalsToInTime.trans _ (value.length + 1)
          ((table rest).length + (field query).length + (field value).reverse.length + 3) _ _ _ values (by simpa using accepted)
        have joined := EvalsToInTime.trans _
          ((key.length + 2 * query.length + 0 + 3) + 1)
          (((table rest).length + (field query).length + (field value).reverse.length + 3) + (value.length + 1))
          _ _ _ compareJoined (by simpa [matched] using branch)
        have simplified : EvalsToInTime machine.step
            (config (some .startRow) state (table ((key, value) :: rest)) (field query) [] [])
            (some (config none initial (output (lookup query ((key, value) :: rest))) [] [] []))
            (key.length + 2 * query.length + 4 + value.length + 1 +
              ((table rest).length + query.length + value.length + 3)) := by
          convert joined using 1
          all_goals simp [table, lookup, matched, output, field, List.append_assoc]
          all_goals omega
        apply BinaryReferenceMachine.within simplified
        simp only [searchBudget, List.length_cons, table, List.length_append, field, List.length_map, Nat.add_mul, Nat.one_mul]
        omega
      · have values := value_run value (table rest) (field query) [] none none false
        have remaining := ih (some 2, none, false)
        have branch := EvalsToInTime.trans _ (value.length + 1) (searchBudget query rest) _ _ _ values (by simpa using remaining)
        have joined := EvalsToInTime.trans _
          ((key.length + 2 * query.length + 0 + 3) + 1)
          ((searchBudget query rest) + (value.length + 1)) _ _ _ compareJoined (by simpa [matched] using branch)
        have simplified : EvalsToInTime machine.step
            (config (some .startRow) state (table ((key, value) :: rest)) (field query) [] [])
            (some (config none initial (output (lookup query ((key, value) :: rest))) [] [] []))
            (key.length + 2 * query.length + 4 + value.length + 1 + searchBudget query rest) := by
          convert joined using 1
          all_goals simp [table, lookup, matched, field, List.append_assoc]
          all_goals omega
        apply BinaryReferenceMachine.within simplified
        simp only [searchBudget, List.length_cons, table, List.length_append, field, List.length_map, Nat.add_mul, Nat.one_mul]
        omega


def scan_run (key : List Bool) (input query temporary result : List Alphabet) (state : Control) :
    EvalsToInTime machine.step
      (config (some .scanQuery) state (field key ++ 2 :: input) query temporary result)
      (some (config (some .restoreQuery) (some 2, state.2) input query
        ((field key).reverse ++ temporary) result)) (key.length + 1) := by
  induction key generalizing state temporary with
  | nil => simpa [field] using SymbolMapMachine.oneStep (scan_end state input query temporary result)
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (scan_bit state head (field tail ++ 2 :: input) query temporary result)
      have rest := ih (bit head :: temporary) (some (bit head), state.2)
      simpa [field, List.reverse_cons, List.append_assoc] using
        EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

def restore_query_run (temporary query input result : List Alphabet) (state : Control) :
    EvalsToInTime machine.step
      (config (some .restoreQuery) state input query temporary result)
      (some (config (some .startRow) (none, state.2) input
        (temporary.reverse ++ query) [] result)) (temporary.length + 1) := by
  induction temporary generalizing query state with
  | nil => simpa using SymbolMapMachine.oneStep (restore_query_nil state input query result)
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (restore_query_cons state head input query tail result)
      have rest := ih (head :: query) (some head, state.2)
      simpa [List.reverse_cons, List.append_assoc] using
        EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

theorem init_eq (input : List Alphabet) :
    initList machine input = config (some .scanQuery) initial input [] [] [] := by
  simp only [initList, machine, config]
  congr 1
  funext stack
  cases stack
  · simp; rfl
  · simp
  · simp
  · simp

theorem halt_eq (result : List Alphabet) :
    haltList machine result = config none initial result [] [] [] := by
  simp only [haltList, machine, config]
  congr 1
  funext stack
  cases stack
  · simp; rfl
  · simp
  · simp
  · simp

/-- Complete execution of ordered binary-reference lookup. Both success and
refusal clear every internal stack and retain the actual submitted bit cost. -/
def outputs (query : List Bool) (rows : List (List Bool × List Bool)) :
    TM2OutputsInTime machine (packet query rows) (some (output (lookup query rows)))
      (2 * query.length + 2 + searchBudget query rows) := by
  have scanned := scan_run query (table rows) [] [] [] initial
  simp only [List.append_nil] at scanned
  have restored := restore_query_run (field query).reverse [] (table rows) [] (some 2, initial.2)
  simp only [List.reverse_reverse, List.append_nil] at restored
  have searched := search_run rows query initial
  have first := EvalsToInTime.trans _ (query.length + 1)
    ((field query).reverse.length + 1) _ _ _ scanned restored
  have joined := EvalsToInTime.trans _
    (((field query).reverse.length + 1) + (query.length + 1))
    (searchBudget query rows) _ _ _ first searched
  change EvalsToInTime _ (initList machine (packet query rows))
    (some (haltList machine (output (lookup query rows)))) _
  rw [init_eq, halt_eq]
  simpa [packet, field, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, two_mul] using joined

theorem rows_length_le_table_length (rows : List (List Bool × List Bool)) :
    rows.length ≤ (table rows).length := by
  induction rows with
  | nil => simp [table]
  | cons row rest ih =>
      rcases row with ⟨key, value⟩
      simp only [table, List.length_cons, List.length_append, field, List.length_map]
      omega

theorem packet_length (query : List Bool) (rows : List (List Bool × List Bool)) :
    (packet query rows).length = query.length + (table rows).length + 1 := by
  simp [packet, field]; omega

theorem outputs_bound (query : List Bool) (rows : List (List Bool × List Bool)) :
    2 * query.length + 2 + searchBudget query rows ≤
      4 * (packet query rows).length ^ 2 + 20 * (packet query rows).length + 20 := by
  have rowBound := rows_length_le_table_length rows
  have queryBound : query.length ≤ (packet query rows).length := by rw [packet_length]; omega
  have countBound : rows.length + 1 ≤ (packet query rows).length := by rw [packet_length]; omega
  have multiplied := Nat.mul_le_mul countBound (show 2 * query.length + 5 ≤ 2 * (packet query rows).length + 5 by omega)
  rw [packet_length] at multiplied queryBound countBound ⊢
  simp only [searchBudget]
  nlinarith


/-- Lookup cannot manufacture a longer value than the submitted table stores.
This bounds the actual intermediate output used by machine composition. -/
theorem output_lookup_length_le_table (query : List Bool) (rows : List (List Bool × List Bool)) :
    (output (lookup query rows)).length ≤ (table rows).length := by
  induction rows with
  | nil => simp [lookup, output, table]
  | cons row rest ih =>
      rcases row with ⟨key, value⟩
      by_cases matched : query = key
      · simp [lookup, matched, output, table, field]; omega
      · simp only [lookup, if_neg matched, table, List.length_cons, List.length_append, field, List.length_map]
        omega

theorem output_length_le_packet (query : List Bool) (rows : List (List Bool × List Bool)) :
    (output (lookup query rows)).length ≤ (packet query rows).length := by
  have bound := output_lookup_length_le_table query rows
  rw [packet_length]
  omega

set_option backward.isDefEq.respectTransparency false in
/-- Polynomial execution of the actual finite machine on every encoded query,
including absent references and ordered tables containing duplicate keys. -/
noncomputable def computable : TM2ComputableInPolyTime
    (fun input : List Bool × List (List Bool × List Bool) => packet input.1 input.2)
    output (fun input : List Bool × List (List Bool × List Bool) => lookup input.1 input.2) where
  tm := machine
  inputAlphabet := Equiv.refl Alphabet
  outputAlphabet := Equiv.refl Alphabet
  time := C 4 * X ^ 2 + C 20 * X + C 20
  outputsFun input := by
    change TM2OutputsInTime machine ((packet input.1 input.2).map id)
      (some ((output (lookup input.1 input.2)).map id)) _
    simp only [List.map_id_fun]
    apply BinaryReferenceMachine.within (outputs input.1 input.2)
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X] using outputs_bound input.1 input.2


/-- Binary address fields are exactly the original certificate codec's
terminated natural fields, without a fixed machine-word range. -/
def naturalKey (value : Nat) : List Bool := (Nat.digits 2 value).map (fun digit => decide (digit ≠ 0))

theorem field_naturalKey (value : Nat) :
    field (naturalKey value) ++ [2] = Mettapedia.OSLF.Binding.WireCodec.Binary.natural value := by
  simp only [field, naturalKey, Mettapedia.OSLF.Binding.WireCodec.Binary.natural, List.map_map]
  congr 1
  apply List.map_congr_left
  intro digit _
  by_cases zero : digit = 0 <;> simp [bit, zero]

theorem naturalKey_injective : Function.Injective naturalKey := by
  intro first second same
  have inputSame := congrArg (fun key => field key ++ [2]) same
  rw [field_naturalKey, field_naturalKey] at inputSame
  have parsed := congrArg Mettapedia.OSLF.Binding.WireCodec.Binary.readNatural inputSame
  have firstRead := Mettapedia.OSLF.Binding.WireCodec.Binary.readNatural_natural first []
  have secondRead := Mettapedia.OSLF.Binding.WireCodec.Binary.readNatural_natural second []
  simp only [List.append_nil] at firstRead secondRead
  rw [firstRead, secondRead] at parsed
  exact congrArg Prod.fst (Option.some.inj parsed)

/-- Cache addresses and arithmetic use the same canonical original binary
digits. Their two Boolean projections agree on every actual base-two digit. -/
theorem naturalKey_eq_naturalBits (value : Nat) :
    naturalKey value = Mettapedia.Computability.BinaryStackArithmetic.naturalBits value := by
  unfold naturalKey Mettapedia.Computability.BinaryStackArithmetic.naturalBits
  apply List.map_congr_left
  intro digit member
  have bound := Nat.digits_lt_base (by decide : 1 < 2) member
  have alternatives : digit = 0 ∨ digit = 1 := by omega
  rcases alternatives with rfl | rfl <;> rfl

/-- A chronological address increment is executed on its bit field; its
numeric value is never expanded into that many machine transitions. -/
def nextKeyOutputs (value : Nat) :
    TM2OutputsInTime Mettapedia.Computability.BinaryStackArithmetic.machine
      (naturalKey value) (some (naturalKey (value + 1)))
      (2 * (naturalKey value).length + 3) := by
  simpa only [naturalKey_eq_naturalBits] using
    Mettapedia.Computability.BinaryStackArithmetic.naturalOutputs value

/-- Reference bounds compare complete original binary keys. False is
distinct from malformed framing, which has its own refusal output. -/
def compareKeysOutputs (first second : Nat) :
    TM2OutputsInTime Mettapedia.Computability.BinaryWordComparison.machine
      (Mettapedia.Computability.BinaryWordComparison.packet (naturalKey first) (naturalKey second))
      (some [some (decide (first < second))])
      (3 * (Mettapedia.Computability.BinaryWordComparison.packet
        (naturalKey first) (naturalKey second)).length + 3) := by
  simpa only [naturalKey_eq_naturalBits,
    Mettapedia.Computability.BinaryWordComparison.less_naturalBits] using
    Mettapedia.Computability.BinaryWordComparison.outputs
      (Mettapedia.Computability.BinaryStackArithmetic.naturalBits first)
      (Mettapedia.Computability.BinaryStackArithmetic.naturalBits second)

/-- Physical block offsets add using the same key encoding and charge every
input bit, carry and canonical output bit. -/
def addKeysOutputs (first second : Nat) :
    TM2OutputsInTime Mettapedia.Computability.BinaryWordAddition.machine
      (Mettapedia.Computability.BinaryWordAddition.packet (naturalKey first) (naturalKey second))
      (some ((naturalKey (first + second)).map some))
      (5 * (Mettapedia.Computability.BinaryWordAddition.packet
        (naturalKey first) (naturalKey second)).length + 8) := by
  simpa only [naturalKey_eq_naturalBits, Mettapedia.Computability.BinaryWordAddition.encodedInput] using
    Mettapedia.Computability.BinaryWordAddition.naturalOutputs first second

def indexedFromWith {A : Type} (encode : A → List Bool) (offset : Nat) :
    List A → List (List Bool × List Bool)
  | [] => []
  | value :: rest => (naturalKey offset, encode value) :: indexedFromWith encode (offset + 1) rest

theorem lookup_indexedFromWith {A : Type} (encode : A → List Bool)
    (offset query : Nat) (values : List A) :
    lookup (naturalKey query) (indexedFromWith encode offset values) =
      if query < offset then none else values[query - offset]?.map encode := by
  induction values generalizing offset with
  | nil => simp [indexedFromWith, lookup]
  | cons first rest ih =>
      by_cases same : query = offset
      · subst query
        simp [indexedFromWith, lookup]
      · have different : naturalKey query ≠ naturalKey offset := fun equal => same (naturalKey_injective equal)
        simp only [indexedFromWith, lookup, if_neg different, ih]
        by_cases before : query < offset
        · have beforeNext : query < offset + 1 := by omega
          simp [before, beforeNext]
        · have after : offset < query := by omega
          have afterNext : ¬ query < offset + 1 := by omega
          have subtraction : query - offset = query - (offset + 1) + 1 := by omega
          simp [before, afterNext, subtraction]

theorem indexedFromWith_append {A : Type} (encode : A → List Bool) (offset : Nat)
    (values : List A) (value : A) :
    indexedFromWith encode offset (values ++ [value]) =
      indexedFromWith encode offset values ++ [(naturalKey (offset + values.length), encode value)] := by
  induction values generalizing offset with
  | nil => simp [indexedFromWith]
  | cons first rest ih =>
      simp [indexedFromWith, ih, Nat.add_left_comm, Nat.add_comm]

def indexedFrom (offset : Nat) : List Nat → List (List Bool × List Bool) :=
  indexedFromWith naturalKey offset

def indexed (roots : Array Nat) : List (List Bool × List Bool) := indexedFrom 0 roots.toList

theorem lookup_indexedFrom (offset query : Nat) (roots : List Nat) :
    lookup (naturalKey query) (indexedFrom offset roots) =
      if query < offset then none else roots[query - offset]?.map naturalKey := by
  exact lookup_indexedFromWith naturalKey offset query roots

/-- The executed table lookup is precisely an original source-root cache
lookup, retaining physical addresses and refusing indices beyond that cache. -/
theorem lookup_indexed (roots : Array Nat) (query : Nat) :
    lookup (naturalKey query) (indexed roots) = roots[query]?.map naturalKey := by
  simpa [indexed] using lookup_indexedFrom 0 query roots.toList

/-- Ordered parent lookup retains repeated references through the original
shared-graph lookup operation. This projection adds no graph authority. -/
def resolveParents (rows : List (List Bool × List Bool)) : List Nat → Option (List (List Bool))
  | [] => some []
  | index :: rest => do
      let physical ← lookup (naturalKey index) rows
      let following ← resolveParents rows rest
      pure (physical :: following)

theorem resolveParents_indexed (roots : Array Nat) (indices : List Nat) :
    resolveParents (indexed roots) indices =
      (Mettapedia.Logic.DerivationGraph.lookupPremises roots indices).map (List.map naturalKey) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      simp only [resolveParents, lookup_indexed, Mettapedia.Logic.DerivationGraph.lookupPremises]
      cases first : roots[index]? <;>
        cases later : Mettapedia.Logic.DerivationGraph.lookupPremises roots rest <;>
        simp [ih, later]


def referencePacket (roots : Array Nat) (query : Nat) : List Alphabet :=
  packet (naturalKey query) (indexed roots)

def physicalOutput (value : Option Nat) : List Alphabet := output (value.map naturalKey)

/-- The concrete machine realizes lookup of an already authored physical root.
The bound includes the complete binary key and root-table payload. -/
def referenceOutputs (roots : Array Nat) (query : Nat) :
    TM2OutputsInTime machine (referencePacket roots query) (some (physicalOutput roots[query]?))
      (4 * (referencePacket roots query).length ^ 2 + 20 * (referencePacket roots query).length + 20) := by
  have run := BinaryReferenceMachine.within (outputs (naturalKey query) (indexed roots))
    (outputs_bound (naturalKey query) (indexed roots))
  simpa only [TM2OutputsInTime, referencePacket, lookup_indexed, physicalOutput] using run

/-- Future references are refused by executed table search, rather than by
iterating up to the submitted numeric value. -/
def futureReferenceOutputs (roots : Array Nat) (query : Nat) (outside : roots.size ≤ query) :
    TM2OutputsInTime machine (referencePacket roots query) (some ([0] : List Alphabet))
      (4 * (referencePacket roots query).length ^ 2 + 20 * (referencePacket roots query).length + 20) := by
  simpa [physicalOutput, Array.getElem?_eq_none outside, output] using referenceOutputs roots query


namespace Controls

theorem shared_occurrences :
    resolveParents (indexed #[7, 13, 7]) [2, 0, 2] =
      some [naturalKey 7, naturalKey 7, naturalKey 7] := by decide

theorem future_refused : lookup (naturalKey 3) (indexed #[7, 13, 7]) = none := by decide

theorem first_duplicate_key : lookup [true] [([true], [false]), ([true], [true])] = some [false] := by decide

theorem different_binary_length : lookup [true, false, false] [([true], [false])] = none := by decide

end Controls

namespace TableAppend

open Mettapedia.Computability
open WordTemplateMachine

attribute [local implicit_reducible] Indexed.machine Indexed.Alphabet

/-- The unique final table marker is omitted while preparing the append.
Keys and values contain only the original binary symbols. -/
def body : List (List Bool × List Bool) → List Alphabet
  | [] => []
  | (key, value) :: rest => 3 :: field key ++ 2 :: field value ++ 2 :: body rest

theorem table_body (rows : List (List Bool × List Bool)) : table rows = body rows ++ [4] := by
  induction rows with
  | nil => rfl
  | cons row rest ih => cases row; simp only [table, body, ih, List.cons_append, List.append_assoc]

theorem body_append (first second : List (List Bool × List Bool)) :
    body (first ++ second) = body first ++ body second := by
  induction first with
  | nil => rfl
  | cons row rest ih => cases row; simp only [List.cons_append, body, ih, List.append_assoc]

def images (symbol : Option Alphabet) : List (Option Alphabet) :=
  if symbol = some 4 then [] else [symbol]

theorem flatMap_images (word : List (Option Alphabet)) :
    word.flatMap images = word.filter (fun symbol => symbol != some 4) := by
  induction word with
  | nil => rfl
  | cons symbol rest ih => by_cases terminal : symbol = some 4 <;>
      simp [images, terminal, ih]

theorem field_filter (bits : List Bool) :
    (field bits).filter (fun symbol => symbol != 4) = field bits := by
  induction bits with
  | nil => rfl
  | cons first rest ih =>
      change (bit first :: field rest).filter _ = bit first :: field rest
      have retained : (bit first != (4 : Alphabet)) = true := by cases first <;> decide
      simp only [List.filter_cons, retained, ih]
      rfl

theorem table_filter (rows : List (List Bool × List Bool)) :
    (table rows).filter (fun symbol => symbol != 4) = body rows := by
  induction rows with
  | nil => decide
  | cons row rest ih => cases row; simp [table, body, List.filter_append, field_filter, ih]

def fields (rows : List (List Bool × List Bool)) (key value : List Bool) : Fin 3 → List Alphabet :=
  ![table rows, field key, field value]

def normalizedFields (rows : List (List Bool × List Bool)) (key value : List Bool) : Fin 3 → List Alphabet :=
  ![body rows, field key, field value]

def packet (rows : List (List Bool × List Bool)) (key value : List Bool) : List (Option Alphabet) :=
  Indexed.argumentWire (fields rows key value)

def template : Indexed.Template Alphabet 3 :=
  [.inr 0, .inl 3, .inr 1, .inl 2, .inr 2, .inl 2, .inl 4]

theorem filtered_word (word : List Alphabet) :
    (word.map some).flatMap images =
      (word.filter (fun symbol => symbol != 4)).map some := by
  induction word with
  | nil => rfl
  | cons symbol rest ih => by_cases terminal : symbol = 4 <;> simp [images, terminal, ih]

theorem filtered_fields (rows : List (List Bool × List Bool)) (key value : List Bool) :
    (packet rows key value).flatMap images =
      Indexed.argumentWire (normalizedFields rows key value) := by
  simp only [packet, Indexed.argumentWire, Indexed.frame, List.finRange_succ, List.finRange_zero,
    List.map_nil, List.map_cons, List.flatMap_cons, List.flatMap_nil,
    List.flatMap_append, fields, normalizedFields, Matrix.cons_val_zero,
    Matrix.cons_val_succ, filtered_word, table_filter, field_filter]
  simp [images]

theorem assembled (rows : List (List Bool × List Bool)) (key value : List Bool) :
    Indexed.instantiate template (normalizedFields rows key value) = table (rows ++ [(key, value)]) := by
  simp [Indexed.instantiate, template, normalizedFields, table_body, body_append, body,
    List.append_assoc]

def normalized (word : List (Option Alphabet)) : List (Option Alphabet) := word.flatMap images

def appendWord (word : List (Option Alphabet)) : List Alphabet :=
  Indexed.instantiateWire template (normalized word)

theorem appendWord_packet (rows : List (List Bool × List Bool)) (key value : List Bool) :
    appendWord (packet rows key value) = table (rows ++ [(key, value)]) := by
  rw [appendWord, normalized, filtered_fields, Indexed.instantiateWire_argumentWire, assembled]

theorem normalized_length (word : List (Option Alphabet)) :
    (normalized word).length ≤ word.length := by
  rw [normalized, flatMap_images]
  exact List.length_filter_le _ _

attribute [local implicit_reducible] WordHomomorphismMachine.machine

local instance : Fintype ((WordHomomorphismMachine.machine images).Γ
    (WordHomomorphismMachine.machine images).k₁) := by
  change Fintype (Option Alphabet)
  infer_instance
local instance : Inhabited ((WordHomomorphismMachine.machine images).Γ
    (WordHomomorphismMachine.machine images).k₁) := by
  change Inhabited (Option Alphabet)
  infer_instance

/-- The append program is the same concrete two-stage stack composition used
by the realization; its intermediate table body remains physical input. -/
@[implicit_reducible] def machine : FinTM2 := StackMachineComposition.machine
  (WordHomomorphismMachine.machine images) (Indexed.machine template)
  (Equiv.refl (Option Alphabet))

/-- Concrete transition instructions for the same append machine. -/
def program : machine.Λ → machine.Stmt :=
  StackMachineComposition.Programs.body WordHomomorphismMachine.Stack.result
    Indexed.Stack.input (Indexed.Phase.emit 0) (none : Option Alphabet) id
    (WordHomomorphismMachine.program images) (Indexed.program template)

theorem program_eq : program = machine.m :=
  StackMachineComposition.body_eq (WordHomomorphismMachine.machine images)
    (Indexed.machine template) (Equiv.refl (Option Alphabet))

/-- This clock charges removal of the table terminator, both word transfers,
the complete copied table, new binary fields, and final output reversal. -/
def outputs (word : List (Option Alphabet)) :
    TM2OutputsInTime machine word (some (appendWord word)) (38 * word.length + 36) := by
  have earlier := WordHomomorphismMachine.outputs images word
  have later := Indexed.outputsWire template (normalized word)
  have copied : (normalized word).map (Equiv.refl (Option Alphabet)) = normalized word :=
    List.map_id _
  have laterMapped : TM2OutputsInTime (Indexed.machine template)
      ((normalized word).map (Equiv.refl (Option Alphabet)))
      (some (appendWord word)) (4 * (template.length + 1) * ((normalized word).length + 1)) := by
    rw [copied]
    exact later
  have joined := StackMachineComposition.outputs
    (WordHomomorphismMachine.machine images) (Indexed.machine template)
    (Equiv.refl (Option Alphabet)) word (normalized word) (appendWord word)
    (2 * word.length + 2 * (normalized word).length + 2)
    (4 * (template.length + 1) * ((normalized word).length + 1)) earlier laterMapped
  refine ⟨joined.toEvalsTo, joined.steps_le_m.trans ?_⟩
  have bound := normalized_length word
  simp only [template, List.length_cons, List.length_nil] at *
  omega

noncomputable def templateRealization :
    TM2ComputableInPolyTime id id (Indexed.instantiateWire template) where
  tm := Indexed.machine template
  inputAlphabet := Equiv.refl (Option Alphabet)
  outputAlphabet := Equiv.refl Alphabet
  time := C (4 * (template.length + 1)) * (X + C 1)
  outputsFun word := by
    change TM2OutputsInTime (Indexed.machine template) (word.map id)
      (some ((Indexed.instantiateWire template word).map id)) _
    simp only [List.map_id_fun]
    simpa only [id, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_X] using Indexed.outputsWire template word

/-- Table append is executed by the original homomorphism and copier machines.
The original table is traversed and copied; no cache is kept in finite control. -/
noncomputable def realization : TM2ComputableInPolyTime id id appendWord :=
  ProofSystems.ExecutedComposition.realization (WordHomomorphismMachine.realization images)
    templateRealization X (by intro input; simpa only [id, Polynomial.eval_X] using normalized_length input)

theorem indexedFrom_append (offset : Nat) (roots : List Nat) (physical : Nat) :
    indexedFrom offset (roots ++ [physical]) =
      indexedFrom offset roots ++ [(naturalKey (offset + roots.length), naturalKey physical)] := by
  exact indexedFromWith_append naturalKey offset roots physical

theorem indexed_push (roots : Array Nat) (physical : Nat) :
    indexed (roots.push physical) = indexed roots ++ [(naturalKey roots.size, naturalKey physical)] := by
  simpa [indexed] using indexedFrom_append 0 roots.toList physical

theorem appendWord_indexed (roots : Array Nat) (physical : Nat) :
    appendWord (packet (indexed roots) (naturalKey roots.size) (naturalKey physical)) =
      table (indexed (roots.push physical)) := by
  rw [appendWord_packet, indexed_push]

/-- The source index equals the current chronological cache size. Appending
one root retains exactly the original `Array.push` lookup semantics. -/
def indexedOutputs (roots : Array Nat) (physical : Nat) :
    TM2OutputsInTime machine
      (packet (indexed roots) (naturalKey roots.size) (naturalKey physical))
      (some (table (indexed (roots.push physical))))
      (38 * (packet (indexed roots) (naturalKey roots.size) (naturalKey physical)).length + 36) := by
  rw [← appendWord_indexed]
  exact outputs _

end TableAppend

namespace PhysicalSize

open Mettapedia.Computability


theorem naturalKey_length (value : Nat) : (naturalKey value).length ≤ value := by
  simpa only [naturalKey, List.length_map] using
    (Nat.digits_length_le_iff (by decide) value).mpr Nat.lt_two_pow_self

theorem table_cons_length (key value : List Bool) (rows : List (List Bool × List Bool)) :
    (table ((key, value) :: rows)).length = key.length + value.length + (table rows).length + 3 := by
  simp only [table, field, List.length_cons, List.length_append, List.length_map]
  omega

/-- The cache size includes every complete chronological key and physical
root. The bound does not erase repeated roots or any stored table row. -/
theorem indexedFrom_table_length (offset : Nat) (roots : List Nat) (physicalBound : Nat)
    (bounded : ∀ physical ∈ roots, physical ≤ physicalBound) :
    (table (indexedFrom offset roots)).length ≤
      roots.length * (offset + roots.length + physicalBound + 3) + 1 := by
  induction roots generalizing offset with
  | nil => simp [indexedFrom, indexedFromWith, table]
  | cons physical rest ih =>
      have first := bounded physical (by simp)
      have tail : ∀ value ∈ rest, value ≤ physicalBound := by
        intro value member
        exact bounded value (by simp [member])
      have following := ih (offset + 1) tail
      simp only [indexedFrom] at following
      have keySize := naturalKey_length offset
      have valueSize := (naturalKey_length physical).trans first
      simp only [indexedFrom, indexedFromWith, table_cons_length, List.length_cons]
      nlinarith

theorem indexed_table_length (roots : Array Nat) (physicalBound : Nat)
    (bounded : ∀ physical ∈ roots.toList, physical ≤ physicalBound) :
    (table (indexed roots)).length ≤
      roots.size * (roots.size + physicalBound + 3) + 1 := by
  simpa only [indexed, Array.length_toList, Nat.zero_add] using
    indexedFrom_table_length 0 roots.toList physicalBound bounded

/-- A submitted future index remains charged by its physical binary length,
rather than by its numeric magnitude. -/
theorem referencePacket_length (roots : Array Nat) (query physicalBound : Nat)
    (bounded : ∀ physical ∈ roots.toList, physical ≤ physicalBound) :
    (referencePacket roots query).length ≤
      (naturalKey query).length + roots.size * (roots.size + physicalBound + 3) + 2 := by
  have stored := indexed_table_length roots physicalBound bounded
  simp only [referencePacket, packet, field, List.length_append, List.length_map, List.length_cons]
  omega

/-- The existing resolver is executed with the entire physically stored
cache; this coarser clock follows its actual transition theorem. -/
def referenceOutputs (roots : Array Nat) (query physicalBound : Nat)
    (bounded : ∀ physical ∈ roots.toList, physical ≤ physicalBound) :
    let payload := (naturalKey query).length + roots.size * (roots.size + physicalBound + 3) + 2
    TM2OutputsInTime machine (referencePacket roots query) (some (physicalOutput roots[query]?))
      (4 * payload ^ 2 + 20 * payload + 20) := by
  dsimp only
  have executed := SharedReferenceExecution.referenceOutputs roots query
  have size := referencePacket_length roots query physicalBound bounded
  refine ⟨executed.toEvalsTo, executed.steps_le_m.trans ?_⟩
  nlinarith [Nat.mul_self_le_mul_self size]

theorem appendPacket_length (roots : Array Nat) (physical physicalBound : Nat)
    (bounded : ∀ value ∈ roots.toList, value ≤ physicalBound)
    (newBound : physical ≤ physicalBound) :
    (TableAppend.packet (indexed roots) (naturalKey roots.size) (naturalKey physical)).length ≤
      roots.size * (roots.size + physicalBound + 3) + roots.size + physicalBound + 4 := by
  have stored := indexed_table_length roots physicalBound bounded
  have keySize := naturalKey_length roots.size
  have valueSize := (naturalKey_length physical).trans newBound
  simp only [TableAppend.packet, WordTemplateMachine.Indexed.argumentWire,
    WordTemplateMachine.Indexed.frame, TableAppend.fields, List.finRange_succ,
    List.finRange_zero, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    Matrix.cons_val_zero, Matrix.cons_val_succ, List.length_append, List.length_map,
    List.length_cons, List.length_nil, field]
  omega

/-- Appending a chronological root scans and copies the actual old cache.
The supplied physical bound affects only the proven clock estimate. -/
def appendOutputs (roots : Array Nat) (physical physicalBound : Nat)
    (bounded : ∀ value ∈ roots.toList, value ≤ physicalBound)
    (newBound : physical ≤ physicalBound) :
    let payload := roots.size * (roots.size + physicalBound + 3) + roots.size + physicalBound + 4
    TM2OutputsInTime TableAppend.machine
      (TableAppend.packet (indexed roots) (naturalKey roots.size) (naturalKey physical))
      (some (table (indexed (roots.push physical)))) (38 * payload + 36) := by
  dsimp only
  have executed := TableAppend.indexedOutputs roots physical
  have size := appendPacket_length roots physical physicalBound bounded newBound
  refine ⟨executed.toEvalsTo, executed.steps_le_m.trans ?_⟩
  omega

end PhysicalSize

namespace EncodedTable
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary

/-- Complete original codec values are stored losslessly in the existing binary resolver. -/
def value {A : Type} (codec : Codec A) (source : A) : List Bool :=
  Triples.encode (encodeWith codec source)

def rows {A : Type} (codec : Codec A) (values : Array A) : List (List Bool × List Bool) :=
  indexedFromWith (value codec) 0 values.toList

def queryPacket {A : Type} (codec : Codec A) (values : Array A) (query : Nat) : List Alphabet :=
  packet (naturalKey query) (rows codec values)

theorem lookup_rows {A : Type} (codec : Codec A) (values : Array A) (query : Nat) :
    lookup (naturalKey query) (rows codec values) = values[query]?.map (value codec) := by
  simpa [rows] using lookup_indexedFromWith (value codec) 0 query values.toList

theorem value_injective {A : Type} (codec : Codec A) : Function.Injective (value codec) :=
  Triples.original_injective codec

/-- The existing finite resolver returns precisely the original chronological array lookup. -/
def referenceOutputs {A : Type} (codec : Codec A) (values : Array A) (query : Nat) :
    TM2OutputsInTime machine (queryPacket codec values query)
      (some (output (values[query]?.map (value codec))))
      (4 * (queryPacket codec values query).length ^ 2 +
        20 * (queryPacket codec values query).length + 20) := by
  have executed := BinaryReferenceMachine.within (outputs (naturalKey query) (rows codec values))
    (outputs_bound (naturalKey query) (rows codec values))
  simpa only [TM2OutputsInTime, queryPacket, lookup_rows] using executed

def futureOutputs {A : Type} (codec : Codec A) (values : Array A) (query : Nat)
    (outside : values.size ≤ query) :
    TM2OutputsInTime machine (queryPacket codec values query) (some ([0] : List Alphabet))
      (4 * (queryPacket codec values query).length ^ 2 +
        20 * (queryPacket codec values query).length + 20) := by
  simpa [Array.getElem?_eq_none outside, output] using referenceOutputs codec values query

theorem rows_push {A : Type} (codec : Codec A) (values : Array A) (next : A) :
    rows codec (values.push next) = rows codec values ++ [(naturalKey values.size, value codec next)] := by
  simpa [rows] using indexedFromWith_append (value codec) 0 values.toList next

/-- Appending copies the full original values and retains physical chronological order. -/
def appendOutputs {A : Type} (codec : Codec A) (values : Array A) (next : A) :
    TM2OutputsInTime TableAppend.machine
      (TableAppend.packet (rows codec values) (naturalKey values.size) (value codec next))
      (some (table (rows codec (values.push next))))
      (38 * (TableAppend.packet (rows codec values) (naturalKey values.size) (value codec next)).length + 36) := by
  rw [rows_push, ← TableAppend.appendWord_packet]
  exact TableAppend.outputs _

theorem encoded_length {A : Type} (codec : Codec A) (source : A) :
    (value codec source).length = 3 * (encodeWith codec source).length := Triples.encode_length _

theorem table_length_bound {A : Type} (encode : A → List Bool) (offset : Nat) (values : List A) :
    (table (indexedFromWith encode offset values)).length ≤
      (values.map fun value => (encode value).length).sum +
        values.length * (offset + values.length + 3) + 1 := by
  induction values generalizing offset with
  | nil => simp [indexedFromWith, table]
  | cons first rest ih =>
      have following := ih (offset + 1)
      have keySize := PhysicalSize.naturalKey_length offset
      simp only [indexedFromWith, PhysicalSize.table_cons_length, List.length_cons,
        List.map_cons, List.sum_cons]
      nlinarith

attribute [local implicit_reducible] machine Triples.Recovery.machine
local instance : Fintype (machine.Γ machine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (machine.Γ machine.k₁) := inferInstanceAs (Inhabited Alphabet)

/-- Recovery exposes the original codec word, with a consumed lookup status.
The bits retained in cache rows never become a free decoded input. -/
def decodedOutput {A : Type} (codec : Codec A) (value : Option A) : List Alphabet :=
  Triples.Recovery.decodedResponse (value.map (encodeWith codec))

/-- A successful recovered word identifies the original stored value. -/
theorem decodedOutput_some_iff {A : Type} (codec : Codec A) (selected : Option A) (expected : A) :
    decodedOutput codec selected = 1 :: encodeWith codec expected ↔ selected = some expected := by
  cases selected with
  | none => simp [decodedOutput, Triples.Recovery.decodedResponse]
  | some selected =>
      simp only [decodedOutput, Option.map_some, Triples.Recovery.decodedResponse,
        Triples.Recovery.result, List.cons.injEq, true_and, Option.some.injEq]
      exact (encodeWith_injective codec).eq_iff

@[reducible, macro_inline] def decodedMachine : FinTM2 :=
  Mettapedia.Computability.StackMachineComposition.machine machine
    Triples.Recovery.machine (Equiv.refl Alphabet)

def decodedProgram : decodedMachine.Λ → decodedMachine.Stmt :=
  Mettapedia.Computability.StackMachineComposition.Programs.body
    (FirstAlphabet := machine.Γ) (SecondAlphabet := Triples.Recovery.machine.Γ)
    machine.k₁ Triples.Recovery.machine.k₀ Triples.Recovery.machine.main default
    (Equiv.refl Alphabet) machine.m Triples.Recovery.machine.m

theorem decodedProgram_eq : decodedProgram = decodedMachine.m :=
  Mettapedia.Computability.StackMachineComposition.body_eq machine Triples.Recovery.machine
    (Equiv.refl Alphabet)

private theorem encodedResponse_eq {A : Type} (codec : Codec A) (selected : Option A) :
    output (selected.map (value codec)) =
      Triples.Recovery.response (selected.map (encodeWith codec)) := by
  cases selected with
  | none => rfl
  | some selected =>
      simp only [Option.map_some,output,value,Triples.Recovery.response,Triples.Recovery.packet,
        Triples.Recovery.bits,field]
      rfl

private theorem lookup_value_length {query found : List Bool}
    {rows : List (List Bool × List Bool)} (stored : lookup query rows = some found) :
    found.length ≤ (table rows).length := by
  induction rows with
  | nil => simp [lookup] at stored
  | cons row rows ih =>
      rcases row with ⟨key,entry⟩
      by_cases same : query = key
      · have valueEq : entry = found := by simpa [lookup,same] using stored
        rw [← valueEq]
        have counted := PhysicalSize.table_cons_length key entry rows
        omega
      · have later : lookup query rows = some found := by simpa [lookup,same] using stored
        have bounded := ih later
        have counted := PhysicalSize.table_cons_length key entry rows
        omega

private theorem response_length {A : Type} (codec : Codec A) (values : Array A) (query : Nat) :
    (output (values[query]?.map (value codec))).length ≤ (queryPacket codec values query).length + 2 := by
  cases found : values[query]? with
  | none => simp [output]
  | some selected =>
      have stored : lookup (naturalKey query) (rows codec values) = some (value codec selected) := by
        simp only [lookup_rows,found,Option.map_some]
      have bounded := lookup_value_length stored
      have packet := packet_length (naturalKey query) (rows codec values)
      simp only [Option.map_some,output,field,List.length_cons,List.length_append,
        List.length_nil,List.length_map] at ⊢
      change (value codec selected).length + 1 + 1 ≤ _
      dsimp only [queryPacket]
      omega

private theorem recovered_length {A : Type} (codec : Codec A) (values : Array A) (query : Nat) :
    ((values[query]?.map (encodeWith codec)).getD []).length ≤
      (output (values[query]?.map (value codec))).length := by
  cases found : values[query]? with
  | none => simp
  | some selected =>
      simp only [Option.map_some,Option.getD_some,output,field,List.length_cons,List.length_append,
        List.length_nil,List.length_map]
      rw [encoded_length]
      omega

/-- Resolver, physical transfer and triple recovery execute as one machine.
Missing or future rows remain a refused response; successful rows contain the
complete original codec word. -/
def decodedReferenceOutputs {A : Type} (codec : Codec A) (values : Array A) (query : Nat) :
    TM2OutputsInTime decodedMachine (queryPacket codec values query)
      (some (decodedOutput codec values[query]?))
      (4 * (queryPacket codec values query).length ^ 2 +
        30 * (queryPacket codec values query).length + 50) := by
  have first := referenceOutputs codec values query
  have second := Triples.Recovery.responseOutputs (values[query]?.map (encodeWith codec))
  rw [← encodedResponse_eq codec values[query]?] at second
  have copied : (output (values[query]?.map (value codec))).map (Equiv.refl Alphabet) =
      output (values[query]?.map (value codec)) := by simp
  rw [← copied] at second
  have joined := Mettapedia.Computability.StackMachineComposition.outputs
    machine Triples.Recovery.machine (Equiv.refl Alphabet)
    (queryPacket codec values query) (output (values[query]?.map (value codec)))
    (decodedOutput codec values[query]?) _ _ first second
  have middle := response_length codec values query
  have recovered := recovered_length codec values query
  change EvalsToInTime _ _ _ _
  refine ⟨joined.toEvalsTo,joined.steps_le_m.trans ?_⟩
  omega

/-- Complete cache lookup has an attached quadratic physical-input clock. -/
noncomputable def decodedRealization {A : Type} (codec : Codec A) :
    TM2ComputableInPolyTime
      (fun input : Array A × Nat => queryPacket codec input.1 input.2)
      (decodedOutput codec) (fun input => input.1[input.2]?) where
  tm := decodedMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := C 4 * X ^ 2 + C 30 * X + C 50
  outputsFun input := by
    change TM2OutputsInTime decodedMachine ((queryPacket codec input.1 input.2).map id)
      (some ((decodedOutput codec input.1[input.2]?).map id))
      ((C 4 * X ^ 2 + C 30 * X + C 50).eval (queryPacket codec input.1 input.2).length)
    simp only [List.map_id_fun, eval_add,eval_mul,eval_pow,eval_X,eval_C]
    exact decodedReferenceOutputs codec input.1 input.2

end EncodedTable

namespace PhysicalAddress
set_option backward.isDefEq.respectTransparency false
open _root_.Computability Turing StateTransition Polynomial
open ProofSystems Mettapedia.Computability
open Mettapedia.OSLF.Binding.WireCodec

def numberEncoding (value : Nat) : List Alphabet := Binary.encodeWith Codec.nat value

theorem numberEncoding_eq (value : Nat) :
    numberEncoding value = 3 :: field (naturalKey value) ++ [2] := by
  simp only [numberEncoding, Binary.encodeWith, Codec.nat, Binary.encodeData,
    Binary.writeData, List.append_nil, List.cons_append]
  rw [field_naturalKey]

def inputImages (symbol : Alphabet) : List (Option Bool) :=
  match symbol.val with
  | 0 => [some false]
  | 1 => [some true]
  | 2 => [none]
  | _ => []

def inputBits (value : Nat) : List (Option Bool) :=
  (BinaryStackArithmetic.naturalBits value).map some ++ [none]

theorem inputImages_field (word : List Bool) :
    (field word).flatMap inputImages = word.map some := by
  induction word with
  | nil => rfl
  | cons head tail ih =>
      change inputImages (bit head) ++ (field tail).flatMap inputImages =
        some head :: tail.map some
      rw [ih]
      cases head <;> rfl

theorem inputImages_number (value : Nat) :
    (numberEncoding value).flatMap inputImages = inputBits value := by
  rw [numberEncoding_eq]
  simp only [List.flatMap_cons, List.flatMap_append, inputImages,
    List.nil_append, List.flatMap_nil, List.append_nil]
  rw [inputImages_field, naturalKey_eq_naturalBits]
  rfl

theorem inputBits_length (value : Nat) :
    (inputBits value).length + 1 = (numberEncoding value).length := by
  simp [inputBits, numberEncoding_eq, field, naturalKey_eq_naturalBits, Nat.add_assoc]

noncomputable def readRealization :
    TM2ComputableInPolyTime numberEncoding inputBits id where
  tm := WordHomomorphismMachine.machine inputImages
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := C 4 * X + C 2
  outputsFun value := by
    have run := WordHomomorphismMachine.outputs inputImages (numberEncoding value)
    rw [inputImages_number] at run
    change TM2OutputsInTime (WordHomomorphismMachine.machine inputImages) ((numberEncoding value).map id)
      (some ((inputBits value).map id)) _
    simp only [List.map_id_fun]
    refine ⟨run.toEvalsTo, run.steps_le_m.trans ?_⟩
    have bound := inputBits_length value
    simp only [eval_add, eval_mul, eval_C, eval_X]
    omega

def offsetTemplate (offset : Nat) : WordTemplateMachine.Template (Option Bool) :=
  none :: ((BinaryStackArithmetic.naturalBits offset).map some).map some

theorem offsetTemplate_exact (offset value : Nat) :
    WordTemplateMachine.instantiate (offsetTemplate offset) (inputBits value) =
      BinaryWordAddition.encodedInput (value, offset) := by
  simp only [offsetTemplate, WordTemplateMachine.instantiate_hole,
    WordTemplateMachine.instantiate_literals, inputBits,
    BinaryWordAddition.encodedInput, BinaryWordAddition.packet, List.append_assoc]
  rfl

noncomputable def offsetRealization (offset : Nat) :
    TM2ComputableInPolyTime inputBits BinaryWordAddition.encodedInput
      (fun value => (value, offset)) where
  tm := WordTemplateMachine.machine (offsetTemplate offset)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := C (4 * ((offsetTemplate offset).length + 1)) * (X + C 1)
  outputsFun value := by
    have run := WordTemplateMachine.outputs (offsetTemplate offset) (inputBits value)
    rw [offsetTemplate_exact] at run
    change TM2OutputsInTime (WordTemplateMachine.machine (offsetTemplate offset)) ((inputBits value).map id)
      (some ((BinaryWordAddition.encodedInput (value, offset)).map id)) _
    simpa only [List.map_id_fun, id_eq, eval_mul, eval_C, eval_add, eval_X] using run

theorem offsetPacket_length (offset value : Nat) :
    (BinaryWordAddition.encodedInput (value, offset)).length ≤
      (numberEncoding value).length + (BinaryStackArithmetic.naturalBits offset).length := by
  simp only [BinaryWordAddition.encodedInput, BinaryWordAddition.packet,
    numberEncoding_eq, field, naturalKey_eq_naturalBits, List.length_append,
    List.length_cons, List.length_map, List.length_nil]
  omega

noncomputable def packetRealization (offset : Nat) :
    TM2ComputableInPolyTime numberEncoding BinaryWordAddition.encodedInput
      (fun value => (value, offset)) := by
  exact ExecutedComposition.realization readRealization (offsetRealization offset) X
    (fun value => by
      have h := inputBits_length value
      simpa only [eval_X, id_eq] using
        (show (inputBits value).length ≤ (numberEncoding value).length by omega))

def outputBits (value : Nat) : List (Option Bool) :=
  (BinaryStackArithmetic.naturalBits value).map some

noncomputable def additionRealization (offset : Nat) :
    TM2ComputableInPolyTime numberEncoding outputBits (fun value => value + offset) := by
  exact ExecutedComposition.realization (packetRealization offset) BinaryWordAddition.realization
    (X + C (BinaryStackArithmetic.naturalBits offset).length)
    (fun value => by simpa only [eval_add, eval_X, eval_C] using offsetPacket_length offset value)

def outputImages : Option Bool → List Alphabet
  | some false => [0]
  | some true => [1]
  | none => [4]

def outputField (value : Nat) : List Alphabet := field (naturalKey value)

theorem outputImages_bits (value : Nat) :
    (outputBits value).flatMap outputImages = outputField value := by
  simp only [outputBits, outputField, naturalKey_eq_naturalBits, field]
  induction BinaryStackArithmetic.naturalBits value with
  | nil => rfl
  | cons head tail ih => cases head <;> simp [outputImages, bit, ih]

theorem outputField_length (value : Nat) :
    (outputField value).length = (outputBits value).length := by
  simp [outputField, outputBits, field, naturalKey_eq_naturalBits]

noncomputable def outputRealization :
    TM2ComputableInPolyTime outputBits outputField id where
  tm := WordHomomorphismMachine.machine outputImages
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := C 4 * X + C 2
  outputsFun value := by
    have run := WordHomomorphismMachine.outputs outputImages (outputBits value)
    rw [outputImages_bits] at run
    change TM2OutputsInTime (WordHomomorphismMachine.machine outputImages) ((outputBits value).map id)
      (some ((outputField value).map id)) _
    simp only [List.map_id_fun]
    refine ⟨run.toEvalsTo, run.steps_le_m.trans ?_⟩
    simp only [outputField_length, eval_add, eval_mul, eval_C, eval_X]
    omega

theorem sumBits_length (offset value : Nat) :
    (outputBits (value + offset)).length ≤
      (numberEncoding value).length + (BinaryStackArithmetic.naturalBits offset).length + 1 := by
  have bits := BinaryWordAddition.naturalBits_add_length value offset
  simp only [outputBits, List.length_map]
  have source := inputBits_length value
  simp only [inputBits, List.length_append, List.length_map, List.length_cons,
    List.length_nil] at source
  omega

noncomputable def fieldRealization (offset : Nat) :
    TM2ComputableInPolyTime numberEncoding outputField (fun value => value + offset) := by
  exact ExecutedComposition.realization (additionRealization offset) outputRealization
    (X + C ((BinaryStackArithmetic.naturalBits offset).length + 1))
    (fun value => by simpa only [eval_add, eval_X, eval_C, Nat.add_assoc] using sumBits_length offset value)

def outputTemplate : WordTemplateMachine.Template Alphabet := [some 3, none, some 2]

theorem outputTemplate_exact (value : Nat) :
    WordTemplateMachine.instantiate outputTemplate (outputField value) = numberEncoding value := by
  rw [numberEncoding_eq]
  simp [outputTemplate, outputField]

noncomputable def frameRealization :
    TM2ComputableInPolyTime outputField numberEncoding id where
  tm := WordTemplateMachine.machine outputTemplate
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := C 16 * (X + C 1)
  outputsFun value := by
    have run := WordTemplateMachine.outputs outputTemplate (outputField value)
    rw [outputTemplate_exact] at run
    change TM2OutputsInTime (WordTemplateMachine.machine outputTemplate) ((outputField value).map id)
      (some ((numberEncoding value).map id)) _
    simpa only [List.map_id_fun, id_eq, outputTemplate, List.length_cons, List.length_nil,
      eval_mul, eval_C, eval_add, eval_X, Nat.reduceAdd, Nat.reduceMul] using run

/-- Fixed local graph offsets are added by an actual binary-word machine.
Every original source digit, emitted digit, transfer and framing operation is
charged. The offset is part of the fixed program, while the base is unbounded
physical input. This is an image-domain arithmetic operation, not a raw decoder. -/
noncomputable def realization (offset : Nat) :
    TM2ComputableInPolyTime numberEncoding numberEncoding (fun value => value + offset) := by
  exact ExecutedComposition.realization (fieldRealization offset) frameRealization
    (X + C ((BinaryStackArithmetic.naturalBits offset).length + 1))
    (fun value => by
      rw [outputField_length]
      simpa only [eval_add, eval_X, eval_C, Nat.add_assoc] using sumBits_length offset value)

noncomputable def outputs (offset value : Nat) :
    TM2OutputsInTime (realization offset).tm
      ((numberEncoding value).map (realization offset).inputAlphabet.symm)
      (some ((numberEncoding (value + offset)).map (realization offset).outputAlphabet.symm))
      ((realization offset).time.eval (numberEncoding value).length) :=
  (realization offset).outputsFun value

theorem result_decodes (offset value : Nat) :
    Binary.decodeWith Codec.nat (numberEncoding (value + offset)) = some (value + offset) :=
  Binary.decodeWith_encodeWith Codec.nat (value + offset)

open Turing Polynomial Mettapedia.Computability
attribute [local implicit_reducible] StackMachineComposition.machine
  WordHomomorphismMachine.machine WordTemplateMachine.machine BinaryWordAddition.machine

local instance : Fintype ((WordHomomorphismMachine.machine inputImages).Γ
    (WordHomomorphismMachine.machine inputImages).k₁) := by
  change Fintype (Option Bool); infer_instance
local instance : Inhabited ((WordHomomorphismMachine.machine inputImages).Γ
    (WordHomomorphismMachine.machine inputImages).k₁) := by
  change Inhabited (Option Bool); infer_instance

def packetMachine (offset : Nat) : FinTM2 := StackMachineComposition.machine
  (WordHomomorphismMachine.machine inputImages)
  (WordTemplateMachine.machine (offsetTemplate offset)) (Equiv.refl _)
attribute [local implicit_reducible] packetMachine

local instance (offset : Nat) : Fintype ((packetMachine offset).Γ (packetMachine offset).k₁) := by
  change Fintype (Option Bool); infer_instance
local instance (offset : Nat) : Inhabited ((packetMachine offset).Γ (packetMachine offset).k₁) := by
  change Inhabited (Option Bool); infer_instance

def additionMachine (offset : Nat) : FinTM2 := StackMachineComposition.machine
  (packetMachine offset) BinaryWordAddition.machine (Equiv.refl _)
attribute [local implicit_reducible] additionMachine

local instance (offset : Nat) : Fintype ((additionMachine offset).Γ (additionMachine offset).k₁) := by
  change Fintype (Option Bool); infer_instance
local instance (offset : Nat) : Inhabited ((additionMachine offset).Γ (additionMachine offset).k₁) := by
  change Inhabited (Option Bool); infer_instance

def fieldMachine (offset : Nat) : FinTM2 := StackMachineComposition.machine
  (additionMachine offset) (WordHomomorphismMachine.machine outputImages) (Equiv.refl _)
attribute [local implicit_reducible] fieldMachine

local instance (offset : Nat) : Fintype ((fieldMachine offset).Γ (fieldMachine offset).k₁) := by
  change Fintype Alphabet; infer_instance
local instance (offset : Nat) : Inhabited ((fieldMachine offset).Γ (fieldMachine offset).k₁) := by
  change Inhabited Alphabet; infer_instance

def machine (offset : Nat) : FinTM2 := StackMachineComposition.machine
  (fieldMachine offset) (WordTemplateMachine.machine outputTemplate) (Equiv.refl _)
attribute [local implicit_reducible] machine

theorem realization_machine (offset : Nat) : (realization offset).tm = machine offset := rfl

def packetProgram (offset : Nat) : (packetMachine offset).Λ → (packetMachine offset).Stmt :=
  StackMachineComposition.Programs.body
    (FirstAlphabet := (WordHomomorphismMachine.machine inputImages).Γ)
    (SecondAlphabet := (WordTemplateMachine.machine (offsetTemplate offset)).Γ) .result .input (.emit ⟨0, by omega⟩) none id
    (WordHomomorphismMachine.program inputImages) (WordTemplateMachine.program (offsetTemplate offset))

theorem packetProgram_eq (offset : Nat) : packetProgram offset = (packetMachine offset).m :=
  StackMachineComposition.body_eq (WordHomomorphismMachine.machine inputImages)
    (WordTemplateMachine.machine (offsetTemplate offset)) (Equiv.refl _)

def additionProgram (offset : Nat) : (additionMachine offset).Λ → (additionMachine offset).Stmt :=
  StackMachineComposition.Programs.body
    (FirstAlphabet := (packetMachine offset).Γ)
    (SecondAlphabet := BinaryWordAddition.machine.Γ) (some (.inr .input)) .input .scan none id
    (packetProgram offset) BinaryWordAddition.program

theorem additionProgram_eq (offset : Nat) : additionProgram offset = (additionMachine offset).m := by
  unfold additionProgram
  rw [packetProgram_eq]
  exact StackMachineComposition.body_eq (packetMachine offset) BinaryWordAddition.machine (Equiv.refl _)

def fieldProgram (offset : Nat) : (fieldMachine offset).Λ → (fieldMachine offset).Stmt :=
  StackMachineComposition.Programs.body
    (FirstAlphabet := (additionMachine offset).Γ)
    (SecondAlphabet := (WordHomomorphismMachine.machine outputImages).Γ) (some (.inr .result)) .input .read none id
    (additionProgram offset) (WordHomomorphismMachine.program outputImages)

theorem fieldProgram_eq (offset : Nat) : fieldProgram offset = (fieldMachine offset).m := by
  unfold fieldProgram
  rw [additionProgram_eq]
  exact StackMachineComposition.body_eq (additionMachine offset)
    (WordHomomorphismMachine.machine outputImages) (Equiv.refl _)

def program (offset : Nat) : (machine offset).Λ → (machine offset).Stmt :=
  StackMachineComposition.Programs.body
    (FirstAlphabet := (fieldMachine offset).Γ)
    (SecondAlphabet := (WordTemplateMachine.machine outputTemplate).Γ) (some (.inr .result)) .input (.emit ⟨0, by omega⟩) (show Alphabet from 0) id
    (fieldProgram offset) (WordTemplateMachine.program outputTemplate)

theorem program_eq (offset : Nat) : program offset = (machine offset).m := by
  unfold program
  rw [fieldProgram_eq]
  exact StackMachineComposition.body_eq (fieldMachine offset)
    (WordTemplateMachine.machine outputTemplate) (Equiv.refl _)

def optionEquality {α : Type} (eq : DecidableEq α) : DecidableEq (Option α) :=
  @Option.instDecidableEq α eq

def sumEquality {α β : Type} (first : DecidableEq α) (second : DecidableEq β) : DecidableEq (α ⊕ β) :=
  fun x y => @instDecidableEqSum α β first second x y

def keyEquality (offset : Nat) : DecidableEq (machine offset).K :=
  optionEquality (sumEquality (optionEquality (sumEquality (optionEquality
    (sumEquality (optionEquality (sumEquality WordHomomorphismMachine.instDecidableEqStack
      WordTemplateMachine.instDecidableEqStack)) BinaryWordAddition.instDecidableEqStack))
      WordHomomorphismMachine.instDecidableEqStack)) WordTemplateMachine.instDecidableEqStack)

def step (offset : Nat) : (machine offset).Cfg → Option (machine offset).Cfg :=
  @TM2.step _ _ _ _ (keyEquality offset) (program offset)

theorem step_eq (offset : Nat) : step offset = (machine offset).step := by
  unfold step
  rw [show keyEquality offset = (machine offset).kDecidableEq from Subsingleton.elim _ _]
  rw [program_eq]
  rfl

theorem time_exact (offset size : Nat) :
    (realization offset).time.eval size =
      (4 * (BinaryStackArithmetic.naturalBits offset).length + 45) * size +
        35 * (BinaryStackArithmetic.naturalBits offset).length + 68 := by
  simp only [realization, fieldRealization, additionRealization, packetRealization,
    readRealization, offsetRealization, outputRealization, frameRealization,
    Mettapedia.GSLT.LanguageDef.ProofSystems.ExecutedComposition.realization,
    BinaryWordAddition.realization, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_comp, offsetTemplate,
    List.length_cons, List.length_map]
  ring


/-- The concrete exposed transition table executes the original numeric codec
through the complete digit, arithmetic and framing pipeline. -/
noncomputable def encodedOutputs (offset value : Nat) :
    TM2OutputsInTime (machine offset) (numberEncoding value)
      (some (numberEncoding (value + offset)))
      ((4 * (BinaryStackArithmetic.naturalBits offset).length + 45) *
        (numberEncoding value).length + 35 * (BinaryStackArithmetic.naturalBits offset).length + 68) := by
  have run := outputs offset value
  change TM2OutputsInTime (machine offset) ((numberEncoding value).map id)
    (some ((numberEncoding (value + offset)).map id)) _ at run
  simpa only [List.map_id_fun, id_eq, time_exact] using run

end PhysicalAddress

end Mettapedia.GSLT.LanguageDef.SharedReferenceExecution

namespace Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.ChainedCache
set_option backward.isDefEq.respectTransparency false
open Turing Mettapedia.Computability Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
attribute [local implicit_reducible] StackMachineComposition.machine
  WordTemplateMachine.machine WordTemplateMachine.Indexed.machine
  WordHomomorphismMachine.machine RetainedWordExecution.WithOutput.machine
  SharedReferenceExecution.machine

abbrev AWord := List SharedReferenceExecution.Alphabet
abbrev Fields (arity : Nat) := Fin arity → AWord

def sourceFields {A : Type} (codec : Codec A) (roots : Array Nat) (values : Array A) (query : Nat) : Fields 3 :=
  ![field (naturalKey query) ++ [2], table (indexed roots), table (EncodedTable.rows codec values)]
def sourcePacket {A : Type} (codec : Codec A) (roots : Array Nat) (values : Array A) (query : Nat) :=
  WordTemplateMachine.Indexed.argumentWire (sourceFields codec roots values query)
def firstTemplate : WordTemplateMachine.Indexed.Template SharedReferenceExecution.Alphabet 3 :=
  [.inr 0,.inr 1]
local instance : Fintype ((WordTemplateMachine.Indexed.machine firstTemplate).Γ
    (WordTemplateMachine.Indexed.machine firstTemplate).k₁) := inferInstanceAs (Fintype SharedReferenceExecution.Alphabet)
local instance : Inhabited ((WordTemplateMachine.Indexed.machine firstTemplate).Γ
    (WordTemplateMachine.Indexed.machine firstTemplate).k₁) := inferInstanceAs (Inhabited SharedReferenceExecution.Alphabet)
local instance : Inhabited (SharedReferenceExecution.machine.Γ SharedReferenceExecution.machine.k₀) :=
  inferInstanceAs (Inhabited SharedReferenceExecution.Alphabet)
@[reducible, macro_inline] def firstMachine := StackMachineComposition.machine (WordTemplateMachine.Indexed.machine firstTemplate)
  SharedReferenceExecution.machine (Equiv.refl SharedReferenceExecution.Alphabet)
local instance : Fintype (firstMachine.Γ firstMachine.k₁) := inferInstanceAs (Fintype SharedReferenceExecution.Alphabet)
local instance : Inhabited (firstMachine.Γ firstMachine.k₀) := inferInstanceAs (Inhabited (Option SharedReferenceExecution.Alphabet))
local instance : Inhabited (firstMachine.Γ firstMachine.k₁) := inferInstanceAs (Inhabited SharedReferenceExecution.Alphabet)

/-- The first physical query uses the submitted binary index and root table. -/
theorem firstTemplate_exact {A : Type} (codec : Codec A) (roots : Array Nat) (values : Array A) (query : Nat) :
    WordTemplateMachine.Indexed.instantiate firstTemplate (sourceFields codec roots values query) =
      referencePacket roots query := by
  simp [firstTemplate,sourceFields,referencePacket,packet,WordTemplateMachine.Indexed.instantiate]

theorem sourcePacket_length {A : Type} (codec : Codec A) (roots : Array Nat) (values : Array A) (query : Nat) :
    (sourcePacket codec roots values query).length =
      (referencePacket roots query).length + (table (EncodedTable.rows codec values)).length + 3 := by
  simp only [sourcePacket,sourceFields,WordTemplateMachine.Indexed.argumentWire_length,
    List.finRange_succ,List.finRange_zero,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    Matrix.cons_val_zero,Matrix.cons_val_succ,List.length_append,List.length_cons,List.length_nil,
    referencePacket,packet]
  omega

/-- Original source-root resolution is executed before theorem-cache access. -/
def firstOutputs {A : Type} (codec : Codec A) (roots : Array Nat) (values : Array A) (query : Nat) :
    let size := (sourcePacket codec roots values query).length
    TM2OutputsInTime firstMachine (sourcePacket codec roots values query)
      (some (physicalOutput roots[query]?)) (4*size^2+40*size+60) := by
  have prepared := WordTemplateMachine.Indexed.outputs firstTemplate (sourceFields codec roots values query)
  rw [firstTemplate_exact] at prepared
  have resolved := SharedReferenceExecution.referenceOutputs roots query
  have identity : (referencePacket roots query).map (Equiv.refl SharedReferenceExecution.Alphabet) =
      referencePacket roots query := by simp
  rw [← identity] at resolved
  have joined := StackMachineComposition.outputs
    (WordTemplateMachine.Indexed.machine firstTemplate) SharedReferenceExecution.machine
    (Equiv.refl SharedReferenceExecution.Alphabet)
    (sourcePacket codec roots values query) (referencePacket roots query)
    (physicalOutput roots[query]?) _ _ prepared resolved
  have bounded : (referencePacket roots query).length ≤ (sourcePacket codec roots values query).length := by
    have counted := sourcePacket_length codec roots values query
    omega
  dsimp only
  refine ⟨joined.toEvalsTo,joined.steps_le_m.trans ?_⟩
  simp only [firstTemplate,List.length_cons,List.length_nil,List.length_map] at ⊢
  dsimp only [sourcePacket] at bounded ⊢
  nlinarith [Nat.pow_le_pow_left bounded 2]

@[reducible, macro_inline] def retainedMachine := RetainedWordExecution.WithOutput.machine firstMachine

def untag (symbol : Sum (Option SharedReferenceExecution.Alphabet) SharedReferenceExecution.Alphabet) :
    List (Option SharedReferenceExecution.Alphabet) :=
  match symbol with | .inl value => [value] | .inr value => [some value]
def closeTemplate : WordTemplateMachine.Template (Option SharedReferenceExecution.Alphabet) := [none,some none]
local instance : Fintype (retainedMachine.Γ retainedMachine.k₁) :=
  inferInstanceAs (Fintype (Sum (Option SharedReferenceExecution.Alphabet) SharedReferenceExecution.Alphabet))
local instance : Inhabited (retainedMachine.Γ retainedMachine.k₁) :=
  inferInstanceAs (Inhabited (Sum (Option SharedReferenceExecution.Alphabet) SharedReferenceExecution.Alphabet))
local instance : Inhabited ((WordHomomorphismMachine.machine untag).Γ
    (WordHomomorphismMachine.machine untag).k₀) :=
  inferInstanceAs (Inhabited (Sum (Option SharedReferenceExecution.Alphabet) SharedReferenceExecution.Alphabet))
@[reducible, macro_inline] def taggedMachine := StackMachineComposition.machine retainedMachine
  (WordHomomorphismMachine.machine untag)
  (Equiv.refl (Sum (Option SharedReferenceExecution.Alphabet) SharedReferenceExecution.Alphabet))
local instance : Fintype (taggedMachine.Γ taggedMachine.k₁) := inferInstanceAs (Fintype (Option SharedReferenceExecution.Alphabet))
local instance : Inhabited (taggedMachine.Γ taggedMachine.k₁) := inferInstanceAs (Inhabited (Option SharedReferenceExecution.Alphabet))
@[reducible, macro_inline] def preparedMachine := StackMachineComposition.machine taggedMachine
  (WordTemplateMachine.machine closeTemplate) (Equiv.refl (Option SharedReferenceExecution.Alphabet))

theorem framed_machine_same : preparedMachine =
    RetainedWordExecution.WithOutput.Framed.machine firstMachine
      (Equiv.refl (Option SharedReferenceExecution.Alphabet))
      (Equiv.refl SharedReferenceExecution.Alphabet) := by
  have same : untag = RetainedWordExecution.WithOutput.Framed.untag firstMachine
      (Equiv.refl (Option SharedReferenceExecution.Alphabet))
      (Equiv.refl SharedReferenceExecution.Alphabet) := by
    funext symbol
    cases symbol <;> rfl
  unfold preparedMachine taggedMachine retainedMachine closeTemplate
    RetainedWordExecution.WithOutput.Framed.machine
    RetainedWordExecution.WithOutput.Framed.taggedMachine
    RetainedWordExecution.WithOutput.Framed.retainedMachine
    RetainedWordExecution.WithOutput.Framed.closeTemplate
  rw [same]
  rfl


def secondFields {A : Type} (codec : Codec A) (roots : Array Nat) (values : Array A) (query : Nat) : Fields 4 :=
  ![field (naturalKey query) ++ [2],table (indexed roots),table (EncodedTable.rows codec values),physicalOutput roots[query]?]
def preparedPacket {A : Type} (codec : Codec A) (roots : Array Nat) (values : Array A) (query : Nat) :=
  WordTemplateMachine.Indexed.argumentWire (secondFields codec roots values query)

theorem untag_exact (input : List (Option SharedReferenceExecution.Alphabet)) (output : AWord) :
    (input.map Sum.inl ++ output.map Sum.inr).flatMap untag = input ++ output.map some := by
  simp only [List.flatMap_append,List.flatMap_map]
  have left : input.flatMap (fun symbol => untag (.inl symbol)) = input := by
    induction input <;> simp_all [untag]
  have right : output.flatMap (fun symbol => untag (.inr symbol)) = output.map some := by
    induction output <;> simp_all [untag]
  rw [left,right]

theorem preparedPacket_eq {A : Type} (codec : Codec A) (roots : Array Nat) (values : Array A) (query : Nat) :
    preparedPacket codec roots values query =
      sourcePacket codec roots values query ++ (physicalOutput roots[query]?).map some ++ [none] := by
  simp [preparedPacket,sourcePacket,secondFields,sourceFields,
    WordTemplateMachine.Indexed.argumentWire,WordTemplateMachine.Indexed.frame,
    List.finRange_succ,List.finRange_zero,List.append_assoc]

theorem physicalOutput_length_le_sourcePacket {A : Type} (codec : Codec A)
    (roots : Array Nat) (values : Array A) (query : Nat) :
    (physicalOutput roots[query]?).length ≤ (sourcePacket codec roots values query).length := by
  have stored := output_length_le_packet (naturalKey query) (indexed roots)
  rw [lookup_indexed] at stored
  have counted := sourcePacket_length codec roots values query
  change (physicalOutput roots[query]?).length ≤ (referencePacket roots query).length at stored
  omega

/-- Both caches and the resolved root are physically preserved and framed for
second-stage selection. Neither table is captured in the transition program. -/
noncomputable def preparedOutputs {A : Type} (codec : Codec A) (roots : Array Nat) (values : Array A) (query : Nat) :
    let size := (sourcePacket codec roots values query).length
    TM2OutputsInTime preparedMachine (sourcePacket codec roots values query)
      (some (preparedPacket codec roots values query)) (4*size^2+90*size+100) := by
  have joined := RetainedWordExecution.WithOutput.Framed.outputs firstMachine
    (Equiv.refl (Option SharedReferenceExecution.Alphabet))
    (Equiv.refl SharedReferenceExecution.Alphabet)
    (sourcePacket codec roots values query) (physicalOutput roots[query]?) _
    (firstOutputs codec roots values query)
  have retained := StackMachineComposition.outputs_of_machine_eq framed_machine_same.symm
    (secondInput := sourcePacket codec roots values query)
    (secondOutput := some (RetainedWordExecution.WithOutput.Framed.outputWord firstMachine
      (Equiv.refl (Option SharedReferenceExecution.Alphabet)) (Equiv.refl SharedReferenceExecution.Alphabet)
      (sourcePacket codec roots values query) (physicalOutput roots[query]?)))
    HEq.rfl HEq.rfl joined

  have framing : RetainedWordExecution.WithOutput.Framed.outputWord firstMachine
      (Equiv.refl (Option SharedReferenceExecution.Alphabet))
      (Equiv.refl SharedReferenceExecution.Alphabet)
      (sourcePacket codec roots values query) (physicalOutput roots[query]?) =
        preparedPacket codec roots values query := by
    rw [preparedPacket_eq]
    change (sourcePacket codec roots values query).map id ++
      (physicalOutput roots[query]?).map some ++ [none] = _
    simp only [List.map_id]
  rw [framing] at retained
  have bounded := physicalOutput_length_le_sourcePacket codec roots values query
  dsimp only
  refine ⟨retained.toEvalsTo,retained.steps_le_m.trans ?_⟩
  omega


def secondTemplate : WordTemplateMachine.Indexed.Template SharedReferenceExecution.Alphabet 4 := [.inr 3,.inr 2]
def acceptsRoot (status : SharedReferenceExecution.Alphabet) : Bool := status == 1
attribute [local implicit_reducible] StackMachineComposition.Dispatch.machine
local instance : Fintype (EncodedTable.decodedMachine.Γ EncodedTable.decodedMachine.k₁) :=
  inferInstanceAs (Fintype SharedReferenceExecution.Alphabet)
local instance : Inhabited (EncodedTable.decodedMachine.Γ EncodedTable.decodedMachine.k₀) :=
  inferInstanceAs (Inhabited SharedReferenceExecution.Alphabet)
local instance : Inhabited (EncodedTable.decodedMachine.Γ EncodedTable.decodedMachine.k₁) :=
  inferInstanceAs (Inhabited SharedReferenceExecution.Alphabet)
@[reducible, macro_inline] def guardedMachine := StackMachineComposition.Dispatch.machine EncodedTable.decodedMachine acceptsRoot
  ([0] : AWord)
local instance : Fintype ((WordTemplateMachine.Indexed.machine secondTemplate).Γ
    (WordTemplateMachine.Indexed.machine secondTemplate).k₁) := inferInstanceAs (Fintype SharedReferenceExecution.Alphabet)
local instance : Inhabited ((WordTemplateMachine.Indexed.machine secondTemplate).Γ
    (WordTemplateMachine.Indexed.machine secondTemplate).k₁) := inferInstanceAs (Inhabited SharedReferenceExecution.Alphabet)
local instance : Inhabited (guardedMachine.Γ guardedMachine.k₀) := inferInstanceAs (Inhabited SharedReferenceExecution.Alphabet)
@[reducible, macro_inline] def secondMachine := StackMachineComposition.machine (WordTemplateMachine.Indexed.machine secondTemplate)
  guardedMachine (Equiv.refl SharedReferenceExecution.Alphabet)

def selected {A : Type} (roots : Array Nat) (values : Array A) (query : Nat) : Option A :=
  roots[query]?.bind (fun physical => values[physical]?)
def secondPacket {A : Type} (codec : Codec A) (roots : Array Nat) (values : Array A) (query : Nat) : AWord :=
  physicalOutput roots[query]? ++ table (EncodedTable.rows codec values)

theorem secondTemplate_exact {A : Type} (codec : Codec A) (roots : Array Nat) (values : Array A) (query : Nat) :
    WordTemplateMachine.Indexed.instantiate secondTemplate (secondFields codec roots values query) =
      secondPacket codec roots values query := by
  simp [secondTemplate,secondFields,secondPacket,WordTemplateMachine.Indexed.instantiate]

theorem preparedPacket_length {A : Type} (codec : Codec A) (roots : Array Nat) (values : Array A) (query : Nat) :
    (preparedPacket codec roots values query).length =
      (sourcePacket codec roots values query).length + (physicalOutput roots[query]?).length + 1 := by
  rw [preparedPacket_eq]
  simp only [List.length_append,List.length_map,List.length_singleton]

theorem secondPacket_length {A : Type} (codec : Codec A) (roots : Array Nat) (values : Array A) (query : Nat) :
    (secondPacket codec roots values query).length ≤ (preparedPacket codec roots values query).length := by
  have source := sourcePacket_length codec roots values query
  have prepared := preparedPacket_length codec roots values query
  simp only [secondPacket,List.length_append]
  omega

/-- An absent source root is refused before target lookup. A present source
root physically supplies the binary query to the original theorem resolver. -/
def guardedOutputs {A : Type} (codec : Codec A) (roots : Array Nat) (values : Array A) (query : Nat) :
    let size := (secondPacket codec roots values query).length
    TM2OutputsInTime guardedMachine (secondPacket codec roots values query)
      (some (EncodedTable.decodedOutput codec (selected roots values query)))
      (4*size^2+30*size+60) := by
  cases found : roots[query]? with
  | none =>
      have refused := StackMachineComposition.Dispatch.outputs_refused EncodedTable.decodedMachine
        acceptsRoot ([0] : AWord) (0 : SharedReferenceExecution.Alphabet)
        (table (EncodedTable.rows codec values)) (by decide)
      dsimp only
      simpa only [secondPacket,physicalOutput,found,Option.map_none,output,List.singleton_append,
        selected,Option.bind_none,EncodedTable.decodedOutput,Triples.Recovery.decodedResponse,
        List.length_cons] using
        (show TM2OutputsInTime guardedMachine ((0 : SharedReferenceExecution.Alphabet) :: table (EncodedTable.rows codec values))
          (some ([0] : AWord)) (4*((table (EncodedTable.rows codec values)).length+1)^2+
            30*((table (EncodedTable.rows codec values)).length+1)+60) from by
          exact ⟨refused.toEvalsTo,refused.steps_le_m.trans (by omega)⟩)
  | some physical =>
      have decoded := EncodedTable.decodedReferenceOutputs codec values physical
      have success := StackMachineComposition.Dispatch.outputs_success EncodedTable.decodedMachine
        acceptsRoot ([0] : AWord) (1 : SharedReferenceExecution.Alphabet) (EncodedTable.queryPacket codec values physical)
        (EncodedTable.decodedOutput codec values[physical]?) _ (by decide) decoded
      have packet : secondPacket codec roots values query = 1 :: EncodedTable.queryPacket codec values physical := by
        simp only [secondPacket,physicalOutput,found,Option.map_some,output,EncodedTable.queryPacket,packet,
          List.cons_append,List.append_assoc,List.nil_append]
      dsimp only
      rw [packet]
      simp only [selected,found,Option.bind_some]
      refine ⟨success.toEvalsTo,success.steps_le_m.trans ?_⟩
      simp only [List.length_cons]
      nlinarith

/-- Ordered physical field selection and the root-status guard precede the
second cache operation; no lookup result is installed by a host callback. -/
def secondOutputs {A : Type} (codec : Codec A) (roots : Array Nat) (values : Array A) (query : Nat) :
    let size := (preparedPacket codec roots values query).length
    TM2OutputsInTime secondMachine (preparedPacket codec roots values query)
      (some (EncodedTable.decodedOutput codec (selected roots values query)))
      (4*size^2+70*size+100) := by
  have prepared := WordTemplateMachine.Indexed.outputs secondTemplate (secondFields codec roots values query)
  rw [secondTemplate_exact] at prepared
  have guarded := guardedOutputs codec roots values query
  have identity : (secondPacket codec roots values query).map (Equiv.refl SharedReferenceExecution.Alphabet) =
      secondPacket codec roots values query := by simp
  rw [← identity] at guarded
  have joined := StackMachineComposition.outputs (WordTemplateMachine.Indexed.machine secondTemplate)
    guardedMachine (Equiv.refl SharedReferenceExecution.Alphabet)
    (preparedPacket codec roots values query) (secondPacket codec roots values query)
    (EncodedTable.decodedOutput codec (selected roots values query)) _ _ prepared guarded
  have bounded := secondPacket_length codec roots values query
  dsimp only
  refine ⟨joined.toEvalsTo,joined.steps_le_m.trans ?_⟩
  simp only [secondTemplate,List.length_cons,List.length_nil,List.length_map]
  dsimp only [preparedPacket] at bounded ⊢
  nlinarith [Nat.pow_le_pow_left bounded 2]

local instance : Fintype (preparedMachine.Γ preparedMachine.k₁) := inferInstanceAs (Fintype (Option SharedReferenceExecution.Alphabet))
local instance : Inhabited (preparedMachine.Γ preparedMachine.k₁) := inferInstanceAs (Inhabited (Option SharedReferenceExecution.Alphabet))
local instance : Inhabited (secondMachine.Γ secondMachine.k₀) := inferInstanceAs (Inhabited (Option SharedReferenceExecution.Alphabet))
@[reducible, macro_inline] def machine := StackMachineComposition.machine preparedMachine secondMachine (Equiv.refl (Option SharedReferenceExecution.Alphabet))

/-- Two-level chronological resolution is one uniform finite-stack machine.
Both unbounded tables are physical input. Repeated roots retain their original
lookup meaning, while missing source or target rows remain refused. -/
noncomputable def outputs {A : Type} (codec : Codec A) (roots : Array Nat) (values : Array A) (query : Nat) :
    TM2OutputsInTime machine (sourcePacket codec roots values query)
      (some (EncodedTable.decodedOutput codec (selected roots values query)))
      (400*((sourcePacket codec roots values query).length+1)^2) := by
  have first := preparedOutputs codec roots values query
  have second := secondOutputs codec roots values query
  have identity : (preparedPacket codec roots values query).map (Equiv.refl (Option SharedReferenceExecution.Alphabet)) =
      preparedPacket codec roots values query := by simp
  rw [← identity] at second
  have joined := StackMachineComposition.outputs preparedMachine secondMachine (Equiv.refl _)
    (sourcePacket codec roots values query) (preparedPacket codec roots values query)
    (EncodedTable.decodedOutput codec (selected roots values query)) _ _ first second
  have restored := preparedPacket_length codec roots values query
  have rootBound := physicalOutput_length_le_sourcePacket codec roots values query
  have preparedBound : (preparedPacket codec roots values query).length ≤
      2*(sourcePacket codec roots values query).length+1 := by omega
  refine ⟨joined.toEvalsTo,joined.steps_le_m.trans ?_⟩
  simp only [List.length_map]
  nlinarith [Nat.pow_le_pow_left preparedBound 2]

/-- The instruction interface omits finite-state enumerations while retaining
all original stack addresses, handoffs, refusal branches and cleanup steps. -/
def firstProgram : firstMachine.Λ → firstMachine.Stmt :=
  StackMachineComposition.Programs.body
    (FirstAlphabet := (WordTemplateMachine.Indexed.machine firstTemplate).Γ)
    (SecondAlphabet := SharedReferenceExecution.machine.Γ)
    .result .input .scanQuery (0 : SharedReferenceExecution.Alphabet) id
    (WordTemplateMachine.Indexed.program firstTemplate) SharedReferenceExecution.machine.m

def retainedProgram : retainedMachine.Λ → retainedMachine.Stmt :=
  RetainedWordExecution.WithOutput.Programs.statement (Γ := firstMachine.Γ)
    (some (.inl WordTemplateMachine.Indexed.Stack.input))
    (some (.inr SharedReferenceExecution.Stack.input)) none (0 : SharedReferenceExecution.Alphabet)
    (none,SharedReferenceExecution.initial,none) (.inl (.emit ⟨0,by decide⟩)) firstProgram

def taggedProgram : taggedMachine.Λ → taggedMachine.Stmt :=
  StackMachineComposition.Programs.body
    (FirstAlphabet := retainedMachine.Γ)
    (SecondAlphabet := (WordHomomorphismMachine.machine untag).Γ)
    none .input .read (default : Sum (Option SharedReferenceExecution.Alphabet) SharedReferenceExecution.Alphabet) id retainedProgram
    (WordHomomorphismMachine.program untag)

def preparedProgram : preparedMachine.Λ → preparedMachine.Stmt :=
  StackMachineComposition.Programs.body
    (FirstAlphabet := taggedMachine.Γ)
    (SecondAlphabet := (WordTemplateMachine.machine closeTemplate).Γ)
    (some (.inr .result)) .input (.emit ⟨0,by decide⟩) none id
    taggedProgram (WordTemplateMachine.program closeTemplate)

def guardProgram : guardedMachine.Λ → guardedMachine.Stmt
  | .run label => StackMachineComposition.Dispatch.lift EncodedTable.decodedMachine
      (EncodedTable.decodedProgram label)
  | .read => .pop (some (.inl .input)) (fun state value => (state.1,value))
      (.branch (fun state => state.2.any acceptsRoot)
        (.load (fun state => (state.1,none)) (.goto fun _ => .run (.inl .scanQuery)))
        (.goto fun _ => .discard))
  | .discard => .pop (some (.inl .input)) (fun state value => (state.1,value))
      (.branch (fun state => state.2.isSome) (.goto fun _ => .discard)
        (.push (some (.inr .result)) (fun _ => (0 : SharedReferenceExecution.Alphabet))
          (.load (fun _ => ((SharedReferenceExecution.initial,Triples.Recovery.initial,none),none)) .halt)))

def secondProgram : secondMachine.Λ → secondMachine.Stmt :=
  StackMachineComposition.Programs.body
    (FirstAlphabet := (WordTemplateMachine.Indexed.machine secondTemplate).Γ)
    (SecondAlphabet := guardedMachine.Γ)
    .result (some (.inl .input)) .read (0 : SharedReferenceExecution.Alphabet) id
    (WordTemplateMachine.Indexed.program secondTemplate) guardProgram

def program : machine.Λ → machine.Stmt :=
  StackMachineComposition.Programs.body
    (FirstAlphabet := preparedMachine.Γ) (SecondAlphabet := secondMachine.Γ)
    (some (.inr .input)) (some (.inl .input)) (.inl (.emit ⟨0,by decide⟩)) none id
    preparedProgram secondProgram

theorem firstProgram_exact : firstProgram = firstMachine.m := by
  exact StackMachineComposition.body_eq (WordTemplateMachine.Indexed.machine firstTemplate)
    SharedReferenceExecution.machine (Equiv.refl _)
theorem retainedProgram_exact : retainedProgram = retainedMachine.m := by
  unfold retainedProgram
  rw [firstProgram_exact]
  simp only [retainedMachine,RetainedWordExecution.WithOutput.machine]
  congr 1
theorem taggedProgram_exact : taggedProgram = taggedMachine.m := by
  unfold taggedProgram
  rw [retainedProgram_exact]
  exact StackMachineComposition.body_eq retainedMachine
    (WordHomomorphismMachine.machine untag) (Equiv.refl _)
theorem preparedProgram_exact : preparedProgram = preparedMachine.m := by
  unfold preparedProgram
  rw [taggedProgram_exact]
  exact StackMachineComposition.body_eq taggedMachine
    (WordTemplateMachine.machine closeTemplate) (Equiv.refl _)
theorem guardProgram_exact : guardProgram = guardedMachine.m := by
  funext label
  cases label <;> simp only [guardProgram,EncodedTable.decodedProgram_eq]
  all_goals rfl
theorem secondProgram_exact : secondProgram = secondMachine.m := by
  unfold secondProgram
  rw [guardProgram_exact]
  exact StackMachineComposition.body_eq (WordTemplateMachine.Indexed.machine secondTemplate)
    guardedMachine (Equiv.refl _)
theorem program_exact : program = machine.m := by
  unfold program
  rw [preparedProgram_exact,secondProgram_exact]
  exact StackMachineComposition.body_eq preparedMachine secondMachine (Equiv.refl _)

/-- Both unbounded cache tables remain physical input to one fixed finite
machine. The quadratic clock is attached to its actual transition relation. -/
noncomputable def realization {A : Type} (codec : Codec A) :
    TM2ComputableInPolyTime
      (fun input : (Array Nat × Array A) × Nat => sourcePacket codec input.1.1 input.1.2 input.2)
      (EncodedTable.decodedOutput codec)
      (fun input => selected input.1.1 input.1.2 input.2) where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 400 * (Polynomial.X + Polynomial.C 1)^2
  outputsFun input := by
    change TM2OutputsInTime machine ((sourcePacket codec input.1.1 input.1.2 input.2).map id)
      (some ((EncodedTable.decodedOutput codec (selected input.1.1 input.1.2 input.2)).map id))
      ((Polynomial.C 400 * (Polynomial.X + Polynomial.C 1)^2).eval
        (sourcePacket codec input.1.1 input.1.2 input.2).length)
    simp only [List.map_id_fun,Polynomial.eval_mul,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
    exact outputs codec input.1.1 input.1.2 input.2

end Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.ChainedCache


namespace Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.EncodedTable.ReferenceCheck
set_option backward.isDefEq.respectTransparency false
open Turing Mettapedia.Computability Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
attribute [local implicit_reducible] StackMachineComposition.machine
  WordTemplateMachine.machine WordTemplateMachine.Indexed.machine
  WordHomomorphismMachine.machine RetainedWordExecution.WithOutput.machine
  SharedReferenceExecution.machine WordEqualityMachine.machine
abbrev AWord := List SharedReferenceExecution.Alphabet
abbrev Fields (arity : Nat) := Fin arity → AWord

def sourceFields {A : Type} (codec : Codec A) (values : Array A) (query : Nat) (expected : A) : Fields 3 :=
  ![field (naturalKey query) ++ [2], table (rows codec values), 1 :: encodeWith codec expected]
def sourcePacket {A : Type} (codec : Codec A) (values : Array A) (query : Nat) (expected : A) :=
  WordTemplateMachine.Indexed.argumentWire (sourceFields codec values query expected)
def firstTemplate : WordTemplateMachine.Indexed.Template SharedReferenceExecution.Alphabet 3 :=
  [.inr 0,.inr 1]
local instance : Fintype ((WordTemplateMachine.Indexed.machine firstTemplate).Γ
    (WordTemplateMachine.Indexed.machine firstTemplate).k₁) := inferInstanceAs (Fintype SharedReferenceExecution.Alphabet)
local instance : Inhabited ((WordTemplateMachine.Indexed.machine firstTemplate).Γ
    (WordTemplateMachine.Indexed.machine firstTemplate).k₁) := inferInstanceAs (Inhabited SharedReferenceExecution.Alphabet)
local instance : Inhabited (decodedMachine.Γ decodedMachine.k₀) :=
  inferInstanceAs (Inhabited SharedReferenceExecution.Alphabet)
local instance : Fintype (decodedMachine.Γ decodedMachine.k₁) :=
  inferInstanceAs (Fintype SharedReferenceExecution.Alphabet)
local instance : Inhabited (decodedMachine.Γ decodedMachine.k₁) :=
  inferInstanceAs (Inhabited SharedReferenceExecution.Alphabet)
@[reducible, macro_inline] def firstMachine := StackMachineComposition.machine (WordTemplateMachine.Indexed.machine firstTemplate)
  decodedMachine (Equiv.refl SharedReferenceExecution.Alphabet)
local instance : Fintype (firstMachine.Γ firstMachine.k₁) := inferInstanceAs (Fintype SharedReferenceExecution.Alphabet)
local instance : Inhabited (firstMachine.Γ firstMachine.k₀) := inferInstanceAs (Inhabited (Option SharedReferenceExecution.Alphabet))
local instance : Inhabited (firstMachine.Γ firstMachine.k₁) := inferInstanceAs (Inhabited SharedReferenceExecution.Alphabet)

/-- Selection operates on the physically supplied cache before comparison. -/
theorem firstTemplate_exact {A : Type} (codec : Codec A) (values : Array A) (query : Nat) (expected : A) :
    WordTemplateMachine.Indexed.instantiate firstTemplate (sourceFields codec values query expected) =
      queryPacket codec values query := by
  simp [firstTemplate,sourceFields,queryPacket,packet,WordTemplateMachine.Indexed.instantiate]

theorem sourcePacket_length {A : Type} (codec : Codec A) (values : Array A) (query : Nat) (expected : A) :
    (sourcePacket codec values query expected).length =
      (queryPacket codec values query).length + (encodeWith codec expected).length + 4 := by
  simp only [sourcePacket,sourceFields,WordTemplateMachine.Indexed.argumentWire_length,
    List.finRange_succ,List.finRange_zero,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    Matrix.cons_val_zero,Matrix.cons_val_succ,List.length_append,List.length_cons,List.length_nil,
    queryPacket,packet,field,List.length_map]
  omega

theorem decodedOutput_length {A : Type} (codec : Codec A) (values : Array A) (query : Nat) :
    (decodedOutput codec values[query]?).length ≤ (queryPacket codec values query).length := by
  have stored := output_length_le_packet (naturalKey query) (rows codec values)
  rw [lookup_rows] at stored
  have recovered : (decodedOutput codec values[query]?).length ≤
      (output (values[query]?.map (value codec))).length := by
    cases found : values[query]? with
    | none => simp [decodedOutput,Triples.Recovery.decodedResponse,output]
    | some selected =>
      simp only [decodedOutput,Option.map_some,Triples.Recovery.decodedResponse,
        Triples.Recovery.result,output,field,List.length_cons,List.length_append,
        List.length_nil,List.length_map]
      rw [encoded_length]
      omega
  exact recovered.trans stored

def firstOutputs {A : Type} (codec : Codec A) (values : Array A) (query : Nat) (expected : A) :
    let size := (sourcePacket codec values query expected).length
    TM2OutputsInTime firstMachine (sourcePacket codec values query expected)
      (some (decodedOutput codec values[query]?)) (4*size^2+50*size+70) := by
  have prepared := WordTemplateMachine.Indexed.outputs firstTemplate (sourceFields codec values query expected)
  rw [firstTemplate_exact] at prepared
  have resolved := decodedReferenceOutputs codec values query
  have identity : (queryPacket codec values query).map (Equiv.refl SharedReferenceExecution.Alphabet) =
      queryPacket codec values query := by simp
  rw [← identity] at resolved
  have joined := StackMachineComposition.outputs
    (WordTemplateMachine.Indexed.machine firstTemplate) decodedMachine
    (Equiv.refl SharedReferenceExecution.Alphabet)
    (sourcePacket codec values query expected) (queryPacket codec values query)
    (decodedOutput codec values[query]?) _ _ prepared resolved
  have bounded : (queryPacket codec values query).length ≤ (sourcePacket codec values query expected).length := by
    have counted := sourcePacket_length codec values query expected
    omega
  dsimp only
  refine ⟨joined.toEvalsTo,joined.steps_le_m.trans ?_⟩
  simp only [firstTemplate,List.length_cons,List.length_nil,List.length_map]
  dsimp only [sourcePacket] at bounded ⊢
  nlinarith [Nat.pow_le_pow_left bounded 2]

@[reducible, macro_inline] def preparedMachine := RetainedWordExecution.WithOutput.Framed.machine firstMachine
  (Equiv.refl (Option SharedReferenceExecution.Alphabet)) (Equiv.refl SharedReferenceExecution.Alphabet)
local instance : Fintype (preparedMachine.Γ preparedMachine.k₁) := inferInstanceAs (Fintype (Option SharedReferenceExecution.Alphabet))
local instance : Inhabited (preparedMachine.Γ preparedMachine.k₁) := inferInstanceAs (Inhabited (Option SharedReferenceExecution.Alphabet))
def preparedFields {A : Type} (codec : Codec A) (values : Array A) (query : Nat) (expected : A) : Fields 4 :=
  ![field (naturalKey query) ++ [2],table (rows codec values),1 :: encodeWith codec expected,decodedOutput codec values[query]?]
def preparedPacket {A : Type} (codec : Codec A) (values : Array A) (query : Nat) (expected : A) :=
  WordTemplateMachine.Indexed.argumentWire (preparedFields codec values query expected)

theorem preparedPacket_eq {A : Type} (codec : Codec A) (values : Array A) (query : Nat) (expected : A) :
    preparedPacket codec values query expected =
      sourcePacket codec values query expected ++ (decodedOutput codec values[query]?).map some ++ [none] := by
  simp [preparedPacket,sourcePacket,preparedFields,sourceFields,
    WordTemplateMachine.Indexed.argumentWire,WordTemplateMachine.Indexed.frame,
    List.finRange_succ,List.finRange_zero,List.append_assoc]

noncomputable def preparedOutputs {A : Type} (codec : Codec A) (values : Array A) (query : Nat) (expected : A) :
    let size := (sourcePacket codec values query expected).length
    TM2OutputsInTime preparedMachine (sourcePacket codec values query expected)
      (some (preparedPacket codec values query expected)) (4*size^2+100*size+100) := by
  have joined := RetainedWordExecution.WithOutput.Framed.outputs firstMachine
    (Equiv.refl (Option SharedReferenceExecution.Alphabet)) (Equiv.refl SharedReferenceExecution.Alphabet)
    (sourcePacket codec values query expected) (decodedOutput codec values[query]?) _
    (firstOutputs codec values query expected)
  have framing : RetainedWordExecution.WithOutput.Framed.outputWord firstMachine
      (Equiv.refl (Option SharedReferenceExecution.Alphabet)) (Equiv.refl SharedReferenceExecution.Alphabet)
      (sourcePacket codec values query expected) (decodedOutput codec values[query]?) =
        preparedPacket codec values query expected := by
    rw [preparedPacket_eq]
    change (sourcePacket codec values query expected).map id ++
      (decodedOutput codec values[query]?).map some ++ [none] = _
    simp only [List.map_id]
  rw [framing] at joined
  have outputBound := decodedOutput_length codec values query
  have inputBound := sourcePacket_length codec values query expected
  dsimp only
  refine ⟨joined.toEvalsTo,joined.steps_le_m.trans ?_⟩
  omega

/-- Preserve the existing four fields while changing the data alphabet for
word equality's separate delimiter. -/
def liftSymbol : Option SharedReferenceExecution.Alphabet → List (Option (Option SharedReferenceExecution.Alphabet))
  | none => [none]
  | some value => [some (some value)]
def comparisonFields {A : Type} (codec : Codec A) (values : Array A) (query : Nat) (expected : A) :
    Fin 4 → List (Option SharedReferenceExecution.Alphabet) :=
  fun index => (preparedFields codec values query expected index).map some

theorem lift_frame (words : List AWord) :
    (WordTemplateMachine.Indexed.frame words).flatMap liftSymbol =
      WordTemplateMachine.Indexed.frame (words.map (List.map some)) := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
    simp only [WordTemplateMachine.Indexed.frame,List.flatMap_cons,List.flatMap_append,
      List.flatMap_cons,List.flatMap_nil,List.map_cons]
    change (word.map some).flatMap liftSymbol ++ (liftSymbol none ++ []) ++
      (WordTemplateMachine.Indexed.frame rest).flatMap liftSymbol =
      (word.map some).map some ++ [none] ++
        WordTemplateMachine.Indexed.frame (rest.map (List.map some))
    rw [ih]
    have inner : (word.map some).flatMap liftSymbol = (word.map some).map some := by
      induction word <;> simp_all [liftSymbol]
    rw [inner]
    rfl

theorem lift_exact {A : Type} (codec : Codec A) (values : Array A) (query : Nat) (expected : A) :
    (preparedPacket codec values query expected).flatMap liftSymbol =
      WordTemplateMachine.Indexed.argumentWire (comparisonFields codec values query expected) := by
  unfold preparedPacket WordTemplateMachine.Indexed.argumentWire
  rw [lift_frame]
  simp only [List.map_map,Function.comp_def]
  rfl

@[reducible, macro_inline] def liftedMachine := StackMachineComposition.machine preparedMachine
  (WordHomomorphismMachine.machine liftSymbol) (Equiv.refl (Option SharedReferenceExecution.Alphabet))
local instance : Fintype (liftedMachine.Γ liftedMachine.k₁) := inferInstanceAs (Fintype (Option (Option SharedReferenceExecution.Alphabet)))
local instance : Inhabited (liftedMachine.Γ liftedMachine.k₁) := inferInstanceAs (Inhabited (Option (Option SharedReferenceExecution.Alphabet)))
local instance : Inhabited ((WordHomomorphismMachine.machine liftSymbol).Γ
    (WordHomomorphismMachine.machine liftSymbol).k₀) := inferInstanceAs (Inhabited (Option SharedReferenceExecution.Alphabet))

def secondTemplate : WordTemplateMachine.Indexed.Template (Option SharedReferenceExecution.Alphabet) 4 :=
  [.inr 2,.inl none,.inr 3]
local instance : Fintype ((WordTemplateMachine.Indexed.machine secondTemplate).Γ
    (WordTemplateMachine.Indexed.machine secondTemplate).k₁) := inferInstanceAs (Fintype (Option SharedReferenceExecution.Alphabet))
local instance : Inhabited ((WordTemplateMachine.Indexed.machine secondTemplate).Γ
    (WordTemplateMachine.Indexed.machine secondTemplate).k₁) := inferInstanceAs (Inhabited (Option SharedReferenceExecution.Alphabet))
local instance : Inhabited ((WordEqualityMachine.machine SharedReferenceExecution.Alphabet).Γ
    (WordEqualityMachine.machine SharedReferenceExecution.Alphabet).k₀) := inferInstanceAs (Inhabited (Option SharedReferenceExecution.Alphabet))
@[reducible, macro_inline] def secondMachine := StackMachineComposition.machine (WordTemplateMachine.Indexed.machine secondTemplate)
  (WordEqualityMachine.machine SharedReferenceExecution.Alphabet) (Equiv.refl (Option SharedReferenceExecution.Alphabet))
local instance : Inhabited (secondMachine.Γ secondMachine.k₀) := inferInstanceAs (Inhabited (Option (Option SharedReferenceExecution.Alphabet)))
@[reducible, macro_inline] def machine := StackMachineComposition.machine liftedMachine secondMachine
  (Equiv.refl (Option (Option SharedReferenceExecution.Alphabet)))

theorem secondTemplate_exact {A : Type} (codec : Codec A) (values : Array A) (query : Nat) (expected : A) :
    WordTemplateMachine.Indexed.instantiate secondTemplate (comparisonFields codec values query expected) =
      WordEqualityMachine.packet (1::encodeWith codec expected) (decodedOutput codec values[query]?) := by
  simp [secondTemplate,comparisonFields,preparedFields,WordTemplateMachine.Indexed.instantiate,
    WordEqualityMachine.packet]

theorem preparedPacket_length {A : Type} (codec : Codec A) (values : Array A) (query : Nat) (expected : A) :
    (preparedPacket codec values query expected).length =
      (sourcePacket codec values query expected).length + (decodedOutput codec values[query]?).length + 1 := by
  rw [preparedPacket_eq]
  simp only [List.length_append,List.length_map,List.length_singleton]

theorem lifted_length (word : List (Option SharedReferenceExecution.Alphabet)) :
    (word.flatMap liftSymbol).length = word.length := by
  induction word with
  | nil => rfl
  | cons symbol rest ih => cases symbol <;> simp [liftSymbol,ih]

noncomputable def liftedOutputs {A : Type} (codec : Codec A) (values : Array A) (query : Nat) (expected : A) :
    let size := (sourcePacket codec values query expected).length
    TM2OutputsInTime liftedMachine (sourcePacket codec values query expected)
      (some (WordTemplateMachine.Indexed.argumentWire (comparisonFields codec values query expected)))
      (4*size^2+120*size+120) := by
  have first := preparedOutputs codec values query expected
  have second := WordHomomorphismMachine.outputs liftSymbol (preparedPacket codec values query expected)
  have liftedSize := lifted_length (preparedPacket codec values query expected)
  rw [lift_exact] at second liftedSize
  have identity : (preparedPacket codec values query expected).map (Equiv.refl _) =
      preparedPacket codec values query expected := by simp
  rw [←identity] at second
  have joined := StackMachineComposition.outputs preparedMachine (WordHomomorphismMachine.machine liftSymbol)
    (Equiv.refl _) (sourcePacket codec values query expected) (preparedPacket codec values query expected)
    (WordTemplateMachine.Indexed.argumentWire (comparisonFields codec values query expected)) _ _ first second
  have counted := preparedPacket_length codec values query expected
  have stored := decodedOutput_length codec values query
  have inputCounted := sourcePacket_length codec values query expected
  dsimp only
  refine ⟨joined.toEvalsTo,joined.steps_le_m.trans ?_⟩
  simp only [List.length_map]
  omega

def secondOutputs {A : Type} [DecidableEq A] (codec : Codec A) (values : Array A) (query : Nat) (expected : A) :
    let size := (WordTemplateMachine.Indexed.argumentWire (comparisonFields codec values query expected)).length
    TM2OutputsInTime secondMachine
      (WordTemplateMachine.Indexed.argumentWire (comparisonFields codec values query expected))
      (some [decide (values[query]? = some expected)]) (25*size+30) := by
  have prepared := WordTemplateMachine.Indexed.outputs secondTemplate (comparisonFields codec values query expected)
  rw [secondTemplate_exact] at prepared
  have compared := WordEqualityMachine.outputs (1::encodeWith codec expected) (decodedOutput codec values[query]?)
  have same : ((1::encodeWith codec expected) = decodedOutput codec values[query]?) ↔ values[query]? = some expected :=
    eq_comm.trans (decodedOutput_some_iff codec values[query]? expected)
  simp only [same] at compared
  have identity : (WordEqualityMachine.packet (1::encodeWith codec expected) (decodedOutput codec values[query]?)).map (Equiv.refl _) =
      WordEqualityMachine.packet (1::encodeWith codec expected) (decodedOutput codec values[query]?) := by simp
  rw [←identity] at compared
  have joined := StackMachineComposition.outputs (WordTemplateMachine.Indexed.machine secondTemplate)
    (WordEqualityMachine.machine SharedReferenceExecution.Alphabet) (Equiv.refl _)
    (WordTemplateMachine.Indexed.argumentWire (comparisonFields codec values query expected))
    (WordEqualityMachine.packet (1::encodeWith codec expected) (decodedOutput codec values[query]?))
    [decide (values[query]? = some expected)] _ _ prepared compared
  have full : (WordTemplateMachine.Indexed.argumentWire (comparisonFields codec values query expected)).length =
      (queryPacket codec values query).length + (encodeWith codec expected).length +
        (decodedOutput codec values[query]?).length + 5 := by
    have lifted := lifted_length (preparedPacket codec values query expected)
    rw [lift_exact] at lifted
    have counted := preparedPacket_length codec values query expected
    have sourceCounted := sourcePacket_length codec values query expected
    omega
  dsimp only
  refine ⟨joined.toEvalsTo,joined.steps_le_m.trans ?_⟩
  simp only [secondTemplate,List.length_cons,List.length_nil]
  have packetSize := WordEqualityMachine.packet_length
    (1::encodeWith codec expected) (decodedOutput codec values[query]?)
  simp only [List.length_cons] at packetSize
  omega

/-- Full original-value equality follows actual chronological lookup and
lossless bit recovery. Absent references and different values are refused by
this same finite machine. All cache bytes are part of its physical input. -/
noncomputable def outputs {A : Type} [DecidableEq A] (codec : Codec A) (values : Array A) (query : Nat) (expected : A) :
    TM2OutputsInTime machine (sourcePacket codec values query expected)
      (some [decide (values[query]? = some expected)])
      (250*((sourcePacket codec values query expected).length+1)^2) := by
  have first := liftedOutputs codec values query expected
  have second := secondOutputs codec values query expected
  have identity : (WordTemplateMachine.Indexed.argumentWire (comparisonFields codec values query expected)).map (Equiv.refl _) =
      WordTemplateMachine.Indexed.argumentWire (comparisonFields codec values query expected) := by simp
  rw [←identity] at second
  have joined := StackMachineComposition.outputs liftedMachine secondMachine (Equiv.refl _)
    (sourcePacket codec values query expected)
    (WordTemplateMachine.Indexed.argumentWire (comparisonFields codec values query expected))
    [decide (values[query]? = some expected)] _ _ first second
  have lifted := lifted_length (preparedPacket codec values query expected)
  rw [lift_exact] at lifted
  have preparedSize := preparedPacket_length codec values query expected
  have stored := decodedOutput_length codec values query
  have inputSize := sourcePacket_length codec values query expected
  refine ⟨joined.toEvalsTo,joined.steps_le_m.trans ?_⟩
  simp only [List.length_map]
  nlinarith

/-- The uniform claim guard realizes actual lookup and full-word equality on
every original encoded cache input, including rejected requests. -/
noncomputable def realization {A : Type} [DecidableEq A] (codec : Codec A) :
    TM2ComputableInPolyTime
      (fun input : Array A × Nat × A => sourcePacket codec input.1 input.2.1 input.2.2)
      (fun accepted : Bool => [accepted])
      (fun input : Array A × Nat × A => decide (input.1[input.2.1]? = some input.2.2)) where
  tm := machine
  inputAlphabet := Equiv.refl (Option SharedReferenceExecution.Alphabet)
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 250 * (Polynomial.X + Polynomial.C 1)^2
  outputsFun input := by
    change TM2OutputsInTime machine ((sourcePacket codec input.1 input.2.1 input.2.2).map id)
      (some ([decide (input.1[input.2.1]? = some input.2.2)].map id))
      ((Polynomial.C 250 * (Polynomial.X + Polynomial.C 1)^2).eval
        (sourcePacket codec input.1 input.2.1 input.2.2).length)
    simp only [List.map_id_fun,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X]
    exact outputs codec input.1 input.2.1 input.2.2

noncomputable def absentOutputs {A : Type} [DecidableEq A] (codec : Codec A) (values : Array A) (query : Nat)
    (expected : A) (absent : values[query]? = none) :
    TM2OutputsInTime machine (sourcePacket codec values query expected) (some [false])
      (250*((sourcePacket codec values query expected).length+1)^2) := by
  simpa [absent] using outputs codec values query expected

noncomputable def differentOutputs {A : Type} [DecidableEq A] (codec : Codec A) (values : Array A) (query : Nat)
    (expected stored : A) (found : values[query]? = some stored) (different : stored ≠ expected) :
    TM2OutputsInTime machine (sourcePacket codec values query expected) (some [false])
      (250*((sourcePacket codec values query expected).length+1)^2) := by
  simpa only [found,Option.some.injEq,decide_eq_false different] using outputs codec values query expected

@[reducible, macro_inline] def retainedMachine := RetainedWordExecution.WithOutput.machine firstMachine
@[reducible, macro_inline] def taggedMachine := RetainedWordExecution.WithOutput.Framed.taggedMachine firstMachine
  (Equiv.refl (Option SharedReferenceExecution.Alphabet)) (Equiv.refl SharedReferenceExecution.Alphabet)
abbrev images := RetainedWordExecution.WithOutput.Framed.untag firstMachine
  (Equiv.refl (Option SharedReferenceExecution.Alphabet)) (Equiv.refl SharedReferenceExecution.Alphabet)
abbrev closing := RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ:=SharedReferenceExecution.Alphabet)



local instance : Fintype (firstMachine.Γ firstMachine.k₀) := inferInstanceAs (Fintype (Option SharedReferenceExecution.Alphabet))
local instance : Fintype (retainedMachine.Γ retainedMachine.k₁) :=
  inferInstanceAs (Fintype (Sum (Option SharedReferenceExecution.Alphabet) SharedReferenceExecution.Alphabet))
local instance : Inhabited (retainedMachine.Γ retainedMachine.k₁) :=
  inferInstanceAs (Inhabited (Sum (Option SharedReferenceExecution.Alphabet) SharedReferenceExecution.Alphabet))
local instance : Inhabited ((WordHomomorphismMachine.machine images).Γ
    (WordHomomorphismMachine.machine images).k₀) :=
  inferInstanceAs (Inhabited (Sum (Option SharedReferenceExecution.Alphabet) SharedReferenceExecution.Alphabet))
local instance : Fintype (taggedMachine.Γ taggedMachine.k₁) := inferInstanceAs (Fintype (Option SharedReferenceExecution.Alphabet))
local instance : Inhabited (taggedMachine.Γ taggedMachine.k₁) := inferInstanceAs (Inhabited (Option SharedReferenceExecution.Alphabet))

/-- The executable interface exposes original instructions and physical
addresses without enumerating the composite finite register space. -/
def firstProgram : firstMachine.Λ → firstMachine.Stmt :=
  StackMachineComposition.Programs.body
    (FirstAlphabet := (WordTemplateMachine.Indexed.machine firstTemplate).Γ)
    (SecondAlphabet := EncodedTable.decodedMachine.Γ)
    .result (some (.inl .input)) (.inl .scanQuery) (0 : SharedReferenceExecution.Alphabet) id
    (WordTemplateMachine.Indexed.program firstTemplate) EncodedTable.decodedProgram

def retainedProgram : retainedMachine.Λ → retainedMachine.Stmt :=
  RetainedWordExecution.WithOutput.Programs.statement (Γ := firstMachine.Γ)
    (some (.inl WordTemplateMachine.Indexed.Stack.input))
    (some (.inr (some (.inr Triples.Recovery.Stack.result)))) none (0 : SharedReferenceExecution.Alphabet)
    (none,(SharedReferenceExecution.initial,Triples.Recovery.initial,none),none)
    (.inl (.emit ⟨0,by decide⟩)) firstProgram

def taggedProgram : taggedMachine.Λ → taggedMachine.Stmt :=
  StackMachineComposition.Programs.body
    (FirstAlphabet := retainedMachine.Γ)
    (SecondAlphabet := (WordHomomorphismMachine.machine images).Γ)
    none .input .read (default : Sum (Option SharedReferenceExecution.Alphabet) SharedReferenceExecution.Alphabet)
    id retainedProgram (WordHomomorphismMachine.program images)

def preparedProgram : preparedMachine.Λ → preparedMachine.Stmt :=
  StackMachineComposition.Programs.body
    (FirstAlphabet := taggedMachine.Γ) (SecondAlphabet := (WordTemplateMachine.machine closing).Γ)
    (some (.inr .result)) .input (.emit ⟨0,by decide⟩) none id
    taggedProgram (WordTemplateMachine.program closing)

def liftedProgram : liftedMachine.Λ → liftedMachine.Stmt :=
  StackMachineComposition.Programs.body
    (FirstAlphabet := preparedMachine.Γ) (SecondAlphabet := (WordHomomorphismMachine.machine liftSymbol).Γ)
    (some (.inr .input)) .input .read none id
    preparedProgram (WordHomomorphismMachine.program liftSymbol)

def secondProgram : secondMachine.Λ → secondMachine.Stmt :=
  StackMachineComposition.Programs.body
    (FirstAlphabet := (WordTemplateMachine.Indexed.machine secondTemplate).Γ)
    (SecondAlphabet := (WordEqualityMachine.machine SharedReferenceExecution.Alphabet).Γ)
    .result .input .scan none id
    (WordTemplateMachine.Indexed.program secondTemplate) (WordEqualityMachine.machine SharedReferenceExecution.Alphabet).m

def program : machine.Λ → machine.Stmt :=
  StackMachineComposition.Programs.body
    (FirstAlphabet := liftedMachine.Γ) (SecondAlphabet := secondMachine.Γ)
    (some (.inr .result)) (some (.inl .input)) (.inl (.emit ⟨0,by decide⟩)) none id
    liftedProgram secondProgram

theorem firstProgram_exact : firstProgram = firstMachine.m := by
  unfold firstProgram
  rw [EncodedTable.decodedProgram_eq]
  exact StackMachineComposition.body_eq (WordTemplateMachine.Indexed.machine firstTemplate)
    EncodedTable.decodedMachine (Equiv.refl _)
theorem retainedProgram_exact : retainedProgram = retainedMachine.m := by
  unfold retainedProgram
  rw [firstProgram_exact]
  simp only [retainedMachine,RetainedWordExecution.WithOutput.machine]
  congr 1
theorem taggedProgram_exact : taggedProgram = taggedMachine.m := by
  unfold taggedProgram
  rw [retainedProgram_exact]
  exact StackMachineComposition.body_eq retainedMachine
    (WordHomomorphismMachine.machine images) (Equiv.refl _)
theorem preparedProgram_exact : preparedProgram = preparedMachine.m := by
  unfold preparedProgram
  rw [taggedProgram_exact]
  exact StackMachineComposition.body_eq taggedMachine
    (WordTemplateMachine.machine closing) (Equiv.refl _)
theorem liftedProgram_exact : liftedProgram = liftedMachine.m := by
  unfold liftedProgram
  rw [preparedProgram_exact]
  exact StackMachineComposition.body_eq preparedMachine
    (WordHomomorphismMachine.machine liftSymbol) (Equiv.refl _)
theorem secondProgram_exact : secondProgram = secondMachine.m :=
  StackMachineComposition.body_eq (WordTemplateMachine.Indexed.machine secondTemplate)
    (WordEqualityMachine.machine SharedReferenceExecution.Alphabet) (Equiv.refl _)
theorem program_exact : program = machine.m := by
  unfold program
  rw [liftedProgram_exact,secondProgram_exact]
  exact StackMachineComposition.body_eq liftedMachine secondMachine (Equiv.refl _)

end Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.EncodedTable.ReferenceCheck
