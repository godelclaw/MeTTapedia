import Mettapedia.Data.List.StableTopK
import Mettapedia.Languages.MeTTa.PeTTa.ProgramQuotation
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgeEval
import Mettapedia.Languages.MeTTa.PeTTa.StdLibCalls

/-! # Execution of the authored stable integer ranking program

The source file is read into the existing MeTTa evaluator's program type.
Payloads remain captured data, including atoms that would be executable in a
code position. These are source-semantics theorems; the native runtime is a
separate implementation qualified against the same source.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.StableTopK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Eval BridgeKit MeTTaIL.WireKit
open scoped ProgramQuotation

structure Row where
  index : Nat
  score : Int
  payload : Atom

def row (value : Row) : Atom :=
  .expression [.grounded (.int value.index), .grounded (.int value.score), value.payload]

def rows : List Row → Atom
  | [] => .symbol "RankNil"
  | first :: rest => apply "RankCons" [row first, rows rest]

def source : ProgramQuotation.QuotedProgram := petta_source_file%
  "../../../../../../../metta/math/stable_top_k.metta"
  sha256 "2af3805a857a4b83005228939456dc37d7a26e338c16e2b1a1db6d80b5a56db0"

def library : Library := ⟨⟨[], [], [], [], []⟩, source.program, ["rank:"]⟩

theorem library_checked : library.check = true := by decide +kernel

private theorem row_score (program : SpaceSemantics.Program) (caller : Subst)
    (state : Effects.State) (code : Atom) (value : Row)
    (computed : PureReturns program caller state code state (row value)) :
    PureReturns program caller state (apply "index-atom" [code, number 1]) state
      (.grounded (.int value.score)) := by
  apply native_binary_call_returns program caller state state state state "index-atom"
    code (number 1) (row value) (number 1) _ (by decide) (by decide)
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument])
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument]) computed
    (number_returns _ _ _ _) _ (by decide)
  rfl

private theorem row_index (program : SpaceSemantics.Program) (caller : Subst)
    (state : Effects.State) (code : Atom) (value : Row)
    (computed : PureReturns program caller state code state (row value)) :
    PureReturns program caller state (apply "index-atom" [code, number 0]) state
      (number value.index) := by
  apply native_binary_call_returns program caller state state state state "index-atom"
    code (number 0) (row value) (number 0) _ (by decide) (by decide)
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument])
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument]) computed
    (number_returns _ _ _ _) _ (by decide)
  rfl

private theorem integer_ge (program : SpaceSemantics.Program) (caller : Subst)
    (state : Effects.State) (left right : Atom) (a b : Int)
    (hl : PureReturns program caller state left state (.grounded (.int a)))
    (hr : PureReturns program caller state right state (.grounded (.int b))) :
    PureReturns program caller state (apply ">=" [left, right]) state
      (Effects.boolean (decide (a ≥ b))) := by
  apply native_binary_call_returns program caller state state state state ">="
    left right _ _ _ (by decide) (by decide)
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument])
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument]) hl hr _ (by decide)
  rfl

syntax "rank_eval" (" [" term,* "]")? : tactic
macro_rules
  | `(tactic| rank_eval $[[$facts,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    `(tactic|
      (try simp only [Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil,
         Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil.applySubstList_nil]
       metta_eval [$facts,*] with library_checked unfolding [rows, row,
         List.StableTopK.insert, List.StableTopK.sort, List.StableTopK.eligible,
         List.StableTopK.select, List.StableTopK.bounded, List.filter_cons, List.take,
         Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil,
         Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil.applySubstList_nil]
       all_goals first
         | (apply pure_let_returns _ _ _ _ _ _ _ _ (by rfl)
            rank_eval [$facts,*]
            rank_eval [$facts,*])
         | (apply pure_if_returns
            rank_eval [$facts,*]
            split <;> simp_all only [decide_true, decide_false, Bool.false_eq_true,
              ite_true, ite_false, List.StableTopK.insert, rows]
            all_goals rank_eval [$facts,*])
         | (apply row_score; rank_eval [$facts,*])
         | (apply row_index; rank_eval [$facts,*])
         | ((apply integer_ge) <;> rank_eval [$facts,*])
         | (split <;> rank_eval [$facts,*])))

theorem insert_returns (state : Effects.State) (value : Row) (values : List Row) :
    PureReturns library.runtime [] state
      (apply "rank:insert" [row value, rows values]) state
      (rows (List.StableTopK.insert Row.score value values)) := by
  induction values with
  | nil =>
    metta_call library_checked
    rank_eval
  | cons first rest ih =>
    metta_call library_checked
    simp only [Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]
    metta_eval with library_checked unfolding [rows, row]
    apply pure_let_returns _ _ _ _ _ _ _ _ (by rfl)
    · apply row_score _ _ _ _ value
      exact bound_returns _ _ _ (by rfl)
    · apply pure_let_returns _ _ _ _ _ _ _ _ (by rfl)
      · apply row_score _ _ _ _ first
        exact bound_returns _ _ _ (by rfl)
      · apply pure_if_returns
        · apply integer_ge _ _ _ _ _ value.score first.score
          · exact bound_returns _ _ _ (by rfl)
          · exact bound_returns _ _ _ (by rfl)
        · by_cases order : value.score ≥ first.score
          · simp only [order, decide_true, ite_true, List.StableTopK.insert, rows]
            rank_eval
          · simp only [order, decide_false, Bool.false_eq_true, ite_false,
              List.StableTopK.insert, rows]
            rank_eval [ih]

theorem sort_returns (state : Effects.State) (values : List Row) :
    PureReturns library.runtime [] state (apply "rank:sort" [rows values]) state
      (rows (List.StableTopK.sort Row.score values)) := by
  induction values with
  | nil => metta_call library_checked; rank_eval
  | cons first rest ih =>
    metta_call library_checked
    rank_eval [ih, insert_returns state first (List.StableTopK.sort Row.score rest)]

theorem eligible_returns (state : Effects.State) (before : Nat) (values : List Row) :
    PureReturns library.runtime [] state
      (apply "rank:eligible" [number before, rows values]) state
      (rows (List.StableTopK.eligible Row.index before values)) := by
  induction values with
  | nil => metta_call library_checked; rank_eval
  | cons first rest ih =>
    metta_call library_checked
    simp only [Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]
    metta_eval with library_checked unfolding [rows, row]
    apply pure_let_returns _ _ _ _ _ _ _ _ (by rfl)
    · apply row_index _ _ _ _ first
      exact bound_returns _ _ _ (by rfl)
    · rank_eval [ih]

theorem take_returns (state : Effects.State) (budget : Nat) (values : List Row) :
    PureReturns library.runtime [] state
      (apply "rank:take" [number budget, rows values]) state (rows (values.take budget)) := by
  induction budget generalizing values with
  | zero => metta_call library_checked; rank_eval
  | succ budget ih =>
    cases values with
    | nil => metta_call library_checked; rank_eval
    | cons first rest => metta_call library_checked; rank_eval [ih rest]

theorem bounded_returns (state : Effects.State) (budget : Nat) (values : List Row) :
    PureReturns library.runtime [] state
      (apply "rank:bounded" [number budget, rows values]) state
      (rows (List.StableTopK.bounded Row.score budget values)) := by
  cases budget with
  | zero => metta_call library_checked; rank_eval
  | succ budget =>
    induction values with
    | nil => metta_call library_checked; rank_eval
    | cons first rest ih =>
      metta_call library_checked
      rank_eval [ih,
        insert_returns state first (List.StableTopK.bounded Row.score (budget + 1) rest),
        take_returns state (budget + 1)
          (List.StableTopK.insert Row.score first
            (List.StableTopK.bounded Row.score (budget + 1) rest))]

/-- Every input list and every finite budget: no effects, no lost payloads,
and the exact ordered result of the mathematical algorithm. -/
theorem select_returns (state : Effects.State) (before budget : Nat) (values : List Row) :
    PureReturns library.runtime [] state
      (apply "rank:select" [number before, number budget, rows values]) state
      (rows (List.StableTopK.select Row.score Row.index before budget values)) := by
  metta_call library_checked
  have boundedResult := bounded_returns state budget
    (List.StableTopK.eligible Row.index before values)
  rw [List.StableTopK.bounded_eq_take_sort] at boundedResult
  rank_eval [eligible_returns state before values,
    boundedResult]

theorem row_injective : Function.Injective row := by
  intro first second equal
  cases first
  cases second
  simpa [row, Int.ofNat_inj] using equal

theorem rows_injective : Function.Injective rows := by
  intro first
  induction first with
  | nil => intro second equal; cases second <;> simp_all [rows, apply]
  | cons first rest ih =>
    intro second equal
    cases second with
    | nil => simp [rows, apply] at equal
    | cons other tail =>
      have parts : row first = row other ∧ rows rest = rows tail := by
        simpa [rows, apply] using equal
      rw [row_injective parts.1, ih parts.2]

/-- All completed runs, rather than one selected reduction path. The
existing evaluator determinism theorem supplies the converse. -/
theorem completed_iff (state after : Effects.State) (before budget : Nat)
    (values : List Row) (answers input output : List Atom) :
    (∃ fuel, run library.runtime fuel
      { state, control := .evaluate [] (apply "rank:select"
          [number before, number budget, rows values]) } =
        .complete after answers input output) ↔
    after = state ∧
      answers = [rows (List.StableTopK.select Row.score Row.index before budget values)] ∧
      input = [] ∧ output = [] :=
  pure_returns_completed_iff _ _ _ _ _ _ (select_returns state before budget values) _ _ _ _

theorem completed_result_iff (state : Effects.State) (before budget : Nat)
    (values result : List Row) :
    (∃ fuel, run library.runtime fuel
      { state, control := .evaluate [] (apply "rank:select"
          [number before, number budget, rows values]) } =
        .complete state [rows result] [] []) ↔
      result = List.StableTopK.select Row.score Row.index before budget values := by
  rw [completed_iff]
  simp only [true_and, and_true, List.singleton_inj, rows_injective.eq_iff]

theorem completed_contract (state : Effects.State) (before budget : Nat)
    (values result : List Row)
    (finished : ∃ fuel, run library.runtime fuel
      { state, control := .evaluate [] (apply "rank:select"
          [number before, number budget, rows values]) } =
        .complete state [rows result] [] []) :
    result.length ≤ budget ∧
    (∀ value ∈ result, value ∈ values ∧ value.index < before) ∧
    result.Pairwise (fun x y => x.score ≥ y.score) ∧
    (∀ key, List.Sublist (result.filter (fun x => decide (x.score = key)))
      ((List.StableTopK.eligible Row.index before values).filter
        (fun x => decide (x.score = key)))) := by
  rw [(completed_result_iff state before budget values result).mp finished]
  exact ⟨List.StableTopK.length_select_le _ _ _ _ _,
    fun _ member => List.StableTopK.selected_source member,
    List.StableTopK.selected_ordered _ _ _ _ _,
    fun key => List.StableTopK.selected_stable _ _ _ _ _ key⟩

theorem zero_budget_rejects_nonempty (state : Effects.State) (before : Nat)
    (values : List Row) (first : Row) (rest : List Row) :
    ¬ ∃ fuel, run library.runtime fuel
      { state, control := .evaluate [] (apply "rank:select"
          [number before, number 0, rows values]) } =
        .complete state [rows (first :: rest)] [] [] := by
  rw [completed_result_iff]
  simp [List.StableTopK.select]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.StableTopK
