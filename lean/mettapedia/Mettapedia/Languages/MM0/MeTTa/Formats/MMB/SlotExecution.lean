import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.TheoremExecution
import Mettapedia.Languages.MeTTa.PeTTa.StdLibCalls

/-!
# Execution of the original binary source slot update

The original `set-at` operation changes an existing physical slot, preserves
every other slot and refuses an unavailable index. Its replacement is inert
data. Decoder reservation and structural matching consume this same operation.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MM0.MeTTa.MMBSlotExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Store (natural)
open ListAccess (listValue optionValue)

abbrev program := MMBTheoremExecution.program

/-- The existing list update, exposed only when the physical slot exists. -/
def setResult (items : List Atom) (index : Nat) (value : Atom) : Atom :=
  optionValue ((items[index]?).map fun _ => listValue (items.set index value))

private def equation : SpaceSemantics.Equation :=
  ((MMBExecution.binarySource.program.equations.filter (·.head == "mm0:mmb:set-at")).head?).getD
    ⟨"", [], .symbol "None"⟩
private def casesOf (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def cases := casesOf equation.body
private def consBody := (cases[0]'(by decide)).2
private def hereBody := match consBody with | .expression [_, _, here, _] => here | _ => .symbol "None"
private def laterBody := match consBody with | .expression [_, _, _, later] => later | _ => .symbol "None"
private def laterCases := casesOf laterBody
private def rebuiltBody := (laterCases[0]'(by decide)).2
private def environment (items : List Atom) (index : Nat) (value : Atom) : Subst :=
  [("value", value), ("at", natural index), ("items", .expression items)]
private def bound (first : Atom) (rest : List Atom) (index : Nat) (value : Atom) : Subst :=
  ("rest", .expression rest) :: ("first", first) :: environment (first :: rest) index value

private theorem unique : program.equations.filter (·.head == "mm0:mmb:set-at") = [equation] := by
  decide +kernel
private theorem formals : equation.arguments =
    [.expression [.symbol "MM0:L", .var "items"], .var "at", .var "value"] := by decide
private theorem shape : equation.body = .expression [.symbol "case", .var "items",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem cases_shape : cases =
    [(.expression [.symbol "cons", .var "first", .var "rest"], consBody), (.var "bad", .symbol "None")] := by decide
private theorem cons_shape : consBody = .expression [.symbol "if",
    .expression [.symbol "==", .var "at", natural 0], hereBody, laterBody] := by decide
private theorem here_shape : hereBody = .expression [.symbol "let", .var "result",
    .expression [.symbol "mm0:list-cons", .var "value", .expression [.symbol "MM0:L", .var "rest"]],
    .expression [.symbol "Some", .var "result"]] := by decide
private theorem later_shape : laterBody = .expression [.symbol "case",
    .expression [.symbol "mm0:mmb:set-at", .expression [.symbol "MM0:L", .var "rest"],
      .expression [.symbol "-", .var "at", natural 1], .var "value"],
    .expression (laterCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem later_cases_shape : laterCases =
    [(.expression [.symbol "Some", .var "tail"], rebuiltBody), (.var "bad", .symbol "None")] := by decide
private theorem rebuilt_shape : rebuiltBody = .expression [.symbol "let", .var "result",
    .expression [.symbol "mm0:list-cons", .var "first", .var "tail"],
    .expression [.symbol "Some", .var "result"]] := by decide
private theorem clause (items : List Atom) (index : Nat) (value : Atom) :
    clauses program "mm0:mmb:set-at" [listValue items, natural index, value] =
      [.evaluate (environment items index value) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, environment, listValue, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem recursive_from_body (state : State) (first : Atom) (rest : List Atom) (index : Nat) (value : Atom)
    (body : PureReturns program (environment rest index value) state equation.body state (setResult rest index value)) :
    PureReturns program (bound first rest (index + 1) value) state
      (.expression [.symbol "mm0:mmb:set-at", .expression [.symbol "MM0:L", .var "rest"],
        .expression [.symbol "-", .var "at", natural 1], .var "value"]) state (setResult rest index value) := by
  let bindings := bound first rest (index + 1) value
  apply call_returns program bindings state state "mm0:mmb:set-at" _ _ (by decide +kernel) _ (by decide)
  apply raw_argument_answers program bindings state state "mm0:mmb:set-at"
    (.expression [.symbol "MM0:L", .var "rest"]) _ [] 0 [setResult rest index value] (by decide +kernel)
  apply evaluated_argument_returns program bindings state state state (.function "mm0:mmb:set-at")
    (.expression [.symbol "-", .var "at", natural 1]) (natural index) _ _ _ 1 (by decide +kernel)
  · apply native_binary_call_returns program bindings state state state state "-" (.var "at") (natural 1)
      (natural (index + 1)) (natural 1) (natural index)
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
    · exact variable_returns program bindings state "at"
    · exact grounded_returns program bindings state (.int 1)
    · simp [StdLib.integer_subtraction, natural]
  · apply raw_argument_answers program bindings state state "mm0:mmb:set-at" (.var "value") [] _ 2
      [setResult rest index value] (by decide +kernel)
    simpa [bindings, bound, environment, applySubst, applySubst.applySubstList, Subst.lookup, listValue] using
      authored_function_arguments_return program bindings (environment rest index value) state state "mm0:mmb:set-at"
        [listValue rest, natural index, value] 3 equation.body (setResult rest index value)
        (by decide +kernel) (by decide) (clause rest index value) body

private theorem cons_returns (state : State) (first : Atom) (rest : List Atom) (index : Nat) (value : Atom)
    (body : PureReturns program (bound first rest index value) state consBody state (setResult (first :: rest) index value)) :
    PureReturns program (environment (first :: rest) index value) state equation.body state
      (setResult (first :: rest) index value) := by
  rw [shape]
  apply case_returns program (environment (first :: rest) index value) (bound first rest index value)
    state state state (.var "items") (.expression (first :: rest)) consBody _ _ cases (read_cases_encoded cases)
  · exact variable_returns program _ state "items"
  · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      matchAtom, Subst.lookup, bound, environment]
  · exact body

private theorem body_returns (state : State) (items : List Atom) (index : Nat) (value : Atom) :
    PureReturns program (environment items index value) state equation.body state (setResult items index value) := by
  induction items generalizing index with
  | nil =>
      rw [shape]
      apply case_returns program (environment [] index value) (("bad", .expression []) :: environment [] index value)
        state state state (.var "items") (.expression []) (.symbol "None") _ _ cases (read_cases_encoded cases)
      · exact variable_returns program _ state "items"
      · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          matchAtom, Subst.lookup, environment]
      · simpa [setResult, optionValue] using symbol_returns program _ state "None"
  | cons first rest ih =>
      apply cons_returns
      cases index with
      | zero =>
          let bindings := bound first rest 0 value
          let after := ("result", listValue (value :: rest)) :: bindings
          rw [cons_shape]
          apply if_returns program bindings state state state _ (boolean true) _ _ _
          · apply native_binary_call_returns program bindings state state state state "==" (.var "at") (natural 0)
              (natural 0) (natural 0) (boolean true)
              (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
            · exact variable_returns program bindings state "at"
            · exact grounded_returns program bindings state (.int 0)
            · simp [StdLib.structural_equality]
          · simp only [boolean]
            rw [here_shape]
            apply let_returns program bindings after state state state (.var "result") _ _ (listValue (value :: rest)) _
            · let prior : Subst := [("head", value), ("tail", listValue rest)]
              have returned := MMBProofRunExecution.checker_returns (by decide +kernel)
                (ListAccess.cons_captured_returns prior state value rest "head" "tail" rfl rfl)
              apply captured_call_returns program prior bindings state state "mm0:list-cons"
                [.var "head", .var "tail"] [.var "value", .expression [.symbol "MM0:L", .var "rest"]] _
                (by decide +kernel) (by decide) _ _ _ returned
              · intro offset argument found
                have bounded : offset < 2 := by
                  have inside := (getElem?_eq_some_iff.mp found).choose
                  simpa using inside
                interval_cases offset <;> simp at found <;> subst argument <;> right <;> rfl
              · intro offset argument found
                have bounded : offset < 2 := by
                  have inside := (getElem?_eq_some_iff.mp found).choose
                  simpa using inside
                interval_cases offset
                · simp at found; subst argument; right; rfl
                · left; decide +kernel
              · simp [prior, bindings, bound, environment, listValue, applySubst, applySubst.applySubstList, Subst.lookup]
            · simp [SpaceSemantics.matchValue, matchAtom, after, bindings, bound, environment, Subst.lookup]
            · simpa [setResult, optionValue, after, applySubst, Subst.lookup] using
                unary_constructor_returns program after state "Some" "result" (by decide +kernel) (by decide)
      | succ index =>
          let bindings := bound first rest (index + 1) value
          rw [cons_shape]
          apply if_returns program bindings state state state _ (boolean false) _ _ _
          · apply native_binary_call_returns program bindings state state state state "==" (.var "at") (natural 0)
              (natural (index + 1)) (natural 0) (boolean false)
              (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
            · exact variable_returns program bindings state "at"
            · exact grounded_returns program bindings state (.int 0)
            · rw [StdLib.structural_equality, beq_eq_false_iff_ne.mpr (by
                intro same
                have countSame := congrArg MMUResolution.decodeNatural same
                simp [MMUResolution.decodeNatural, natural] at countSame)]
          · simp only [boolean]
            rw [later_shape]
            cases found : rest[index]? with
            | none =>
                apply case_returns program bindings (("bad", .symbol "None") :: bindings) state state state _
                  (.symbol "None") (.symbol "None") _ _ laterCases (read_cases_encoded laterCases)
                · simpa [setResult, found, optionValue] using recursive_from_body state first rest index value (ih index)
                · simp [later_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                    matchAtom, Subst.lookup, bindings, bound, environment]
                · simpa [setResult, found, optionValue] using symbol_returns program _ state "None"
            | some old =>
                let updated := rest.set index value
                let tailed := ("tail", listValue updated) :: bindings
                let after := ("result", listValue (first :: updated)) :: tailed
                apply case_returns program bindings tailed state state state _ (optionValue (some (listValue updated)))
                  rebuiltBody _ _ laterCases (read_cases_encoded laterCases)
                · simpa [setResult, found, optionValue, updated] using recursive_from_body state first rest index value (ih index)
                · simp [later_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, tailed, bindings, bound, environment, optionValue]
                · rw [rebuilt_shape]
                  apply let_returns program tailed after state state state (.var "result") _ _ (listValue (first :: updated)) _
                  · apply MMBProofRunExecution.checker_returns (by decide +kernel)
                    apply ListAccess.cons_captured_returns tailed state first updated "first" "tail"
                    · simp [tailed, bindings, bound, environment, applySubst, Subst.lookup]
                    · rfl
                  · simp [SpaceSemantics.matchValue, matchAtom, after, tailed, bindings, bound, environment, Subst.lookup]
                  · simpa [setResult, found, optionValue, updated, after, applySubst, Subst.lookup] using
                      unary_constructor_returns program after state "Some" "result" (by decide +kernel) (by decide)

/-- The original source updates exactly one existing slot, including inert
replacement data, or returns its explicit out-of-range refusal. -/
theorem set_at_returns (bindings : Subst) (state : State) (items : List Atom) (index : Nat) (value : Atom)
    (itemsName indexName valueName : String)
    (itemsCaptured : applySubst bindings (.var itemsName) = listValue items)
    (indexCaptured : applySubst bindings (.var indexName) = natural index)
    (valueCaptured : applySubst bindings (.var valueName) = value) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmb:set-at", .var itemsName, .var indexName, .var valueName]) state
      (setResult items index value) := by
  apply authored_variable_call_returns program bindings (environment items index value) state state
    "mm0:mmb:set-at" [itemsName, indexName, valueName] equation.body _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (body_returns state items index value) (by decide)
  simpa [itemsCaptured, indexCaptured, valueCaptured] using clause items index value

end Mettapedia.Languages.MM0.MeTTa.MMBSlotExecution
