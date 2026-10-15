import Mettapedia.Languages.HOLLight.MeTTa.Premises
import Mettapedia.Languages.MeTTa.PeTTa.CoreExecution

/-!
# First-match lookup executed by the authored HOL library

The same source helper serves declaration lookup, checked proof references
and simultaneous substitutions. It is proved against the existing List.lookup
operation for every finite table and arbitrary captured values. A captured
value is returned as data, without executing a head it might contain.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.Lookup

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)

def table (entries : List (Atom × Atom)) : Atom :=
  Premises.keys (entries.map fun entry => .expression [.symbol "HOL:Entry", entry.1, entry.2])

def answer : Option Atom → Atom
  | none => .symbol "None"
  | some value => .expression [.symbol "Some", value]

private def equation : SpaceSemantics.Equation :=
  (dataSource.program.equations.filter
    (fun row => row.head == "hol-light:lookup"))[0]'(by decide)

private def cases : SpaceSemantics.Cases :=
  match equation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def consBody : Atom :=
  .expression [.symbol "if", .expression [.symbol "==", .var "name", .var "key"],
    .expression [.symbol "Some", .var "value"],
    .expression [.symbol "hol-light:lookup", .var "key", .var "rest"]]

private def environment (key : Atom) (entries : List (Atom × Atom)) : Subst :=
  [("entries", table entries), ("key", key)]

private def boundEnvironment (key name value : Atom) (rest : List (Atom × Atom)) : Subst :=
  [("rest", table rest), ("value", value), ("name", name)] ++
    environment key ((name, value) :: rest)

private theorem equation_unique :
    program.equations.filter (fun row => row.head == "hol-light:lookup") = [equation] := by rfl

private theorem formals : equation.arguments = [.var "key", .var "entries"] := by decide

private theorem body_shape : equation.body =
    .expression [.symbol "case", .var "entries",
      .expression (cases.map fun row => .expression [row.1, row.2])] := by decide

private theorem cases_shape : cases =
    [(.symbol "HOL:Nil", .symbol "None"),
     (.expression [.symbol "HOL:Cons",
        .expression [.symbol "HOL:Entry", .var "name", .var "value"], .var "rest"], consBody),
     (.var "malformed", .symbol "None")] := by decide

private theorem clause (key : Atom) (entries : List (Atom × Atom)) :
    clauses program "hol-light:lookup" [key, table entries] =
      [.evaluate (environment key entries) equation.body] := by
  rw [clauses_use_only_the_named_equations, equation_unique]
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem nil_selected (key : Atom) :
    SpaceSemantics.selectCase (environment key []) (table []) cases =
      some (environment key [], .symbol "None") := by
  simp [cases_shape, environment, table, Premises.keys,
    SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]

private theorem cons_selected (key name value : Atom) (rest : List (Atom × Atom)) :
    SpaceSemantics.selectCase (environment key ((name, value) :: rest))
      (table ((name, value) :: rest)) cases =
      some (boundEnvironment key name value rest, consBody) := by
  simp [cases_shape, environment, boundEnvironment, table, Premises.keys,
    SpaceSemantics.selectCase, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_returns (key : Atom) (entries : List (Atom × Atom)) (state : State) :
    BoundCalls.CorePath.PureReturns program (environment key entries) state equation.body state
      (answer (entries.lookup key)) := by
  induction entries with
  | nil =>
      rw [body_shape]
      apply BoundCalls.CorePath.case_returns program (environment key []) (environment key []) state state state
        (.var "entries") (table []) (.symbol "None") _ _ cases (read_cases_encoded cases)
      · exact BoundCalls.CorePath.variable_returns program _ state "entries"
      · exact nil_selected key
      · exact BoundCalls.CorePath.symbol_returns program _ state "None"
  | cons entry rest ih =>
      obtain ⟨name, value⟩ := entry
      rw [body_shape]
      apply BoundCalls.CorePath.case_returns program (environment key ((name, value) :: rest))
        (boundEnvironment key name value rest) state state state
        (.var "entries") (table ((name, value) :: rest)) consBody _ _ cases (read_cases_encoded cases)
      · exact BoundCalls.CorePath.variable_returns program _ state "entries"
      · exact cons_selected key name value rest
      · unfold consBody
        apply BoundCalls.CorePath.if_returns program (boundEnvironment key name value rest) state state state
          (.expression [.symbol "==", .var "name", .var "key"])
          (boolean (decide (name = key))) _ _ _
        · apply BoundCalls.CorePath.native_variable_call_returns program (boundEnvironment key name value rest)
            state state "==" ["name", "key"] _ (by decide) (by decide) _ (by decide)
          simp [StdLib.structural_equality, boundEnvironment, environment, applySubst, Subst.lookup, beq_eq_decide]
        · by_cases same : name = key
          · simp only [same, decide_true, boolean, BEq.rfl, ↓reduceIte]
            simpa [answer, List.lookup, same, boundEnvironment, environment, applySubst, Subst.lookup] using
              BoundCalls.CorePath.unary_constructor_returns program (boundEnvironment key name value rest)
                state "Some" "value" (by decide) (by decide)
          · simp only [same, decide_false, boolean]
            apply BoundCalls.CorePath.authored_variable_call_returns program (boundEnvironment key name value rest)
              (environment key rest) state state "hol-light:lookup" ["key", "rest"]
              equation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
            · simpa [boundEnvironment, environment, applySubst, Subst.lookup] using clause key rest
            · simpa [answer, List.lookup, same, Ne.symm same, beq_eq_decide] using ih

/-- Every source transition is certified to be unchanged by captured dispatch,
for arbitrary finite tables and arbitrary opaque captured keys and values. -/
theorem authored_lookup_certificate (bindings : Subst) (state : State) (key : Atom)
    (entries : List (Atom × Atom)) (keyName entriesName : String)
    (capturedKey : applySubst bindings (.var keyName) = key)
    (capturedEntries : applySubst bindings (.var entriesName) = table entries) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:lookup", .var keyName, .var entriesName]) state
      (answer (entries.lookup key)) := by
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings (environment key entries)
    state state "hol-light:lookup" [keyName, entriesName] equation.body _
    (by decide) (by decide) (by decide) _ (body_returns key entries state) (by decide)
  simpa only [List.map_cons, List.map_nil, capturedKey, capturedEntries] using clause key entries

/-- Lookup agrees with first-match table lookup under the original authored
execution relation, retaining the complete source store. -/
theorem authored_lookup_return (bindings : Subst) (state : State) (key : Atom)
    (entries : List (Atom × Atom)) (keyName entriesName : String)
    (capturedKey : applySubst bindings (.var keyName) = key)
    (capturedEntries : applySubst bindings (.var entriesName) = table entries) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:lookup", .var keyName, .var entriesName]) state
      (answer (entries.lookup key)) :=
  (authored_lookup_certificate bindings state key entries keyName entriesName capturedKey capturedEntries).original

/-- The same constructed certificate supplies the captured-call execution.
Opaque table values stay data even when they contain authored function names. -/
theorem authored_lookup_bound_return (bindings : Subst) (state : State) (key : Atom)
    (entries : List (Atom × Atom)) (keyName entriesName : String)
    (capturedKey : applySubst bindings (.var keyName) = key)
    (capturedEntries : applySubst bindings (.var entriesName) = table entries) :
    BoundCalls.PureReturns program bindings state
      (.expression [.symbol "hol-light:lookup", .var keyName, .var entriesName]) state
      (answer (entries.lookup key)) :=
  (authored_lookup_certificate bindings state key entries keyName entriesName capturedKey capturedEntries).extended

/-- An earlier entry wins even when the same key occurs again. -/
theorem earlier_entry_wins (key first later : Atom) :
    ([(key, first), (key, later)] : List (Atom × Atom)).lookup key = some first := by
  simp [List.lookup]

end Mettapedia.Languages.HOLLight.MeTTa.Lookup
