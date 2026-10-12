import Mettapedia.Languages.HOLLight.MeTTa.Representation

/-!
# Executed opening of a checked positional binder

The actual source traversal replaces the final active binder by a closed
checked term. Contextual annotations and free occurrences are retained.
Checked input excludes indices beyond the discharged binder, so the source
decrement branch and the shared canonical operation agree on this fragment.
Their behavior on malformed open data is not identified.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.BinderOpening

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open Eval
open Effects (State boolean)
open Representation (termAtom)
open TypeSubstitution (typeAtom nameAtom)

private def equation : SpaceSemantics.Equation :=
  (syntaxSource.program.equations.filter (fun row => row.head == "hol-light:open-binder"))[0]'(by decide)
private def cases : SpaceSemantics.Cases :=
  match equation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def greaterBody : Atom := .expression [.symbol "if",
  .expression [.symbol ">", .var "index", .var "depth"],
  .expression [.symbol "HOL:Bound", .expression [.symbol "-", .var "index", .grounded (.int 1)],
    .var "type"], .var "term"]
private def boundBody : Atom := .expression [.symbol "if",
  .expression [.symbol "==", .var "index", .var "depth"], .var "replacement", greaterBody]
private def increment : Atom := .expression [.symbol "+", .var "depth", .grounded (.int 1)]
private def lambdaBody : Atom := .expression [.symbol "HOL:Lam", .var "type",
  .expression [.symbol "hol-light:open-binder", .var "replacement", increment, .var "body"]]
private def applicationBody : Atom := .expression [.symbol "HOL:App",
  .expression [.symbol "hol-light:open-binder", .var "replacement", .var "depth", .var "function"],
  .expression [.symbol "hol-light:open-binder", .var "replacement", .var "depth", .var "argument"]]
private def environment (operators : TypeOp → Atom) (constants : Const → Atom)
    (replacement : CanonicalTerm) (positions : List Ty) (term : DBTerm) : Subst :=
  [("term", termAtom operators constants (positions ++ [replacement.ty]) term),
   ("depth", .grounded (.int positions.length)),
   ("replacement", termAtom operators constants [] replacement.term)]
private theorem shape : equation.body = .expression [.symbol "case", .var "term",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem cases_shape : cases =
    [(.expression [.symbol "HOL:Free", .var "name", .var "type"], .var "term"),
     (.expression [.symbol "HOL:Bound", .var "index", .var "type"], boundBody),
     (.expression [.symbol "HOL:C", .var "identity", .var "type"], .var "term"),
     (.expression [.symbol "HOL:Lam", .var "type", .var "body"], lambdaBody),
     (.expression [.symbol "HOL:App", .var "function", .var "argument"], applicationBody),
     (.var "malformed", .symbol "None")] := by decide
private theorem clause (operators : TypeOp → Atom) (constants : Const → Atom)
    (replacement : CanonicalTerm) (positions : List Ty) (term : DBTerm) :
    clauses program "hol-light:open-binder" [termAtom operators constants [] replacement.term,
      .grounded (.int positions.length), termAtom operators constants (positions ++ [replacement.ty]) term] =
      [.evaluate (environment operators constants replacement positions term) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:open-binder") = [equation] := by rfl
  rw [unique]
  have formals : equation.arguments = [.var "replacement", .var "depth", .var "term"] := by decide
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem computed_call_return (operators : TypeOp → Atom) (constants : Const → Atom)
    (replacement : CanonicalTerm) (positions : List Ty) (term : DBTerm)
    (bindings : Subst) (state : State) (replacementExpr depthExpr termExpr answer : Atom)
    (replacementReturned : PureReturns program bindings state replacementExpr state (termAtom operators constants [] replacement.term))
    (depthReturned : PureReturns program bindings state depthExpr state (.grounded (.int positions.length)))
    (termReturned : PureReturns program bindings state termExpr state
      (termAtom operators constants (positions ++ [replacement.ty]) term))
    (bodyReturned : PureReturns program (environment operators constants replacement positions term) state equation.body state answer) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:open-binder", replacementExpr, depthExpr, termExpr]) state answer := by
  apply call_returns program bindings state state "hol-light:open-binder" _ _ (by decide) _ (by decide)
  apply evaluated_argument_returns program bindings state state state (.function "hol-light:open-binder")
    replacementExpr _ _ [depthExpr, termExpr] [] 0 (by decide) replacementReturned
  apply evaluated_argument_returns program bindings state state state (.function "hol-light:open-binder")
    depthExpr _ _ [termExpr] [_] 1 (by decide) depthReturned
  apply evaluated_argument_returns program bindings state state state (.function "hol-light:open-binder")
    termExpr _ _ [] [_, _] 2 (by decide) termReturned
  exact authored_function_arguments_return program bindings (environment operators constants replacement positions term)
    state state "hol-light:open-binder" [_, _, _] 3 equation.body _
    (by decide) (by decide) (clause operators constants replacement positions term) bodyReturned

private theorem body_returns (operators : TypeOp → Atom) (constants : Const → Atom)
    (replacement : CanonicalTerm) (term : DBTerm) (positions : List Ty) (type : Ty)
    (typed : term.inferType (positions ++ [replacement.ty]) = some type) (state : State) :
    PureReturns program (environment operators constants replacement positions term) state equation.body state
      (termAtom operators constants positions (DBTerm.instantiateAt replacement.term positions.length term)) := by
  induction term generalizing positions type with
  | free sourceVar =>
      let before := environment operators constants replacement positions (.free sourceVar)
      let bound := [("type", typeAtom operators sourceVar.ty), ("name", nameAtom sourceVar.name)] ++ before
      rw [shape]
      apply case_returns program before bound state state state (.var "term")
        (termAtom operators constants (positions ++ [replacement.ty]) (.free sourceVar)) (.var "term")
        _ _ cases (read_cases_encoded cases)
      · exact variable_returns program before state "term"
      · simp [cases_shape, bound, before, environment, termAtom, Representation.variableAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · simpa [DBTerm.instantiateAt, termAtom, bound, before, environment, applySubst, Subst.lookup] using
          variable_returns program bound state "term"
  | const constant annotation =>
      let before := environment operators constants replacement positions (.const constant annotation)
      let bound := [("type", typeAtom operators annotation), ("identity", constants constant)] ++ before
      rw [shape]
      apply case_returns program before bound state state state (.var "term")
        (termAtom operators constants (positions ++ [replacement.ty]) (.const constant annotation)) (.var "term")
        _ _ cases (read_cases_encoded cases)
      · exact variable_returns program before state "term"
      · simp [cases_shape, bound, before, environment, termAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · simpa [DBTerm.instantiateAt, termAtom, bound, before, environment, applySubst, Subst.lookup] using
          variable_returns program bound state "term"
  | bound index =>
      simp only [DBTerm.inferType] at typed
      have inRange : index < (positions ++ [replacement.ty]).length := (List.getElem?_eq_some_iff.mp typed).1
      let before := environment operators constants replacement positions (.bound index)
      let bound := [("type", (((positions ++ [replacement.ty])[index]?).map (typeAtom operators)).getD (.symbol "None")),
        ("index", Atom.grounded (.int index))] ++ before
      rw [shape]
      apply case_returns program before bound state state state (.var "term")
        (termAtom operators constants (positions ++ [replacement.ty]) (.bound index)) boundBody
        _ _ cases (read_cases_encoded cases)
      · exact variable_returns program before state "term"
      · simp [cases_shape, bound, before, environment, termAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · unfold boundBody
        by_cases target : index = positions.length
        · subst index
          apply if_returns program bound state state state _ (boolean true) _ _ _
          · apply native_variable_call_returns program bound state state "==" ["index", "depth"] _
              (by decide) (by decide) _ (by decide)
            simp [StdLib.structural_equality, bound, before, environment, applySubst, Subst.lookup, boolean]
          · have represented : termAtom operators constants positions replacement.term =
                termAtom operators constants [] replacement.term := by
              simpa using Representation.termAtom_append_context operators constants replacement.checked positions
            simpa [boolean, DBTerm.instantiateAt, represented, bound, before, environment, applySubst, Subst.lookup] using
              variable_returns program bound state "replacement"
        · have earlier : index < positions.length := by simp only [List.length_append, List.length_singleton] at inRange; omega
          apply if_returns program bound state state state _ (boolean false) _ _ _
          · apply native_variable_call_returns program bound state state "==" ["index", "depth"] _
              (by decide) (by decide) _ (by decide)
            have different : (index : Int) ≠ positions.length := by omega
            simp [StdLib.structural_equality, bound, before, environment, applySubst, Subst.lookup, boolean, different]
          · unfold greaterBody
            apply if_returns program bound state state state _ (boolean false) _ _ _
            · apply native_variable_call_returns program bound state state ">" ["index", "depth"] _
                (by decide) (by decide) _ (by decide)
              have notGreater : ¬ (positions.length : Int) < index := by omega
              simp [StdLib.greater_comparison, bound, before, environment, applySubst, Subst.lookup, boolean, notGreater]
            · simpa [boolean, DBTerm.instantiateAt, target, termAtom, List.getElem?_append_left earlier,
                bound, before, environment, applySubst, Subst.lookup] using variable_returns program bound state "term"
  | abs domain body ih =>
      obtain ⟨codomain, bodyTyped, typeEqual⟩ :
          ∃ codomain, body.inferType (domain :: (positions ++ [replacement.ty])) = some codomain ∧
            Ty.function domain codomain = type := by
        cases checked : body.inferType (domain :: (positions ++ [replacement.ty])) <;>
          simp [DBTerm.inferType, checked] at typed
        exact ⟨_, rfl, typed⟩
      let before := environment operators constants replacement positions (.abs domain body)
      let bound := [("body", termAtom operators constants (domain :: (positions ++ [replacement.ty])) body),
        ("type", typeAtom operators domain)] ++ before
      rw [shape]
      apply case_returns program before bound state state state (.var "term")
        (termAtom operators constants (positions ++ [replacement.ty]) (.abs domain body)) lambdaBody
        _ _ cases (read_cases_encoded cases)
      · exact variable_returns program before state "term"
      · simp [cases_shape, bound, before, environment, termAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · simp only [DBTerm.instantiateAt, termAtom]
        unfold lambdaBody
        apply binary_constructor_returns program bound state state state "HOL:Lam" (.var "type") _
          (typeAtom operators domain) _ (by decide) (by decide)
        · simpa [bound, applySubst, Subst.lookup] using variable_returns program bound state "type"
        · apply computed_call_return operators constants replacement (domain :: positions) body bound state
            (.var "replacement") increment (.var "body") _ _ _ _
            (ih (domain :: positions) codomain (by simpa using bodyTyped))
          · simpa [bound, before, environment, applySubst, Subst.lookup] using variable_returns program bound state "replacement"
          · unfold increment
            apply native_binary_call_returns program bound state state state state "+" (.var "depth") (.grounded (.int 1))
              (.grounded (.int positions.length)) (.grounded (.int 1))
              (.grounded (.int (domain :: positions).length)) (by decide) (by decide) (by decide) (by decide) _
              (grounded_returns program bound state _) _ (by decide)
            · simpa [bound, before, environment, applySubst, Subst.lookup] using variable_returns program bound state "depth"
            · simp [StdLib.integer_addition]
          · simpa [bound, applySubst, Subst.lookup] using variable_returns program bound state "body"
  | app function argument functionIH argumentIH =>
      obtain ⟨functionType, argumentType, functionTyped, argumentTyped⟩ :
          ∃ functionType argumentType, function.inferType (positions ++ [replacement.ty]) = some functionType ∧
            argument.inferType (positions ++ [replacement.ty]) = some argumentType := by
        cases hf : function.inferType (positions ++ [replacement.ty]) <;>
          cases ha : argument.inferType (positions ++ [replacement.ty]) <;>
          simp [DBTerm.inferType, hf, ha] at typed
        exact ⟨_, _, rfl, rfl⟩
      let before := environment operators constants replacement positions (.app function argument)
      let bound := [("argument", termAtom operators constants (positions ++ [replacement.ty]) argument),
        ("function", termAtom operators constants (positions ++ [replacement.ty]) function)] ++ before
      rw [shape]
      apply case_returns program before bound state state state (.var "term")
        (termAtom operators constants (positions ++ [replacement.ty]) (.app function argument)) applicationBody
        _ _ cases (read_cases_encoded cases)
      · exact variable_returns program before state "term"
      · simp [cases_shape, bound, before, environment, termAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · simp only [DBTerm.instantiateAt, termAtom]
        unfold applicationBody
        apply binary_constructor_returns program bound state state state "HOL:App" _ _ _ _ (by decide) (by decide)
        · apply computed_call_return operators constants replacement positions function bound state
            (.var "replacement") (.var "depth") (.var "function") _ _ _ _ (functionIH positions functionType functionTyped)
          · simpa [bound, before, environment, applySubst, Subst.lookup] using variable_returns program bound state "replacement"
          · simpa [bound, before, environment, applySubst, Subst.lookup] using variable_returns program bound state "depth"
          · simpa [bound, applySubst, Subst.lookup] using variable_returns program bound state "function"
        · apply computed_call_return operators constants replacement positions argument bound state
            (.var "replacement") (.var "depth") (.var "argument") _ _ _ _ (argumentIH positions argumentType argumentTyped)
          · simpa [bound, before, environment, applySubst, Subst.lookup] using variable_returns program bound state "replacement"
          · simpa [bound, before, environment, applySubst, Subst.lookup] using variable_returns program bound state "depth"
          · simpa [bound, applySubst, Subst.lookup] using variable_returns program bound state "argument"

/-- The real opener executes on a checked binder body and closed replacement.
No global interpretation of unrecognized operator or constant payloads is used. -/
theorem authored_open_computed_return (operators : TypeOp → Atom) (constants : Const → Atom)
    (replacement : CanonicalTerm) (term : DBTerm) (positions : List Ty) (type : Ty)
    (typed : term.inferType (positions ++ [replacement.ty]) = some type)
    (bindings : Subst) (state : State) (replacementExpr depthExpr termExpr : Atom)
    (replacementReturned : PureReturns program bindings state replacementExpr state (termAtom operators constants [] replacement.term))
    (depthReturned : PureReturns program bindings state depthExpr state (.grounded (.int positions.length)))
    (termReturned : PureReturns program bindings state termExpr state (termAtom operators constants (positions ++ [replacement.ty]) term)) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:open-binder", replacementExpr, depthExpr, termExpr]) state
      (termAtom operators constants positions (DBTerm.instantiateAt replacement.term positions.length term)) :=
  computed_call_return operators constants replacement positions term bindings state replacementExpr depthExpr termExpr _
    replacementReturned depthReturned termReturned (body_returns operators constants replacement term positions type typed state)

/-- Source execution and the shared binding operation have the same result;
typing follows from the existing shared HOL binder-instantiation theorem. -/
theorem authored_open_preserves_typing (operators : TypeOp → Atom) (constants : Const → Atom)
    (replacement : CanonicalTerm) (term : DBTerm) (positions : List Ty) (type : Ty)
    (typed : term.inferType (positions ++ [replacement.ty]) = some type)
    (bindings : Subst) (state : State) (replacementExpr depthExpr termExpr : Atom)
    (replacementReturned : PureReturns program bindings state replacementExpr state (termAtom operators constants [] replacement.term))
    (depthReturned : PureReturns program bindings state depthExpr state (.grounded (.int positions.length)))
    (termReturned : PureReturns program bindings state termExpr state (termAtom operators constants (positions ++ [replacement.ty]) term)) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:open-binder", replacementExpr, depthExpr, termExpr]) state
      (termAtom operators constants positions (DBTerm.instantiateAt replacement.term positions.length term)) ∧
    (DBTerm.instantiateAt replacement.term positions.length term).inferType positions = some type :=
  ⟨authored_open_computed_return operators constants replacement term positions type typed bindings state
    replacementExpr depthExpr termExpr replacementReturned depthReturned termReturned,
   DBTerm.inferType_instantiateAt replacement.term term replacement.ty replacement.checked positions typed⟩

end Mettapedia.Languages.HOLLight.MeTTa.BinderOpening
