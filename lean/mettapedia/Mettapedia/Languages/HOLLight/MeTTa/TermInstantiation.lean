import Mettapedia.Languages.HOLLight.MeTTa.Representation

/-!
# Authored type instantiation of shared HOL terms

Instantiation changes the types of free and bound occurrences while retaining
their identities and positions. Bound annotations are reconstructed in the
substituted context. The result is the existing shared substitution action,
executed by the actual quoted MeTTa source, without a native HOL primitive.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.TermInstantiation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open Eval
open Representation (termAtom variableAtom)
open TypeSubstitution (nameAtom typeAtom maplets)
open Effects (State)

private def equation : SpaceSemantics.Equation :=
  (syntaxSource.program.equations.filter
    (fun row => row.head == "hol-light:term-inst-type"))[0]'(by decide)

private def cases : SpaceSemantics.Cases :=
  match equation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def typeCall : Atom :=
  .expression [.symbol "hol-light:type-subst", .var "entries", .var "type"]

private def freeBody : Atom := .expression [.symbol "HOL:Free", .var "name", typeCall]
private def boundBody : Atom := .expression [.symbol "HOL:Bound", .var "index", typeCall]
private def constantBody : Atom := .expression [.symbol "HOL:C", .var "identity", typeCall]
private def lambdaBody : Atom := .expression [.symbol "HOL:Lam", typeCall,
  .expression [.symbol "hol-light:term-inst-type", .var "entries", .var "body"]]
private def applicationBody : Atom := .expression [.symbol "HOL:App",
  .expression [.symbol "hol-light:term-inst-type", .var "entries", .var "function"],
  .expression [.symbol "hol-light:term-inst-type", .var "entries", .var "argument"]]

private def environment (operators : TypeOp → Atom) (constants : Const → Atom)
    (entries : List (Ty × Ty)) (context : List Ty) (term : DBTerm) : Subst :=
  [("term", termAtom operators constants context term), ("entries", maplets operators entries)]

private theorem equation_unique :
    program.equations.filter (fun row => row.head == "hol-light:term-inst-type") = [equation] := by rfl
private theorem formals : equation.arguments = [.var "entries", .var "term"] := by decide
private theorem body_shape : equation.body =
    .expression [.symbol "case", .var "term",
      .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem cases_shape : cases =
    [(.expression [.symbol "HOL:Free", .var "name", .var "type"], freeBody),
     (.expression [.symbol "HOL:Bound", .var "index", .var "type"], boundBody),
     (.expression [.symbol "HOL:C", .var "identity", .var "type"], constantBody),
     (.expression [.symbol "HOL:Lam", .var "type", .var "body"], lambdaBody),
     (.expression [.symbol "HOL:App", .var "function", .var "argument"], applicationBody),
     (.var "malformed", .symbol "None")] := by decide

private theorem clause (operators : TypeOp → Atom) (constants : Const → Atom)
    (entries : List (Ty × Ty)) (context : List Ty) (term : DBTerm) :
    clauses program "hol-light:term-inst-type" [maplets operators entries, termAtom operators constants context term] =
      [.evaluate (environment operators constants entries context term) equation.body] := by
  rw [clauses_use_only_the_named_equations, equation_unique]
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_returns (operators : TypeOp → Atom) (constants : Const → Atom)
    (entries : List (Ty × Ty)) (term : DBTerm) (context : List Ty) (type : Ty)
    (checked : term.inferType context = some type) (state : State) :
    PureReturns program (environment operators constants entries context term) state equation.body state
      (termAtom operators constants (context.map (SourceSubstitution.typeSubstitution entries).apply)
        ((SourceSubstitution.typeOnlySubstitution entries).raw.applyDB term)) := by
  rw [body_shape]
  cases term with
  | free sourceVar =>
      let bound := [("type", typeAtom operators sourceVar.ty), ("name", nameAtom sourceVar.name)] ++
        environment operators constants entries context (.free sourceVar)
      apply case_returns program (environment operators constants entries context (.free sourceVar)) bound
        state state state (.var "term") (variableAtom operators sourceVar) freeBody
        _ _ cases (read_cases_encoded cases)
      · simpa [environment, termAtom, applySubst, Subst.lookup] using
          variable_returns program (environment operators constants entries context (.free sourceVar)) state "term"
      · simp [cases_shape, bound, environment, termAtom, variableAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · simp only [SourceSubstitution.typeOnlySubstitution, TypeCorrectTermSubstitution.ofTypes,
          TermSubst.applyDB, TermSubst.lookup, List.find?_nil, Option.map_none, termAtom, variableAtom,
          TypeSubst.applyVar]
        unfold freeBody
        apply binary_constructor_returns program bound state state state "HOL:Free" (.var "name") typeCall
          (nameAtom sourceVar.name) (typeAtom operators ((SourceSubstitution.typeSubstitution entries).apply sourceVar.ty))
          (by decide) (by decide)
        · simpa [bound, environment, applySubst, Subst.lookup] using variable_returns program bound state "name"
        · exact TypeSubstitution.authored_type_substitution_return operators bound state entries sourceVar.ty "entries" "type"
            (by simp [bound, environment, applySubst, Subst.lookup])
            (by simp [bound, environment, applySubst, Subst.lookup])
  | bound index =>
      have annotation : context[index]? = some type := by simpa only [DBTerm.inferType] using checked
      let bound := [("type", typeAtom operators type), ("index", Atom.grounded (.int index))] ++
        environment operators constants entries context (.bound index)
      apply case_returns program (environment operators constants entries context (.bound index)) bound
        state state state (.var "term") (termAtom operators constants context (.bound index)) boundBody
        _ _ cases (read_cases_encoded cases)
      · exact variable_returns program _ state "term"
      · simp [cases_shape, bound, annotation, environment, termAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · simp only [SourceSubstitution.typeOnlySubstitution, TypeCorrectTermSubstitution.ofTypes,
          TermSubst.applyDB_bound, termAtom, List.getElem?_map, annotation, Option.map_some, Option.getD_some]
        unfold boundBody
        apply binary_constructor_returns program bound state state state "HOL:Bound" (.var "index") typeCall
          (.grounded (.int index)) (typeAtom operators ((SourceSubstitution.typeSubstitution entries).apply type))
          (by decide) (by decide)
        · simpa [bound, environment, applySubst, Subst.lookup] using variable_returns program bound state "index"
        · exact TypeSubstitution.authored_type_substitution_return operators bound state entries type "entries" "type"
            (by simp [bound, environment, applySubst, Subst.lookup])
            (by simp [bound, environment, applySubst, Subst.lookup])
  | const constant annotation =>
      let bound := [("type", typeAtom operators annotation), ("identity", constants constant)] ++
        environment operators constants entries context (.const constant annotation)
      apply case_returns program (environment operators constants entries context (.const constant annotation)) bound
        state state state (.var "term") (termAtom operators constants context (.const constant annotation)) constantBody
        _ _ cases (read_cases_encoded cases)
      · exact variable_returns program _ state "term"
      · simp [cases_shape, bound, environment, termAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · simp only [SourceSubstitution.typeOnlySubstitution, TypeCorrectTermSubstitution.ofTypes,
          TermSubst.applyDB_const, termAtom]
        unfold constantBody
        apply binary_constructor_returns program bound state state state "HOL:C" (.var "identity") typeCall
          (constants constant) (typeAtom operators ((SourceSubstitution.typeSubstitution entries).apply annotation))
          (by decide) (by decide)
        · simpa [bound, environment, applySubst, Subst.lookup] using variable_returns program bound state "identity"
        · exact TypeSubstitution.authored_type_substitution_return operators bound state entries annotation "entries" "type"
            (by simp [bound, environment, applySubst, Subst.lookup])
            (by simp [bound, environment, applySubst, Subst.lookup])
  | abs domain body =>
      obtain ⟨codomain, bodyChecked, _⟩ := DBTerm.inferType_abs_eq_some_iff.mp checked
      let bound := [("body", termAtom operators constants (domain :: context) body), ("type", typeAtom operators domain)] ++
        environment operators constants entries context (.abs domain body)
      apply case_returns program (environment operators constants entries context (.abs domain body)) bound
        state state state (.var "term") (termAtom operators constants context (.abs domain body)) lambdaBody
        _ _ cases (read_cases_encoded cases)
      · exact variable_returns program _ state "term"
      · simp [cases_shape, bound, environment, termAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · simp only [SourceSubstitution.typeOnlySubstitution, TypeCorrectTermSubstitution.ofTypes,
          TermSubst.applyDB_abs, termAtom]
        unfold lambdaBody
        apply binary_constructor_returns program bound state state state "HOL:Lam" typeCall
          (.expression [.symbol "hol-light:term-inst-type", .var "entries", .var "body"])
          (typeAtom operators ((SourceSubstitution.typeSubstitution entries).apply domain))
          (termAtom operators constants ((domain :: context).map (SourceSubstitution.typeSubstitution entries).apply)
            ((SourceSubstitution.typeOnlySubstitution entries).raw.applyDB body)) (by decide) (by decide)
        · exact TypeSubstitution.authored_type_substitution_return operators bound state entries domain "entries" "type"
            (by simp [bound, environment, applySubst, Subst.lookup])
            (by simp [bound, environment, applySubst, Subst.lookup])
        · apply authored_variable_call_returns program bound
            (environment operators constants entries (domain :: context) body) state state "hol-light:term-inst-type"
            ["entries", "body"] equation.body _ (by decide) (by decide) (by decide) _
            (body_returns operators constants entries body (domain :: context) codomain bodyChecked state) (by decide)
          simpa [bound, environment, applySubst, Subst.lookup] using clause operators constants entries (domain :: context) body
  | app function argument =>
      obtain ⟨domain, functionChecked, argumentChecked⟩ := DBTerm.inferType_app_eq_some_iff.mp checked
      let bound := [("argument", termAtom operators constants context argument), ("function", termAtom operators constants context function)] ++
        environment operators constants entries context (.app function argument)
      apply case_returns program (environment operators constants entries context (.app function argument)) bound
        state state state (.var "term") (termAtom operators constants context (.app function argument)) applicationBody
        _ _ cases (read_cases_encoded cases)
      · exact variable_returns program _ state "term"
      · simp [cases_shape, bound, environment, termAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · simp only [SourceSubstitution.typeOnlySubstitution, TypeCorrectTermSubstitution.ofTypes,
          TermSubst.applyDB_app, termAtom]
        unfold applicationBody
        apply binary_constructor_returns program bound state state state "HOL:App"
          (.expression [.symbol "hol-light:term-inst-type", .var "entries", .var "function"])
          (.expression [.symbol "hol-light:term-inst-type", .var "entries", .var "argument"])
          (termAtom operators constants (context.map (SourceSubstitution.typeSubstitution entries).apply)
            ((SourceSubstitution.typeOnlySubstitution entries).raw.applyDB function))
          (termAtom operators constants (context.map (SourceSubstitution.typeSubstitution entries).apply)
            ((SourceSubstitution.typeOnlySubstitution entries).raw.applyDB argument)) (by decide) (by decide)
        · apply authored_variable_call_returns program bound (environment operators constants entries context function)
            state state "hol-light:term-inst-type" ["entries", "function"] equation.body _
            (by decide) (by decide) (by decide) _
            (body_returns operators constants entries function context (.function domain type) functionChecked state) (by decide)
          simpa [bound, environment, applySubst, Subst.lookup] using clause operators constants entries context function
        · apply authored_variable_call_returns program bound (environment operators constants entries context argument)
            state state "hol-light:term-inst-type" ["entries", "argument"] equation.body _
            (by decide) (by decide) (by decide) _
            (body_returns operators constants entries argument context domain argumentChecked state) (by decide)
          simpa [bound, environment, applySubst, Subst.lookup] using clause operators constants entries context argument
termination_by sizeOf term

/-- The authored instantiation agrees with shared STT on every checked term
and its actual substituted binder context. -/
theorem authored_type_instantiation_return (operators : TypeOp → Atom) (constants : Const → Atom)
    (bindings : Subst) (state : State) (entries : List (Ty × Ty)) (context : List Ty)
    (term : DBTerm) (type : Ty) (checked : term.inferType context = some type)
    (entriesKey termKey : String)
    (capturedEntries : applySubst bindings (.var entriesKey) = maplets operators entries)
    (capturedTerm : applySubst bindings (.var termKey) = termAtom operators constants context term) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:term-inst-type", .var entriesKey, .var termKey]) state
      (termAtom operators constants (context.map (SourceSubstitution.typeSubstitution entries).apply)
        ((SourceSubstitution.typeOnlySubstitution entries).raw.applyDB term)) := by
  apply authored_variable_call_returns program bindings (environment operators constants entries context term)
    state state "hol-light:term-inst-type" [entriesKey, termKey] equation.body _
    (by decide) (by decide) (by decide) _
    (body_returns operators constants entries term context type checked state) (by decide)
  simpa only [List.map_cons, List.map_nil, capturedEntries, capturedTerm] using clause operators constants entries context term

/-- The executed result has the substituted type in the substituted context,
using the existing shared calculus's general preservation theorem. -/
theorem authored_type_instantiation_preserves_typing (operators : TypeOp → Atom) (constants : Const → Atom)
    (bindings : Subst) (state : State) (entries : List (Ty × Ty)) (context : List Ty)
    (term : DBTerm) (type : Ty) (checked : term.inferType context = some type)
    (entriesKey termKey : String)
    (capturedEntries : applySubst bindings (.var entriesKey) = maplets operators entries)
    (capturedTerm : applySubst bindings (.var termKey) = termAtom operators constants context term) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:term-inst-type", .var entriesKey, .var termKey]) state
      (termAtom operators constants (context.map (SourceSubstitution.typeSubstitution entries).apply)
        ((SourceSubstitution.typeOnlySubstitution entries).raw.applyDB term)) ∧
    ((SourceSubstitution.typeOnlySubstitution entries).raw.applyDB term).inferType
      (context.map (SourceSubstitution.typeSubstitution entries).apply) =
        some ((SourceSubstitution.typeSubstitution entries).apply type) := by
  exact ⟨authored_type_instantiation_return operators constants bindings state entries context term type checked
    entriesKey termKey capturedEntries capturedTerm,
    TermSubst.inferType_applyDB (SourceSubstitution.typeOnlySubstitution entries).typeCorrect checked⟩

end Mettapedia.Languages.HOLLight.MeTTa.TermInstantiation
