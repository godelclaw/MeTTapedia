import Mettapedia.Languages.HOLLight.MeTTa.Representation
import Mettapedia.Languages.MeTTa.PeTTa.CoreExecution

/-!
# Shared HOL typing computed by the authored MeTTa library

The actual retained `term-type` equation computes the existing shared STT
judgment on checked positional terms. Its binder annotations come from the
context, and its function constructor uses the registered HOL Light name.
This computation does not admit constants, operators or axioms: their
declaration formation remains a separate obligation at the source boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.TermJudgment

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open Eval
open Effects (State boolean)
open Representation (termAtom variableAtom registeredOperatorAtom)
open TypeSubstitution (nameAtom typeAtom)

private def equation : SpaceSemantics.Equation :=
  (syntaxSource.program.equations.filter
    (fun row => row.head == "hol-light:term-type"))[0]'(by decide)

private def cases : SpaceSemantics.Cases :=
  match equation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def lambdaBody : Atom := .expression [.symbol "case",
  .expression [.symbol "hol-light:term-type", .var "body"], .expression
    [.expression [.expression [.symbol "Some", .var "codomain"],
      .expression [.symbol "Some",
        .expression [.symbol "hol-light:fun", .var "domain", .var "codomain"]]],
     .expression [.var "malformed", .symbol "None"]]]

private def applicationBody : Atom := .expression [.symbol "case",
  .expression [.symbol "hol-light:term-type", .var "function"], .expression
    [.expression [.expression [.symbol "Some", .expression [.symbol "Tyapp",
       .grounded (.string "fun"), .expression [.symbol "HOL:Cons", .var "domain",
         .expression [.symbol "HOL:Cons", .var "codomain", .symbol "HOL:Nil"]]]],
      .expression [.symbol "if", .expression [.symbol "==",
        .expression [.symbol "hol-light:term-type", .var "argument"],
        .expression [.symbol "Some", .var "domain"]],
        .expression [.symbol "Some", .var "codomain"], .symbol "None"]],
     .expression [.var "malformed", .symbol "None"]]]

private def applicationSelected : Atom := .expression [.symbol "if", .expression [.symbol "==",
  .expression [.symbol "hol-light:term-type", .var "argument"],
  .expression [.symbol "Some", .var "domain"]],
  .expression [.symbol "Some", .var "codomain"], .symbol "None"]

private def lambdaCases : SpaceSemantics.Cases :=
  match lambdaBody with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def applicationCases : SpaceSemantics.Cases :=
  match applicationBody with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def environment (constants : Const → Atom) (context : List Ty) (term : DBTerm) : Subst :=
  [("term", termAtom registeredOperatorAtom constants context term)]

private theorem equation_unique :
    program.equations.filter (fun row => row.head == "hol-light:term-type") = [equation] := by rfl

private theorem formals : equation.arguments = [.var "term"] := by decide

private theorem body_shape : equation.body =
    .expression [.symbol "case", .var "term",
      .expression (cases.map fun row => .expression [row.1, row.2])] := by decide

private theorem cases_shape : cases =
    [(.expression [.symbol "HOL:Free", .var "name", .var "type"],
       .expression [.symbol "Some", .var "type"]),
     (.expression [.symbol "HOL:Bound", .var "index", .var "type"],
       .expression [.symbol "Some", .var "type"]),
     (.expression [.symbol "HOL:C", .var "identity", .var "type"],
       .expression [.symbol "Some", .var "type"]),
     (.expression [.symbol "HOL:Lam", .var "domain", .var "body"], lambdaBody),
     (.expression [.symbol "HOL:App", .var "function", .var "argument"], applicationBody),
     (.var "malformed", .symbol "None")] := by decide

private theorem lambda_shape : lambdaBody = .expression [.symbol "case",
    .expression [.symbol "hol-light:term-type", .var "body"],
    .expression (lambdaCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem application_shape : applicationBody = .expression [.symbol "case",
    .expression [.symbol "hol-light:term-type", .var "function"],
    .expression (applicationCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem lambda_cases_shape : lambdaCases =
    [(.expression [.symbol "Some", .var "codomain"],
       .expression [.symbol "Some", .expression [.symbol "hol-light:fun", .var "domain", .var "codomain"]]),
     (.var "malformed", .symbol "None")] := by decide

private theorem application_cases_shape : applicationCases =
    [(.expression [.symbol "Some", .expression [.symbol "Tyapp", .grounded (.string "fun"),
        .expression [.symbol "HOL:Cons", .var "domain",
          .expression [.symbol "HOL:Cons", .var "codomain", .symbol "HOL:Nil"]]]], applicationSelected),
     (.var "malformed", .symbol "None")] := by decide

private theorem clause (constants : Const → Atom) (context : List Ty) (term : DBTerm) :
    clauses program "hol-light:term-type" [termAtom registeredOperatorAtom constants context term] =
      [.evaluate (environment constants context term) equation.body] := by
  rw [clauses_use_only_the_named_equations, equation_unique]
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private def functionEquation : SpaceSemantics.Equation :=
  (syntaxSource.program.equations.filter
    (fun row => row.head == "hol-light:fun"))[0]'(by decide)

private def functionEnvironment (domain codomain : Ty) : Subst :=
  [("codomain", typeAtom registeredOperatorAtom codomain),
    ("domain", typeAtom registeredOperatorAtom domain)]

private theorem function_clause (domain codomain : Ty) :
    clauses program "hol-light:fun" [typeAtom registeredOperatorAtom domain, typeAtom registeredOperatorAtom codomain] =
      [.evaluate (functionEnvironment domain codomain) functionEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:fun") = [functionEquation] := by rfl
  rw [unique]
  have arguments : functionEquation.arguments = [.var "domain", .var "codomain"] := by decide
  simp [arguments, functionEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem function_body_return (state : State) (domain codomain : Ty) :
    BoundCalls.CorePath.PureReturns program (functionEnvironment domain codomain) state functionEquation.body state
      (typeAtom registeredOperatorAtom (.function domain codomain)) := by
  have body : functionEquation.body = .expression [.symbol "Tyapp", .grounded (.string "fun"),
      .expression [.symbol "HOL:Cons", .var "domain",
        .expression [.symbol "HOL:Cons", .var "codomain", .symbol "HOL:Nil"]]] := by decide
  rw [body]
  simp only [Ty.function, typeAtom, Representation.registered_function_atom,
    List.map_cons, List.map_nil, Premises.keys]
  apply BoundCalls.CorePath.binary_constructor_returns program (functionEnvironment domain codomain) state state state "Tyapp"
    (.grounded (.string "fun")) _ (.grounded (.string "fun")) _ (by decide) (by decide)
  · exact BoundCalls.CorePath.grounded_returns program (functionEnvironment domain codomain) state _
  · apply BoundCalls.CorePath.binary_constructor_returns program (functionEnvironment domain codomain) state state state "HOL:Cons"
        (.var "domain") _ _ _ (by decide) (by decide)
    · simpa [functionEnvironment, applySubst, Subst.lookup] using
        BoundCalls.CorePath.variable_returns program (functionEnvironment domain codomain) state "domain"
    · apply BoundCalls.CorePath.binary_constructor_returns program (functionEnvironment domain codomain) state state state "HOL:Cons"
          (.var "codomain") (.symbol "HOL:Nil") _ _ (by decide) (by decide)
      · simpa [functionEnvironment, applySubst, Subst.lookup] using
          BoundCalls.CorePath.variable_returns program (functionEnvironment domain codomain) state "codomain"
      · exact BoundCalls.CorePath.symbol_returns program (functionEnvironment domain codomain) state "HOL:Nil"

/-- Source function types are constructed after computing both supplied type
values; this law also serves primitive-signature initialization. -/
theorem authored_function_certificate (bindings : Subst) (state : State) (left right : Atom)
    (domain codomain : Ty)
    (leftReturns : BoundCalls.CorePath.PureReturns program bindings state left state (typeAtom registeredOperatorAtom domain))
    (rightReturns : BoundCalls.CorePath.PureReturns program bindings state right state (typeAtom registeredOperatorAtom codomain)) :
    BoundCalls.CorePath.PureReturns program bindings state (.expression [.symbol "hol-light:fun", left, right]) state
      (typeAtom registeredOperatorAtom (.function domain codomain)) := by
  exact BoundCalls.CorePath.authored_binary_call_returns program bindings (functionEnvironment domain codomain)
    state state state state "hol-light:fun" left right _ _ functionEquation.body _
    (by decide) (by decide) (by decide) (by decide) (by decide)
    leftReturns rightReturns (function_clause domain codomain) (function_body_return state domain codomain) (by decide)

private theorem function_return (bindings : Subst) (state : State)
    (domain codomain : Ty) (domainKey codomainKey : String)
    (capturedDomain : applySubst bindings (.var domainKey) = typeAtom registeredOperatorAtom domain)
    (capturedCodomain : applySubst bindings (.var codomainKey) = typeAtom registeredOperatorAtom codomain) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:fun", .var domainKey, .var codomainKey]) state
      (typeAtom registeredOperatorAtom (.function domain codomain)) := by
  exact authored_function_certificate bindings state _ _ domain codomain
    (by simpa only [capturedDomain] using BoundCalls.CorePath.variable_returns program bindings state domainKey)
    (by simpa only [capturedCodomain] using BoundCalls.CorePath.variable_returns program bindings state codomainKey)

private theorem body_returns (constants : Const → Atom) (term : DBTerm)
    (context : List Ty) (type : Ty) (checked : term.inferType context = some type) (state : State) :
    BoundCalls.CorePath.PureReturns program (environment constants context term) state equation.body state
      (.expression [.symbol "Some", typeAtom registeredOperatorAtom type]) := by
  rw [body_shape]
  cases term with
  | free sourceVar =>
      have typeSame : sourceVar.ty = type := by simpa using checked
      subst type
      let bound := [("type", typeAtom registeredOperatorAtom sourceVar.ty),
        ("name", nameAtom sourceVar.name)] ++ environment constants context (.free sourceVar)
      apply BoundCalls.CorePath.case_returns program (environment constants context (.free sourceVar)) bound state state state
        (.var "term") (variableAtom registeredOperatorAtom sourceVar)
        (.expression [.symbol "Some", .var "type"]) _ _ cases (read_cases_encoded cases)
      · simpa [environment, termAtom, applySubst, Subst.lookup] using
          BoundCalls.CorePath.variable_returns program (environment constants context (.free sourceVar)) state "term"
      · simp [cases_shape, bound, environment, termAtom, variableAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · simpa [bound, applySubst, Subst.lookup] using
          BoundCalls.CorePath.unary_constructor_returns program bound state "Some" "type" (by decide) (by decide)
  | bound index =>
      have annotation : context[index]? = some type := by simpa using checked
      let bound := [("type", typeAtom registeredOperatorAtom type), ("index", Atom.grounded (.int index))] ++
        environment constants context (.bound index)
      apply BoundCalls.CorePath.case_returns program (environment constants context (.bound index)) bound state state state
        (.var "term") (termAtom registeredOperatorAtom constants context (.bound index))
        (.expression [.symbol "Some", .var "type"]) _ _ cases (read_cases_encoded cases)
      · exact BoundCalls.CorePath.variable_returns program _ state "term"
      · simp [cases_shape, bound, environment, annotation, termAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · simpa [bound, applySubst, Subst.lookup] using
          BoundCalls.CorePath.unary_constructor_returns program bound state "Some" "type" (by decide) (by decide)
  | const constant annotation =>
      have typeSame : annotation = type := by simpa using checked
      subst type
      let bound := [("type", typeAtom registeredOperatorAtom annotation), ("identity", constants constant)] ++
        environment constants context (.const constant annotation)
      apply BoundCalls.CorePath.case_returns program (environment constants context (.const constant annotation)) bound state state state
        (.var "term") (termAtom registeredOperatorAtom constants context (.const constant annotation))
        (.expression [.symbol "Some", .var "type"]) _ _ cases (read_cases_encoded cases)
      · exact BoundCalls.CorePath.variable_returns program _ state "term"
      · simp [cases_shape, bound, environment, termAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · simpa [bound, applySubst, Subst.lookup] using
          BoundCalls.CorePath.unary_constructor_returns program bound state "Some" "type" (by decide) (by decide)
  | abs domain body =>
      obtain ⟨codomain, bodyChecked, rfl⟩ := DBTerm.inferType_abs_eq_some_iff.mp checked
      let bound := [("body", termAtom registeredOperatorAtom constants (domain :: context) body),
        ("domain", typeAtom registeredOperatorAtom domain)] ++ environment constants context (.abs domain body)
      apply BoundCalls.CorePath.case_returns program (environment constants context (.abs domain body)) bound state state state
        (.var "term") (termAtom registeredOperatorAtom constants context (.abs domain body))
        lambdaBody _ _ cases (read_cases_encoded cases)
      · exact BoundCalls.CorePath.variable_returns program _ state "term"
      · simp [cases_shape, bound, environment, termAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · rw [lambda_shape]
        let inner := ("codomain", typeAtom registeredOperatorAtom codomain) :: bound
        apply BoundCalls.CorePath.case_returns program bound inner state state state
          (.expression [.symbol "hol-light:term-type", .var "body"])
          (.expression [.symbol "Some", typeAtom registeredOperatorAtom codomain])
          (.expression [.symbol "Some", .expression [.symbol "hol-light:fun", .var "domain", .var "codomain"]])
          _ _ lambdaCases (read_cases_encoded lambdaCases)
        · apply BoundCalls.CorePath.authored_variable_call_returns program bound (environment constants (domain :: context) body)
            state state "hol-light:term-type" ["body"] equation.body _
            (by decide) (by decide) (by decide) _
            (body_returns constants body (domain :: context) codomain bodyChecked state) (by decide)
          simpa [bound, environment, applySubst, Subst.lookup] using clause constants (domain :: context) body
        · simp [lambda_cases_shape, inner, bound, environment, SpaceSemantics.selectCase,
            SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · apply BoundCalls.CorePath.unary_constructor_of_returns program inner state state "Some" _ _ (by decide) (by decide)
          exact function_return inner state domain codomain "domain" "codomain"
            (by simp [inner, bound, applySubst, Subst.lookup])
            (by simp [inner, bound, applySubst, Subst.lookup])
  | app function argument =>
      obtain ⟨domain, functionChecked, argumentChecked⟩ := DBTerm.inferType_app_eq_some_iff.mp checked
      let bound := [("argument", termAtom registeredOperatorAtom constants context argument),
        ("function", termAtom registeredOperatorAtom constants context function)] ++
          environment constants context (.app function argument)
      apply BoundCalls.CorePath.case_returns program (environment constants context (.app function argument)) bound state state state
        (.var "term") (termAtom registeredOperatorAtom constants context (.app function argument))
        applicationBody _ _ cases (read_cases_encoded cases)
      · exact BoundCalls.CorePath.variable_returns program _ state "term"
      · simp [cases_shape, bound, environment, termAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · rw [application_shape]
        let inner := [("codomain", typeAtom registeredOperatorAtom type),
          ("domain", typeAtom registeredOperatorAtom domain)] ++ bound
        apply BoundCalls.CorePath.case_returns program bound inner state state state
          (.expression [.symbol "hol-light:term-type", .var "function"])
          (.expression [.symbol "Some", typeAtom registeredOperatorAtom (.function domain type)])
          applicationSelected _ _ applicationCases (read_cases_encoded applicationCases)
        · apply BoundCalls.CorePath.authored_variable_call_returns program bound (environment constants context function)
            state state "hol-light:term-type" ["function"] equation.body _
            (by decide) (by decide) (by decide) _
            (body_returns constants function context (.function domain type) functionChecked state) (by decide)
          simpa [bound, environment, applySubst, Subst.lookup] using clause constants context function
        · simp [application_cases_shape, inner, bound, environment,
            Ty.function, typeAtom, Representation.registered_function_atom, Premises.keys,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · unfold applicationSelected
          apply BoundCalls.CorePath.if_returns program inner state state state _ (boolean true) _ _ _ _ _
          · apply BoundCalls.CorePath.native_binary_call_returns program inner state state state state "=="
              (.expression [.symbol "hol-light:term-type", .var "argument"])
              (.expression [.symbol "Some", .var "domain"])
              (.expression [.symbol "Some", typeAtom registeredOperatorAtom domain])
              (.expression [.symbol "Some", typeAtom registeredOperatorAtom domain]) (boolean true)
              (by decide) (by decide) (by decide) (by decide) _ _ _ (by decide)
            · apply BoundCalls.CorePath.authored_variable_call_returns program inner (environment constants context argument)
                state state "hol-light:term-type" ["argument"] equation.body _
                (by decide) (by decide) (by decide) _
                (body_returns constants argument context domain argumentChecked state) (by decide)
              simpa [inner, bound, environment, applySubst, Subst.lookup] using clause constants context argument
            · simpa [inner, applySubst, Subst.lookup] using
                BoundCalls.CorePath.unary_constructor_returns program inner state "Some" "domain" (by decide) (by decide)
            · simp [StdLib.structural_equality, boolean]
          · simpa [inner, applySubst, Subst.lookup] using
              BoundCalls.CorePath.unary_constructor_returns program inner state "Some" "codomain" (by decide) (by decide)
termination_by sizeOf term

/-- Every checked canonical term computes its existing shared STT type by
running the authored equation, in its actual positional context. -/
theorem authored_term_type_certificate (constants : Const → Atom) (bindings : Subst) (state : State)
    (context : List Ty) (term : DBTerm) (type : Ty) (checked : term.inferType context = some type)
    (termKey : String)
    (capturedTerm : applySubst bindings (.var termKey) = termAtom registeredOperatorAtom constants context term) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:term-type", .var termKey]) state
      (.expression [.symbol "Some", typeAtom registeredOperatorAtom type]) := by
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings (environment constants context term)
    state state "hol-light:term-type" [termKey] equation.body _
    (by decide) (by decide) (by decide) _
    (body_returns constants term context type checked state) (by decide)
  simpa only [List.map_cons, List.map_nil, capturedTerm] using clause constants context term

/-- Distinct admitted argument types cannot become equal through their printed
representation. The actual authored judgment refuses such an application. -/
theorem authored_wrong_domain_refused_certificate (theory : DefinitionAdapters.TheoryContext)
    (constants : Const → Atom) (bindings : Subst) (state : State) (context : List Ty)
    (function argument : DBTerm) (domain codomain argumentType : Ty)
    (functionChecked : function.inferType context = some (.function domain codomain))
    (argumentChecked : argument.inferType context = some argumentType)
    (domainFormed : SignatureFormation.TypeFormed theory.signature domain)
    (argumentFormed : SignatureFormation.TypeFormed theory.signature argumentType)
    (different : argumentType ≠ domain) (termKey : String)
    (capturedTerm : applySubst bindings (.var termKey) =
      termAtom registeredOperatorAtom constants context (.app function argument)) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:term-type", .var termKey]) state (.symbol "None") := by
  have encodedDifferent : typeAtom registeredOperatorAtom argumentType ≠
      typeAtom registeredOperatorAtom domain := fun same => different
    (Representation.registered_typeAtom_injective theory argumentType domain argumentFormed domainFormed same)
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings (environment constants context (.app function argument))
    state state "hol-light:term-type" [termKey] equation.body _
    (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, capturedTerm] using clause constants context (.app function argument)
  · rw [body_shape]
    let bound := [("argument", termAtom registeredOperatorAtom constants context argument),
      ("function", termAtom registeredOperatorAtom constants context function)] ++
        environment constants context (.app function argument)
    apply BoundCalls.CorePath.case_returns program (environment constants context (.app function argument)) bound state state state
      (.var "term") (termAtom registeredOperatorAtom constants context (.app function argument))
      applicationBody _ _ cases (read_cases_encoded cases)
    · exact BoundCalls.CorePath.variable_returns program _ state "term"
    · simp [cases_shape, bound, environment, termAtom,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · rw [application_shape]
      let inner := [("codomain", typeAtom registeredOperatorAtom codomain),
        ("domain", typeAtom registeredOperatorAtom domain)] ++ bound
      apply BoundCalls.CorePath.case_returns program bound inner state state state
        (.expression [.symbol "hol-light:term-type", .var "function"])
        (.expression [.symbol "Some", typeAtom registeredOperatorAtom (.function domain codomain)])
        applicationSelected _ _ applicationCases (read_cases_encoded applicationCases)
      · exact authored_term_type_certificate constants bound state context function (.function domain codomain)
          functionChecked "function" (by simp [bound, applySubst, Subst.lookup])
      · simp [application_cases_shape, inner, bound, environment, Ty.function, typeAtom,
          Representation.registered_function_atom, Premises.keys, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · unfold applicationSelected
        apply BoundCalls.CorePath.if_returns program inner state state state _ (boolean false) _ _ _ _ _
        · apply BoundCalls.CorePath.native_binary_call_returns program inner state state state state "=="
            (.expression [.symbol "hol-light:term-type", .var "argument"])
            (.expression [.symbol "Some", .var "domain"])
            (.expression [.symbol "Some", typeAtom registeredOperatorAtom argumentType])
            (.expression [.symbol "Some", typeAtom registeredOperatorAtom domain]) (boolean false)
            (by decide) (by decide) (by decide) (by decide) _ _ _ (by decide)
          · exact authored_term_type_certificate constants inner state context argument argumentType
              argumentChecked "argument" (by simp [inner, bound, applySubst, Subst.lookup])
          · simpa [inner, applySubst, Subst.lookup] using
              BoundCalls.CorePath.unary_constructor_returns program inner state "Some" "domain" (by decide) (by decide)
          · simp [StdLib.structural_equality, boolean, encodedDifferent]
        · exact BoundCalls.CorePath.symbol_returns program inner state "None"


theorem authored_function_return (bindings : Subst) (state : State) (left right : Atom)
    (domain codomain : Ty)
    (leftReturns : PureReturns program bindings state left state (typeAtom registeredOperatorAtom domain))
    (rightReturns : PureReturns program bindings state right state (typeAtom registeredOperatorAtom codomain)) :
    PureReturns program bindings state (.expression [.symbol "hol-light:fun", left, right]) state
      (typeAtom registeredOperatorAtom (.function domain codomain)) := by
  exact authored_binary_call_returns program bindings (functionEnvironment domain codomain)
    state state state state "hol-light:fun" left right _ _ functionEquation.body _
    (by decide) (by decide) (by decide) (by decide) (by decide)
    leftReturns rightReturns (function_clause domain codomain) (function_body_return state domain codomain).original (by decide)


theorem authored_term_type_return (constants : Const → Atom) (bindings : Subst) (state : State)
    (context : List Ty) (term : DBTerm) (type : Ty) (checked : term.inferType context = some type)
    (termKey : String)
    (capturedTerm : applySubst bindings (.var termKey) = termAtom registeredOperatorAtom constants context term) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:term-type", .var termKey]) state
      (.expression [.symbol "Some", typeAtom registeredOperatorAtom type]) :=
  (authored_term_type_certificate constants bindings state context term type checked termKey capturedTerm).original

theorem authored_term_type_bound_return (constants : Const → Atom) (bindings : Subst) (state : State)
    (context : List Ty) (term : DBTerm) (type : Ty) (checked : term.inferType context = some type)
    (termKey : String)
    (capturedTerm : applySubst bindings (.var termKey) = termAtom registeredOperatorAtom constants context term) :
    BoundCalls.PureReturns program bindings state
      (.expression [.symbol "hol-light:term-type", .var termKey]) state
      (.expression [.symbol "Some", typeAtom registeredOperatorAtom type]) :=
  (authored_term_type_certificate constants bindings state context term type checked termKey capturedTerm).extended

theorem authored_wrong_domain_refused (theory : DefinitionAdapters.TheoryContext)
    (constants : Const → Atom) (bindings : Subst) (state : State) (context : List Ty)
    (function argument : DBTerm) (domain codomain argumentType : Ty)
    (functionChecked : function.inferType context = some (.function domain codomain))
    (argumentChecked : argument.inferType context = some argumentType)
    (domainFormed : SignatureFormation.TypeFormed theory.signature domain)
    (argumentFormed : SignatureFormation.TypeFormed theory.signature argumentType)
    (different : argumentType ≠ domain) (termKey : String)
    (capturedTerm : applySubst bindings (.var termKey) =
      termAtom registeredOperatorAtom constants context (.app function argument)) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:term-type", .var termKey]) state (.symbol "None") :=
  (authored_wrong_domain_refused_certificate theory constants bindings state context function argument domain codomain argumentType functionChecked argumentChecked domainFormed argumentFormed different termKey capturedTerm).original

theorem authored_wrong_domain_bound_refused (theory : DefinitionAdapters.TheoryContext)
    (constants : Const → Atom) (bindings : Subst) (state : State) (context : List Ty)
    (function argument : DBTerm) (domain codomain argumentType : Ty)
    (functionChecked : function.inferType context = some (.function domain codomain))
    (argumentChecked : argument.inferType context = some argumentType)
    (domainFormed : SignatureFormation.TypeFormed theory.signature domain)
    (argumentFormed : SignatureFormation.TypeFormed theory.signature argumentType)
    (different : argumentType ≠ domain) (termKey : String)
    (capturedTerm : applySubst bindings (.var termKey) =
      termAtom registeredOperatorAtom constants context (.app function argument)) :
    BoundCalls.PureReturns program bindings state
      (.expression [.symbol "hol-light:term-type", .var termKey]) state (.symbol "None") :=
  (authored_wrong_domain_refused_certificate theory constants bindings state context function argument domain codomain argumentType functionChecked argumentChecked domainFormed argumentFormed different termKey capturedTerm).extended

end Mettapedia.Languages.HOLLight.MeTTa.TermJudgment
