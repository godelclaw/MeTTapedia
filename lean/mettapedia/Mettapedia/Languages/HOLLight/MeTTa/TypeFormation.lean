import Mettapedia.Languages.HOLLight.MeTTa.OperatorTable
import Mettapedia.Languages.HOLLight.MeTTa.ListOperations

/-!
# Registered type formation executed by the authored HOL library

HOL Light uses string names for formal type parameters. Operator occurrences
are first resolved to admitted declarations. Neither condition asserts type
formation: a resolved operator can still have the wrong number of arguments.
The execution theorem computes the existing shared signature-formation test,
including its refusals, on arbitrary finite resolved source types.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.TypeFormation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.SignatureFormation
open Eval
open Effects (State boolean)
open TypeSubstitution (nameAtom typeAtom)
open Representation (registeredOperatorAtom)

/-- Structural source resolution, independently of the operator's arity. -/
def Resolved (signature : Signature) : Ty → Prop
  | .var name => name.namespaceComponents = []
  | .op operator arguments =>
      (∃ arity, signature.typeOperators operator = some arity) ∧
        ∀ argument ∈ arguments, Resolved signature argument
termination_by type => sizeOf type

private def typeEquation : SpaceSemantics.Equation :=
  (syntaxSource.program.equations.filter
    (fun row => row.head == "hol-light:type-formed"))[0]'(by decide)
private def listEquation : SpaceSemantics.Equation :=
  (syntaxSource.program.equations.filter
    (fun row => row.head == "hol-light:types-formed"))[0]'(by decide)

private def typeCases : SpaceSemantics.Cases :=
  match typeEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def listCases : SpaceSemantics.Cases :=
  match listEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def registeredBody : Atom := .expression [.symbol "if",
  .expression [.symbol "hol-light:list-valid", .var "arguments"],
  .expression [.symbol "if", .expression [.symbol "==",
    .expression [.symbol "hol-light:length", .var "arguments"], .var "arity"],
    .expression [.symbol "hol-light:types-formed", .var "operators", .var "arguments"],
    boolean false], boolean false]

private def operatorBody : Atom := .expression [.symbol "case",
  .expression [.symbol "hol-light:lookup", .var "name", .var "operators"],
  .expression [.expression [.expression [.symbol "Some", .expression
    [.symbol "HOL:TypeOperator", .var "arity", .var "origin"]], registeredBody],
    .expression [.var "unknown", boolean false]]]

private def operatorCases : SpaceSemantics.Cases :=
  match operatorBody with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def consBody : Atom := .expression [.symbol "if",
  .expression [.symbol "hol-light:type-formed", .var "operators", .var "first"],
  .expression [.symbol "hol-light:types-formed", .var "operators", .var "rest"], boolean false]

private def typeEnvironment (operators : Atom) (type : Ty) : Subst :=
  [("type", typeAtom registeredOperatorAtom type), ("operators", operators)]
private def listEnvironment (operators : Atom) (types : List Ty) : Subst :=
  [("types", Premises.keys (types.map (typeAtom registeredOperatorAtom))), ("operators", operators)]

private theorem type_unique :
    program.equations.filter (fun row => row.head == "hol-light:type-formed") = [typeEquation] := by rfl
private theorem list_unique :
    program.equations.filter (fun row => row.head == "hol-light:types-formed") = [listEquation] := by rfl
private theorem type_formals : typeEquation.arguments = [.var "operators", .var "type"] := by decide
private theorem list_formals : listEquation.arguments = [.var "operators", .var "types"] := by decide
private theorem type_body_shape : typeEquation.body = .expression [.symbol "case", .var "type",
    .expression (typeCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem list_body_shape : listEquation.body = .expression [.symbol "case", .var "types",
    .expression (listCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem type_cases_shape : typeCases =
    [(.expression [.symbol "Tyvar", .var "name"], .expression [.symbol "==",
       .expression [.symbol "get-type", .var "name"], .symbol "String"]),
     (.expression [.symbol "Tyapp", .var "name", .var "arguments"], operatorBody),
     (.var "malformed", boolean false)] := by decide
private theorem list_cases_shape : listCases =
    [(.symbol "HOL:Nil", boolean true),
     (.expression [.symbol "HOL:Cons", .var "first", .var "rest"], consBody),
     (.var "malformed", boolean false)] := by decide
private theorem operator_shape : operatorBody = .expression [.symbol "case",
    .expression [.symbol "hol-light:lookup", .var "name", .var "operators"],
    .expression (operatorCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem operator_cases_shape : operatorCases =
    [(.expression [.symbol "Some", .expression
       [.symbol "HOL:TypeOperator", .var "arity", .var "origin"]], registeredBody),
     (.var "unknown", boolean false)] := by decide

private theorem type_clause (operators : Atom) (type : Ty) :
    clauses program "hol-light:type-formed" [operators, typeAtom registeredOperatorAtom type] =
      [.evaluate (typeEnvironment operators type) typeEquation.body] := by
  rw [clauses_use_only_the_named_equations, type_unique]
  simp [type_formals, typeEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
private theorem list_clause (operators : Atom) (types : List Ty) :
    clauses program "hol-light:types-formed" [operators, Premises.keys (types.map (typeAtom registeredOperatorAtom))] =
      [.evaluate (listEnvironment operators types) listEquation.body] := by
  rw [clauses_use_only_the_named_equations, list_unique]
  simp [list_formals, listEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

mutual
  private theorem type_body_returns (context : DefinitionAdapters.TheoryContext)
      (table : OperatorTable.Table context) (origin : TypeOp → Atom)
      (type : Ty) (resolved : Resolved context.signature type) (state : State) :
      BoundCalls.CorePath.PureReturns program (typeEnvironment (OperatorTable.tableAtom table origin) type)
        state typeEquation.body state (boolean (typeFormedB context.signature type)) := by
    let operators := OperatorTable.tableAtom table origin
    rw [type_body_shape]
    cases type with
    | var name =>
        simp only [Resolved] at resolved
        let bound := ("name", nameAtom name) :: typeEnvironment operators (.var name)
        apply BoundCalls.CorePath.case_returns program (typeEnvironment operators (.var name)) bound state state state
          (.var "type") (typeAtom registeredOperatorAtom (.var name))
          (.expression [.symbol "==", .expression [.symbol "get-type", .var "name"], .symbol "String"])
          _ _ typeCases (read_cases_encoded typeCases)
        · exact BoundCalls.CorePath.variable_returns program _ state "type"
        · simp [type_cases_shape, bound, typeEnvironment, typeAtom,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · simp only [typeFormedB]
          apply BoundCalls.CorePath.native_binary_call_returns program bound state state state state "=="
            _ (.symbol "String") (.symbol "String") (.symbol "String") (boolean true)
            (by decide) (by decide) (by decide) (by decide)
          · apply BoundCalls.CorePath.native_variable_call_returns program bound state state "get-type" ["name"]
              (.symbol "String") (by decide) (by decide) _ (by decide)
            simp [StdLib.string_type_is_string, bound, typeEnvironment, applySubst, Subst.lookup,
              nameAtom, show name.namespaceComponents = [] from resolved]
          · exact BoundCalls.CorePath.symbol_returns program bound state "String"
          · rfl
          · decide
    | op operator arguments =>
        simp only [Resolved] at resolved
        obtain ⟨⟨arity, found⟩, argumentsResolved⟩ := resolved
        let values := arguments.map (typeAtom registeredOperatorAtom)
        let bound := [("arguments", Premises.keys values), ("name", registeredOperatorAtom operator)] ++
          typeEnvironment operators (.op operator arguments)
        apply BoundCalls.CorePath.case_returns program (typeEnvironment operators (.op operator arguments)) bound state state state
          (.var "type") (typeAtom registeredOperatorAtom (.op operator arguments)) operatorBody
          _ _ typeCases (read_cases_encoded typeCases)
        · exact BoundCalls.CorePath.variable_returns program _ state "type"
        · simp [type_cases_shape, bound, values, typeEnvironment, typeAtom,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · let registered := [("origin", origin operator), ("arity", Atom.grounded (.int arity))] ++ bound
          rw [operator_shape]
          apply BoundCalls.CorePath.case_returns program bound registered state state state
            (.expression [.symbol "hol-light:lookup", .var "name", .var "operators"])
            (.expression [.symbol "Some", .expression
              [.symbol "HOL:TypeOperator", .grounded (.int arity), origin operator]])
            registeredBody _ _ operatorCases (read_cases_encoded operatorCases)
          · have returned := Lookup.authored_lookup_certificate bound state (registeredOperatorAtom operator)
              (OperatorTable.entriesAtom table origin) "name" "operators"
              (by simp [bound, typeEnvironment, applySubst, Subst.lookup])
              (by simp [bound, typeEnvironment, operators, OperatorTable.tableAtom, applySubst, Subst.lookup])
            simpa [OperatorTable.lookup_registered table origin operator arity found, Lookup.answer] using returned
          · simp [operator_cases_shape, registered, bound, typeEnvironment,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
          · unfold registeredBody
            apply BoundCalls.CorePath.if_returns program registered state state state _ (boolean true) _ _ _
            · exact ListOperations.Validity.authored_list_valid_certificate registered state values "arguments"
                (by simp [registered, bound, typeEnvironment, applySubst, Subst.lookup])
            · simp only [boolean, BEq.rfl, ↓reduceIte]
              apply BoundCalls.CorePath.if_returns program registered state state state _ (boolean (decide (arguments.length = arity))) _ _ _
              · apply BoundCalls.CorePath.native_binary_call_returns program registered state state state state "=="
                  _ (.var "arity") (.grounded (.int arguments.length)) (.grounded (.int arity))
                  (boolean (decide (arguments.length = arity)))
                  (by decide) (by decide) (by decide) (by decide)
                · simpa [values] using ListOperations.Length.authored_length_certificate registered state values "arguments"
                    (by simp [registered, bound, typeEnvironment, applySubst, Subst.lookup])
                · simpa [registered, bound, typeEnvironment, applySubst, Subst.lookup] using
                    BoundCalls.CorePath.variable_returns program registered state "arity"
                · simp [StdLib.structural_equality, beq_eq_decide, Int.ofNat_inj]
                · decide
              · by_cases same : arguments.length = arity
                · simp only [same, decide_true, boolean, BEq.rfl, ↓reduceIte]
                  have recursive := list_body_returns context table origin arguments argumentsResolved state
                  apply BoundCalls.CorePath.authored_variable_call_returns program registered (listEnvironment operators arguments)
                    state state "hol-light:types-formed" ["operators", "arguments"] listEquation.body _
                    (by decide) (by decide) (by decide) _ _ (by decide)
                  · simpa [registered, bound, typeEnvironment, applySubst, Subst.lookup, values] using
                      list_clause operators arguments
                  · simpa [typeFormedB, found, same, boolean, operators] using recursive
                · simp only [same, decide_false, boolean]
                  simpa [typeFormedB, found, same, Ne.symm same, boolean] using
                    BoundCalls.CorePath.grounded_returns program registered state (.bool false)
  termination_by sizeOf type

  private theorem list_body_returns (context : DefinitionAdapters.TheoryContext)
      (table : OperatorTable.Table context) (origin : TypeOp → Atom)
      (types : List Ty) (resolved : ∀ type ∈ types, Resolved context.signature type) (state : State) :
      BoundCalls.CorePath.PureReturns program (listEnvironment (OperatorTable.tableAtom table origin) types)
        state listEquation.body state (boolean (types.all (typeFormedB context.signature))) := by
    let operators := OperatorTable.tableAtom table origin
    rw [list_body_shape]
    cases types with
    | nil =>
        apply BoundCalls.CorePath.case_returns program (listEnvironment operators []) (listEnvironment operators []) state state state
          (.var "types") (.symbol "HOL:Nil") (boolean true) _ _ listCases (read_cases_encoded listCases)
        · exact BoundCalls.CorePath.variable_returns program _ state "types"
        · simp [list_cases_shape, listEnvironment, Premises.keys,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · exact BoundCalls.CorePath.grounded_returns program _ state (.bool true)
    | cons first rest =>
        let bound := [("rest", Premises.keys (rest.map (typeAtom registeredOperatorAtom))),
          ("first", typeAtom registeredOperatorAtom first)] ++ listEnvironment operators (first :: rest)
        apply BoundCalls.CorePath.case_returns program (listEnvironment operators (first :: rest)) bound state state state
          (.var "types") (Premises.keys ((first :: rest).map (typeAtom registeredOperatorAtom)))
          consBody _ _ listCases (read_cases_encoded listCases)
        · exact BoundCalls.CorePath.variable_returns program _ state "types"
        · simp [list_cases_shape, bound, listEnvironment, Premises.keys,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · unfold consBody
          apply BoundCalls.CorePath.if_returns program bound state state state _ (boolean (typeFormedB context.signature first)) _ _ _
          · apply BoundCalls.CorePath.authored_variable_call_returns program bound (typeEnvironment operators first) state state
              "hol-light:type-formed" ["operators", "first"] typeEquation.body _
              (by decide) (by decide) (by decide) _
              (type_body_returns context table origin first (resolved first List.mem_cons_self) state) (by decide)
            simpa [bound, listEnvironment, applySubst, Subst.lookup] using type_clause operators first
          · cases firstFormed : typeFormedB context.signature first with
            | false =>
                simp only [boolean]
                simpa [List.all_cons, firstFormed, boolean] using
                  BoundCalls.CorePath.grounded_returns program bound state (.bool false)
            | true =>
                simp only [boolean, BEq.rfl, ↓reduceIte]
                apply BoundCalls.CorePath.authored_variable_call_returns program bound (listEnvironment operators rest) state state
                  "hol-light:types-formed" ["operators", "rest"] listEquation.body _
                  (by decide) (by decide) (by decide) _ _ (by decide)
                · simpa [bound, listEnvironment, applySubst, Subst.lookup] using list_clause operators rest
                · simpa [List.all_cons, firstFormed, boolean, operators] using list_body_returns context table origin rest
                    (fun type member => resolved type (List.mem_cons_of_mem _ member)) state
  termination_by sizeOf types
end

/-- The authored checker computes shared signature formation, including false
answers for resolved operator occurrences with incorrect arity. -/
theorem authored_type_formed_certificate (context : DefinitionAdapters.TheoryContext)
    (table : OperatorTable.Table context) (origin : TypeOp → Atom)
    (bindings : Subst) (state : State) (type : Ty) (resolved : Resolved context.signature type)
    (operatorsKey typeKey : String)
    (capturedOperators : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table origin)
    (capturedType : applySubst bindings (.var typeKey) = typeAtom registeredOperatorAtom type) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:type-formed", .var operatorsKey, .var typeKey]) state
      (boolean (typeFormedB context.signature type)) := by
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings
    (typeEnvironment (OperatorTable.tableAtom table origin) type) state state
    "hol-light:type-formed" [operatorsKey, typeKey] typeEquation.body _
    (by decide) (by decide) (by decide) _ (type_body_returns context table origin type resolved state) (by decide)
  simpa only [List.map_cons, List.map_nil, capturedOperators, capturedType] using
    type_clause (OperatorTable.tableAtom table origin) type

theorem authored_types_formed_certificate (context : DefinitionAdapters.TheoryContext)
    (table : OperatorTable.Table context) (origin : TypeOp → Atom)
    (bindings : Subst) (state : State) (types : List Ty)
    (resolved : ∀ type ∈ types, Resolved context.signature type)
    (operatorsKey typesKey : String)
    (capturedOperators : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table origin)
    (capturedTypes : applySubst bindings (.var typesKey) = Premises.keys (types.map (typeAtom registeredOperatorAtom))) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:types-formed", .var operatorsKey, .var typesKey]) state
      (boolean (types.all (typeFormedB context.signature))) := by
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings
    (listEnvironment (OperatorTable.tableAtom table origin) types) state state
    "hol-light:types-formed" [operatorsKey, typesKey] listEquation.body _
    (by decide) (by decide) (by decide) _ (list_body_returns context table origin types resolved state) (by decide)
  simpa only [List.map_cons, List.map_nil, capturedOperators, capturedTypes] using
    list_clause (OperatorTable.tableAtom table origin) types

theorem resolved_global_parameter (signature : Signature) (name : String) :
    Resolved signature (.var (Name.global name)) := by simp [Resolved, Name.global]

theorem resolved_registered_operator (signature : Signature) (operator : TypeOp) (arity : Nat)
    (arguments : List Ty) (found : signature.typeOperators operator = some arity)
    (resolved : ∀ argument ∈ arguments, Resolved signature argument) :
    Resolved signature (.op operator arguments) := by
  simp only [Resolved]
  exact ⟨⟨arity, found⟩, resolved⟩

/-- Resolving an operator does not excuse a malformed application of it. -/
theorem authored_wrong_arity_refused_certificate (context : DefinitionAdapters.TheoryContext)
    (table : OperatorTable.Table context) (origin : TypeOp → Atom)
    (bindings : Subst) (state : State) (operator : TypeOp) (arity : Nat)
    (arguments : List Ty) (found : context.signature.typeOperators operator = some arity)
    (resolved : ∀ argument ∈ arguments, Resolved context.signature argument)
    (wrong : arguments.length ≠ arity) (operatorsKey typeKey : String)
    (capturedOperators : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table origin)
    (capturedType : applySubst bindings (.var typeKey) = typeAtom registeredOperatorAtom (.op operator arguments)) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:type-formed", .var operatorsKey, .var typeKey]) state (boolean false) := by
  simpa [typeFormedB, found, wrong, Ne.symm wrong] using
    authored_type_formed_certificate context table origin bindings state (.op operator arguments)
      (resolved_registered_operator context.signature operator arity arguments found resolved)
      operatorsKey typeKey capturedOperators capturedType

/-- An absent operator is refused before its arguments can authorize anything.
No formation or resolution assumption is made about those arguments. -/
theorem authored_unknown_operator_refused_certificate (context : DefinitionAdapters.TheoryContext)
    (table : OperatorTable.Table context) (origin : TypeOp → Atom)
    (bindings : Subst) (state : State) (operator : TypeOp) (arguments : List Ty)
    (fresh : .typeOperator (DefinitionAdapters.operatorName operator) ∉ context.names)
    (operatorsKey typeKey : String)
    (capturedOperators : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table origin)
    (capturedType : applySubst bindings (.var typeKey) = typeAtom registeredOperatorAtom (.op operator arguments)) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:type-formed", .var operatorsKey, .var typeKey]) state (boolean false) := by
  let operators := OperatorTable.tableAtom table origin
  let callee := typeEnvironment operators (.op operator arguments)
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings callee state state
    "hol-light:type-formed" [operatorsKey, typeKey] typeEquation.body _
    (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, capturedOperators, capturedType] using
      type_clause operators (.op operator arguments)
  · rw [type_body_shape]
    let bound := [("arguments", Premises.keys (arguments.map (typeAtom registeredOperatorAtom))),
      ("name", registeredOperatorAtom operator)] ++ callee
    apply BoundCalls.CorePath.case_returns program callee bound state state state (.var "type")
      (typeAtom registeredOperatorAtom (.op operator arguments)) operatorBody
      _ _ typeCases (read_cases_encoded typeCases)
    · exact BoundCalls.CorePath.variable_returns program callee state "type"
    · simp [type_cases_shape, bound, callee, typeEnvironment, typeAtom,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · rw [operator_shape]
      let absent := ("unknown", Atom.symbol "None") :: bound
      apply BoundCalls.CorePath.case_returns program bound absent state state state
        (.expression [.symbol "hol-light:lookup", .var "name", .var "operators"])
        (.symbol "None") (boolean false) _ _ operatorCases (read_cases_encoded operatorCases)
      · have returned := Lookup.authored_lookup_certificate bound state (registeredOperatorAtom operator)
          (OperatorTable.entriesAtom table origin) "name" "operators"
          (by simp [bound, callee, typeEnvironment, applySubst, Subst.lookup])
          (by simp [bound, callee, typeEnvironment, operators, OperatorTable.tableAtom, applySubst, Subst.lookup])
        simpa [OperatorTable.fresh_name_absent table origin operator fresh, Lookup.answer] using returned
      · simp [operator_cases_shape, absent, bound, callee, typeEnvironment,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
      · exact BoundCalls.CorePath.grounded_returns program absent state (.bool false)


theorem authored_type_formed_return (context : DefinitionAdapters.TheoryContext)
    (table : OperatorTable.Table context) (origin : TypeOp → Atom)
    (bindings : Subst) (state : State) (type : Ty) (resolved : Resolved context.signature type)
    (operatorsKey typeKey : String)
    (capturedOperators : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table origin)
    (capturedType : applySubst bindings (.var typeKey) = typeAtom registeredOperatorAtom type) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:type-formed", .var operatorsKey, .var typeKey]) state
      (boolean (typeFormedB context.signature type)) :=
  (authored_type_formed_certificate context table origin bindings state type resolved operatorsKey typeKey capturedOperators capturedType).original

theorem authored_type_formed_bound_return (context : DefinitionAdapters.TheoryContext)
    (table : OperatorTable.Table context) (origin : TypeOp → Atom)
    (bindings : Subst) (state : State) (type : Ty) (resolved : Resolved context.signature type)
    (operatorsKey typeKey : String)
    (capturedOperators : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table origin)
    (capturedType : applySubst bindings (.var typeKey) = typeAtom registeredOperatorAtom type) :
    BoundCalls.PureReturns program bindings state
      (.expression [.symbol "hol-light:type-formed", .var operatorsKey, .var typeKey]) state
      (boolean (typeFormedB context.signature type)) :=
  (authored_type_formed_certificate context table origin bindings state type resolved operatorsKey typeKey capturedOperators capturedType).extended

theorem authored_types_formed_return (context : DefinitionAdapters.TheoryContext)
    (table : OperatorTable.Table context) (origin : TypeOp → Atom)
    (bindings : Subst) (state : State) (types : List Ty)
    (resolved : ∀ type ∈ types, Resolved context.signature type)
    (operatorsKey typesKey : String)
    (capturedOperators : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table origin)
    (capturedTypes : applySubst bindings (.var typesKey) = Premises.keys (types.map (typeAtom registeredOperatorAtom))) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:types-formed", .var operatorsKey, .var typesKey]) state
      (boolean (types.all (typeFormedB context.signature))) :=
  (authored_types_formed_certificate context table origin bindings state types resolved operatorsKey typesKey capturedOperators capturedTypes).original

theorem authored_types_formed_bound_return (context : DefinitionAdapters.TheoryContext)
    (table : OperatorTable.Table context) (origin : TypeOp → Atom)
    (bindings : Subst) (state : State) (types : List Ty)
    (resolved : ∀ type ∈ types, Resolved context.signature type)
    (operatorsKey typesKey : String)
    (capturedOperators : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table origin)
    (capturedTypes : applySubst bindings (.var typesKey) = Premises.keys (types.map (typeAtom registeredOperatorAtom))) :
    BoundCalls.PureReturns program bindings state
      (.expression [.symbol "hol-light:types-formed", .var operatorsKey, .var typesKey]) state
      (boolean (types.all (typeFormedB context.signature))) :=
  (authored_types_formed_certificate context table origin bindings state types resolved operatorsKey typesKey capturedOperators capturedTypes).extended

theorem authored_wrong_arity_refused (context : DefinitionAdapters.TheoryContext)
    (table : OperatorTable.Table context) (origin : TypeOp → Atom)
    (bindings : Subst) (state : State) (operator : TypeOp) (arity : Nat)
    (arguments : List Ty) (found : context.signature.typeOperators operator = some arity)
    (resolved : ∀ argument ∈ arguments, Resolved context.signature argument)
    (wrong : arguments.length ≠ arity) (operatorsKey typeKey : String)
    (capturedOperators : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table origin)
    (capturedType : applySubst bindings (.var typeKey) = typeAtom registeredOperatorAtom (.op operator arguments)) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:type-formed", .var operatorsKey, .var typeKey]) state (boolean false) :=
  (authored_wrong_arity_refused_certificate context table origin bindings state operator arity arguments found resolved wrong operatorsKey typeKey capturedOperators capturedType).original

theorem authored_wrong_arity_bound_refused (context : DefinitionAdapters.TheoryContext)
    (table : OperatorTable.Table context) (origin : TypeOp → Atom)
    (bindings : Subst) (state : State) (operator : TypeOp) (arity : Nat)
    (arguments : List Ty) (found : context.signature.typeOperators operator = some arity)
    (resolved : ∀ argument ∈ arguments, Resolved context.signature argument)
    (wrong : arguments.length ≠ arity) (operatorsKey typeKey : String)
    (capturedOperators : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table origin)
    (capturedType : applySubst bindings (.var typeKey) = typeAtom registeredOperatorAtom (.op operator arguments)) :
    BoundCalls.PureReturns program bindings state
      (.expression [.symbol "hol-light:type-formed", .var operatorsKey, .var typeKey]) state (boolean false) :=
  (authored_wrong_arity_refused_certificate context table origin bindings state operator arity arguments found resolved wrong operatorsKey typeKey capturedOperators capturedType).extended

theorem authored_unknown_operator_refused (context : DefinitionAdapters.TheoryContext)
    (table : OperatorTable.Table context) (origin : TypeOp → Atom)
    (bindings : Subst) (state : State) (operator : TypeOp) (arguments : List Ty)
    (fresh : .typeOperator (DefinitionAdapters.operatorName operator) ∉ context.names)
    (operatorsKey typeKey : String)
    (capturedOperators : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table origin)
    (capturedType : applySubst bindings (.var typeKey) = typeAtom registeredOperatorAtom (.op operator arguments)) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:type-formed", .var operatorsKey, .var typeKey]) state (boolean false) :=
  (authored_unknown_operator_refused_certificate context table origin bindings state operator arguments fresh operatorsKey typeKey capturedOperators capturedType).original

theorem authored_unknown_operator_bound_refused (context : DefinitionAdapters.TheoryContext)
    (table : OperatorTable.Table context) (origin : TypeOp → Atom)
    (bindings : Subst) (state : State) (operator : TypeOp) (arguments : List Ty)
    (fresh : .typeOperator (DefinitionAdapters.operatorName operator) ∉ context.names)
    (operatorsKey typeKey : String)
    (capturedOperators : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table origin)
    (capturedType : applySubst bindings (.var typeKey) = typeAtom registeredOperatorAtom (.op operator arguments)) :
    BoundCalls.PureReturns program bindings state
      (.expression [.symbol "hol-light:type-formed", .var operatorsKey, .var typeKey]) state (boolean false) :=
  (authored_unknown_operator_refused_certificate context table origin bindings state operator arguments fresh operatorsKey typeKey capturedOperators capturedType).extended

end Mettapedia.Languages.HOLLight.MeTTa.TypeFormation
