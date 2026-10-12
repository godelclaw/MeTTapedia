import Mettapedia.Languages.HOLLight.MeTTa.Lookup
import Mettapedia.Languages.HOLLight.SourceSubstitution

/-!
# HOL Light type substitution executed by its authored MeTTa library

The substitution is the existing shared HOL source operation. Its representation
keeps global source names as strings and distinguishes qualified names. Operator
payloads are supplied by the declared context: substitution retains them without
interpreting them. The execution laws concern the actual retained library bodies.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.TypeSubstitution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory (Name Ty TypeOp)
open Eval
open Effects (State boolean)

/-- Flat source names have the source's string representation. Other namespaces
have a disjoint data representation and cannot collide with flat names. -/
def nameAtom (name : Name) : Atom :=
  if name.namespaceComponents = [] then .grounded (.string name.component)
  else .expression [.symbol "HOL:QualifiedName",
    .expression (name.namespaceComponents.map fun part => .grounded (.string part)),
    .grounded (.string name.component)]

theorem nameAtom_injective : Function.Injective nameAtom := by
  intro left right same
  rcases left with ⟨leftSpace, leftName⟩
  rcases right with ⟨rightSpace, rightName⟩
  have textInjective : Function.Injective (fun part : String => Atom.grounded (.string part)) := by
    intro first second equal
    simpa using equal
  cases leftSpace <;> cases rightSpace <;> simp [nameAtom] at same ⊢
  · exact same
  · obtain ⟨spaces, names⟩ := same
    exact ⟨⟨spaces.1, (List.map_inj_right (fun _ _ equal => textInjective equal)).mp spaces.2⟩, names⟩

@[simp] theorem nameAtom_global (name : String) :
    nameAtom (Name.global name) = .grounded (.string name) := rfl

/-- The context resolves operator identity. This operation only moves the
chosen payload intact; it does not authorize a type or a declaration. -/
def typeAtom (operatorAtom : TypeOp → Atom) : Ty → Atom
  | .var name => .expression [.symbol "Tyvar", nameAtom name]
  | .op operator arguments => .expression [.symbol "Tyapp", operatorAtom operator,
      Premises.keys (arguments.map (typeAtom operatorAtom))]
termination_by type => sizeOf type

def maplets (operatorAtom : TypeOp → Atom) (entries : List (Ty × Ty)) : Atom :=
  Premises.keys (entries.map fun entry => .expression [.symbol "HOL:Maplet",
    typeAtom operatorAtom entry.1, typeAtom operatorAtom entry.2])

private def equation : SpaceSemantics.Equation :=
  (dataSource.program.equations.filter
    (fun row => row.head == "hol-light:type-replacement"))[0]'(by decide)

private def outerCases : SpaceSemantics.Cases :=
  match equation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def consBody : Atom :=
  .expression [.symbol "case", .var "key", .expression
    [.expression [.expression [.symbol "Tyvar", .var "candidate"],
      .expression [.symbol "if", .expression [.symbol "==", .var "candidate", .var "name"],
        .var "replacement", .expression [.symbol "hol-light:type-replacement", .var "name", .var "rest"]]],
     .expression [.var "ignored",
       .expression [.symbol "hol-light:type-replacement", .var "name", .var "rest"]]]]

private def innerCases : SpaceSemantics.Cases :=
  match consBody with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def variableBody : Atom :=
  .expression [.symbol "if", .expression [.symbol "==", .var "candidate", .var "name"],
    .var "replacement", .expression [.symbol "hol-light:type-replacement", .var "name", .var "rest"]]

private def environment (operatorAtom : TypeOp → Atom) (name : Name) (entries : List (Ty × Ty)) : Subst :=
  [("entries", maplets operatorAtom entries), ("name", nameAtom name)]

private def consEnvironment (operatorAtom : TypeOp → Atom) (name : Name)
    (replacement key : Ty) (rest : List (Ty × Ty)) : Subst :=
  [("rest", maplets operatorAtom rest), ("key", typeAtom operatorAtom key),
    ("replacement", typeAtom operatorAtom replacement)] ++
      environment operatorAtom name ((replacement, key) :: rest)

private theorem equation_unique :
    program.equations.filter (fun row => row.head == "hol-light:type-replacement") = [equation] := by rfl

private theorem formals : equation.arguments = [.var "name", .var "entries"] := by decide

private theorem body_shape : equation.body =
    .expression [.symbol "case", .var "entries",
      .expression (outerCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem outer_shape : outerCases =
    [(.symbol "HOL:Nil", .expression [.symbol "Tyvar", .var "name"]),
     (.expression [.symbol "HOL:Cons",
       .expression [.symbol "HOL:Maplet", .var "replacement", .var "key"], .var "rest"], consBody),
     (.var "malformed", .symbol "None")] := by decide

private theorem inner_shape : innerCases =
    [(.expression [.symbol "Tyvar", .var "candidate"], variableBody),
     (.var "ignored", .expression [.symbol "hol-light:type-replacement", .var "name", .var "rest"])] := by decide

private theorem cons_shape : consBody =
    .expression [.symbol "case", .var "key",
      .expression (innerCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem clause (operatorAtom : TypeOp → Atom) (name : Name) (entries : List (Ty × Ty)) :
    clauses program "hol-light:type-replacement" [nameAtom name, maplets operatorAtom entries] =
      [.evaluate (environment operatorAtom name entries) equation.body] := by
  rw [clauses_use_only_the_named_equations, equation_unique]
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_returns (operatorAtom : TypeOp → Atom) (name : Name)
    (entries : List (Ty × Ty)) (state : State) :
    PureReturns program (environment operatorAtom name entries) state equation.body state
      (typeAtom operatorAtom (SourceSubstitution.variableType entries name)) := by
  induction entries with
  | nil =>
      rw [body_shape]
      apply case_returns program (environment operatorAtom name [])
        (environment operatorAtom name []) state state state
        (.var "entries") (.symbol "HOL:Nil") (.expression [.symbol "Tyvar", .var "name"])
        _ _ outerCases (read_cases_encoded outerCases)
      · exact variable_returns program _ state "entries"
      · simp [outer_shape, environment, maplets, Premises.keys,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [SourceSubstitution.variableType, typeAtom, environment, applySubst, Subst.lookup] using
          unary_constructor_returns program (environment operatorAtom name []) state
            "Tyvar" "name" (by decide) (by decide)
  | cons entry rest ih =>
      rcases entry with ⟨replacement, key⟩
      rw [body_shape]
      apply case_returns program (environment operatorAtom name ((replacement, key) :: rest))
        (consEnvironment operatorAtom name replacement key rest) state state state
        (.var "entries") (maplets operatorAtom ((replacement, key) :: rest)) consBody _ _
        outerCases (read_cases_encoded outerCases)
      · exact variable_returns program _ state "entries"
      · simp [outer_shape, environment, consEnvironment, maplets, Premises.keys,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · rw [cons_shape]
        cases key with
        | var candidate =>
            let bound := ("candidate", nameAtom candidate) ::
              consEnvironment operatorAtom name replacement (.var candidate) rest
            apply case_returns program (consEnvironment operatorAtom name replacement (.var candidate) rest)
              bound state state state (.var "key") (typeAtom operatorAtom (.var candidate))
              variableBody _ _ innerCases (read_cases_encoded innerCases)
            · exact variable_returns program _ state "key"
            · simp [inner_shape, bound, consEnvironment, typeAtom,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, environment]
            · unfold variableBody
              apply if_returns program bound state state state
                (.expression [.symbol "==", .var "candidate", .var "name"])
                (boolean (decide (candidate = name))) _ _ _
              · apply native_variable_call_returns program bound state state "=="
                  ["candidate", "name"] _ (by decide) (by decide) _ (by decide)
                have comparison : (nameAtom candidate == nameAtom name) = decide (candidate = name) := by
                  simp only [beq_eq_decide, nameAtom_injective.eq_iff]
                simp [StdLib.structural_equality, bound, consEnvironment, environment, applySubst, Subst.lookup, comparison]
              · by_cases same : candidate = name
                · simpa [same, boolean, SourceSubstitution.variableType, bound, consEnvironment,
                    environment, applySubst, Subst.lookup] using variable_returns program bound state "replacement"
                · simp only [same, decide_false, boolean]
                  apply authored_variable_call_returns program bound
                    (environment operatorAtom name rest) state state "hol-light:type-replacement"
                    ["name", "rest"] equation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
                  · simpa [bound, consEnvironment, environment, applySubst, Subst.lookup] using
                      clause operatorAtom name rest
                  · simpa [SourceSubstitution.variableType, Ne.symm same] using ih
        | op operator arguments =>
            let bound := ("ignored", typeAtom operatorAtom (.op operator arguments)) ::
              consEnvironment operatorAtom name replacement (.op operator arguments) rest
            apply case_returns program (consEnvironment operatorAtom name replacement (.op operator arguments) rest)
              bound state state state (.var "key") (typeAtom operatorAtom (.op operator arguments))
              (.expression [.symbol "hol-light:type-replacement", .var "name", .var "rest"])
              _ _ innerCases (read_cases_encoded innerCases)
            · exact variable_returns program _ state "key"
            · simp [inner_shape, bound, consEnvironment, typeAtom,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, environment]
            · apply authored_variable_call_returns program bound (environment operatorAtom name rest)
                state state "hol-light:type-replacement" ["name", "rest"] equation.body _
                (by decide) (by decide) (by decide) _ _ (by decide)
              · simpa [bound, consEnvironment, environment, applySubst, Subst.lookup] using
                  clause operatorAtom name rest
              · simpa [SourceSubstitution.variableType] using ih

/-- The actual authored helper implements the shared source's first-match
operation, including duplicate and ignored non-variable keys. -/
theorem authored_replacement_return (operatorAtom : TypeOp → Atom) (bindings : Subst)
    (state : State) (entries : List (Ty × Ty)) (name : Name) (nameKey entriesKey : String)
    (capturedName : applySubst bindings (.var nameKey) = nameAtom name)
    (capturedEntries : applySubst bindings (.var entriesKey) = maplets operatorAtom entries) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:type-replacement", .var nameKey, .var entriesKey]) state
      (typeAtom operatorAtom (SourceSubstitution.variableType entries name)) := by
  apply authored_variable_call_returns program bindings (environment operatorAtom name entries)
    state state "hol-light:type-replacement" [nameKey, entriesKey] equation.body _
    (by decide) (by decide) (by decide) _ (body_returns operatorAtom name entries state) (by decide)
  simpa only [List.map_cons, List.map_nil, capturedName, capturedEntries] using
    clause operatorAtom name entries

private def typeEquation : SpaceSemantics.Equation :=
  (dataSource.program.equations.filter
    (fun row => row.head == "hol-light:type-subst"))[0]'(by decide)

private def listEquation : SpaceSemantics.Equation :=
  (dataSource.program.equations.filter
    (fun row => row.head == "hol-light:type-subst-list"))[0]'(by decide)

private def typeCases : SpaceSemantics.Cases :=
  match typeEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def listCases : SpaceSemantics.Cases :=
  match listEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def typeVariableBody : Atom :=
  .expression [.symbol "hol-light:type-replacement", .var "name", .var "entries"]

private def typeOperatorBody : Atom :=
  .expression [.symbol "Tyapp", .var "operator",
    .expression [.symbol "hol-light:type-subst-list", .var "entries", .var "arguments"]]

private def listConsBody : Atom :=
  .expression [.symbol "HOL:Cons",
    .expression [.symbol "hol-light:type-subst", .var "entries", .var "first"],
    .expression [.symbol "hol-light:type-subst-list", .var "entries", .var "rest"]]

private def typeEnvironment (operatorAtom : TypeOp → Atom) (entries : List (Ty × Ty))
    (type : Ty) : Subst :=
  [("type", typeAtom operatorAtom type), ("entries", maplets operatorAtom entries)]

private def listEnvironment (operatorAtom : TypeOp → Atom) (entries : List (Ty × Ty))
    (types : List Ty) : Subst :=
  [("types", Premises.keys (types.map (typeAtom operatorAtom))), ("entries", maplets operatorAtom entries)]

private theorem typeEquation_unique :
    program.equations.filter (fun row => row.head == "hol-light:type-subst") = [typeEquation] := by rfl

private theorem listEquation_unique :
    program.equations.filter (fun row => row.head == "hol-light:type-subst-list") = [listEquation] := by rfl

private theorem type_formals : typeEquation.arguments = [.var "entries", .var "type"] := by decide

private theorem list_formals : listEquation.arguments = [.var "entries", .var "types"] := by decide

private theorem type_body_shape : typeEquation.body =
    .expression [.symbol "case", .var "type",
      .expression (typeCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem list_body_shape : listEquation.body =
    .expression [.symbol "case", .var "types",
      .expression (listCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem type_cases_shape : typeCases =
    [(.expression [.symbol "Tyvar", .var "name"], typeVariableBody),
     (.expression [.symbol "Tyapp", .var "operator", .var "arguments"], typeOperatorBody),
     (.var "malformed", .symbol "None")] := by decide

private theorem list_cases_shape : listCases =
    [(.symbol "HOL:Nil", .symbol "HOL:Nil"),
     (.expression [.symbol "HOL:Cons", .var "first", .var "rest"], listConsBody),
     (.var "malformed", .symbol "None")] := by decide

private theorem type_clause (operatorAtom : TypeOp → Atom) (entries : List (Ty × Ty)) (type : Ty) :
    clauses program "hol-light:type-subst" [maplets operatorAtom entries, typeAtom operatorAtom type] =
      [.evaluate (typeEnvironment operatorAtom entries type) typeEquation.body] := by
  rw [clauses_use_only_the_named_equations, typeEquation_unique]
  simp [type_formals, typeEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem list_clause (operatorAtom : TypeOp → Atom) (entries : List (Ty × Ty)) (types : List Ty) :
    clauses program "hol-light:type-subst-list"
      [maplets operatorAtom entries, Premises.keys (types.map (typeAtom operatorAtom))] =
      [.evaluate (listEnvironment operatorAtom entries types) listEquation.body] := by
  rw [clauses_use_only_the_named_equations, listEquation_unique]
  simp [list_formals, listEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

mutual
  private theorem type_body_returns (operatorAtom : TypeOp → Atom)
      (entries : List (Ty × Ty)) (type : Ty) (state : State) :
      PureReturns program (typeEnvironment operatorAtom entries type) state typeEquation.body state
        (typeAtom operatorAtom (SourceSubstitution.typeAction entries type)) := by
    rw [type_body_shape]
    cases type with
    | var name =>
        let bound := ("name", nameAtom name) :: typeEnvironment operatorAtom entries (.var name)
        apply case_returns program (typeEnvironment operatorAtom entries (.var name)) bound
          state state state (.var "type") (typeAtom operatorAtom (.var name)) typeVariableBody
          _ _ typeCases (read_cases_encoded typeCases)
        · exact variable_returns program _ state "type"
        · simp [type_cases_shape, bound, typeEnvironment, typeAtom,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · unfold typeVariableBody
          simpa only [SourceSubstitution.typeAction] using
            authored_replacement_return operatorAtom bound state entries name "name" "entries"
              (by simp [bound, typeEnvironment, applySubst, Subst.lookup])
              (by simp [bound, typeEnvironment, applySubst, Subst.lookup])
    | op operator arguments =>
        let bound := [("arguments", Premises.keys (arguments.map (typeAtom operatorAtom))),
            ("operator", operatorAtom operator)] ++ typeEnvironment operatorAtom entries (.op operator arguments)
        apply case_returns program (typeEnvironment operatorAtom entries (.op operator arguments)) bound
          state state state (.var "type") (typeAtom operatorAtom (.op operator arguments)) typeOperatorBody
          _ _ typeCases (read_cases_encoded typeCases)
        · exact variable_returns program _ state "type"
        · simp [type_cases_shape, bound, typeEnvironment, typeAtom,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · simp only [SourceSubstitution.typeAction, typeAtom]
          unfold typeOperatorBody
          apply binary_constructor_returns program bound state state state "Tyapp"
            (.var "operator")
            (.expression [.symbol "hol-light:type-subst-list", .var "entries", .var "arguments"])
            (operatorAtom operator)
            (Premises.keys ((arguments.map (SourceSubstitution.typeAction entries)).map (typeAtom operatorAtom)))
            (by decide) (by decide)
          · simpa [bound, typeEnvironment, applySubst, Subst.lookup] using
              variable_returns program bound state "operator"
          · apply authored_variable_call_returns program bound
              (listEnvironment operatorAtom entries arguments) state state "hol-light:type-subst-list"
              ["entries", "arguments"] listEquation.body _ (by decide) (by decide) (by decide)
              _ (list_body_returns operatorAtom entries arguments state) (by decide)
            simpa [bound, typeEnvironment, applySubst, Subst.lookup] using
              list_clause operatorAtom entries arguments
  termination_by sizeOf type

  private theorem list_body_returns (operatorAtom : TypeOp → Atom)
      (entries : List (Ty × Ty)) (types : List Ty) (state : State) :
      PureReturns program (listEnvironment operatorAtom entries types) state listEquation.body state
        (Premises.keys ((types.map (SourceSubstitution.typeAction entries)).map (typeAtom operatorAtom))) := by
    rw [list_body_shape]
    cases types with
    | nil =>
        apply case_returns program (listEnvironment operatorAtom entries [])
          (listEnvironment operatorAtom entries []) state state state (.var "types")
          (.symbol "HOL:Nil") (.symbol "HOL:Nil") _ _ listCases (read_cases_encoded listCases)
        · exact variable_returns program _ state "types"
        · simp [list_cases_shape, listEnvironment, Premises.keys,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · exact symbol_returns program _ state "HOL:Nil"
    | cons first rest =>
        let bound := [("rest", Premises.keys (rest.map (typeAtom operatorAtom))),
            ("first", typeAtom operatorAtom first)] ++ listEnvironment operatorAtom entries (first :: rest)
        apply case_returns program (listEnvironment operatorAtom entries (first :: rest)) bound
          state state state (.var "types") (Premises.keys ((first :: rest).map (typeAtom operatorAtom)))
          listConsBody _ _ listCases (read_cases_encoded listCases)
        · exact variable_returns program _ state "types"
        · simp [list_cases_shape, bound, listEnvironment, Premises.keys,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · simp only [List.map_cons, Premises.keys]
          unfold listConsBody
          apply binary_constructor_returns program bound state state state "HOL:Cons"
            (.expression [.symbol "hol-light:type-subst", .var "entries", .var "first"])
            (.expression [.symbol "hol-light:type-subst-list", .var "entries", .var "rest"])
            (typeAtom operatorAtom (SourceSubstitution.typeAction entries first))
            (Premises.keys ((rest.map (SourceSubstitution.typeAction entries)).map (typeAtom operatorAtom)))
            (by decide) (by decide)
          · apply authored_variable_call_returns program bound
              (typeEnvironment operatorAtom entries first) state state "hol-light:type-subst"
              ["entries", "first"] typeEquation.body _ (by decide) (by decide) (by decide)
              _ (type_body_returns operatorAtom entries first state) (by decide)
            simpa [bound, listEnvironment, applySubst, Subst.lookup] using
              type_clause operatorAtom entries first
          · apply authored_variable_call_returns program bound
              (listEnvironment operatorAtom entries rest) state state "hol-light:type-subst-list"
              ["entries", "rest"] listEquation.body _ (by decide) (by decide) (by decide)
              _ (list_body_returns operatorAtom entries rest state) (by decide)
            simpa [bound, listEnvironment, applySubst, Subst.lookup] using
              list_clause operatorAtom entries rest
  termination_by sizeOf types
end

/-- Arbitrary finite type trees and maplet lists are executed by the authored
program with exactly the shared HOL Light simultaneous substitution action. -/
theorem authored_type_substitution_return (operatorAtom : TypeOp → Atom) (bindings : Subst)
    (state : State) (entries : List (Ty × Ty)) (type : Ty) (entriesKey typeKey : String)
    (capturedEntries : applySubst bindings (.var entriesKey) = maplets operatorAtom entries)
    (capturedType : applySubst bindings (.var typeKey) = typeAtom operatorAtom type) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:type-subst", .var entriesKey, .var typeKey]) state
      (typeAtom operatorAtom ((SourceSubstitution.typeSubstitution entries).apply type)) := by
  rw [SourceSubstitution.apply_type]
  apply authored_variable_call_returns program bindings (typeEnvironment operatorAtom entries type)
    state state "hol-light:type-subst" [entriesKey, typeKey] typeEquation.body _
    (by decide) (by decide) (by decide) _ (type_body_returns operatorAtom entries type state) (by decide)
  simpa only [List.map_cons, List.map_nil, capturedEntries, capturedType] using
    type_clause operatorAtom entries type

end Mettapedia.Languages.HOLLight.MeTTa.TypeSubstitution
