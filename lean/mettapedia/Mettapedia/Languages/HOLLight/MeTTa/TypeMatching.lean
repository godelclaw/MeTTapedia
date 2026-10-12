import Mettapedia.Languages.HOLLight.MeTTa.TypeFormation
import Mettapedia.Languages.HOLLight.TypeMatching

/-!
# Polymorphic schema matching executed by the authored library

The source's two mutually recursive equations implement matching over the
existing shared HOL substitution. The source table and all declaration
identities are retained. The selected signature supplies the faithfulness
needed to compare registered operators and replacement types.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.TypeMatching

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open SignatureFormation
open Eval
open Effects (State boolean)
open TypeSubstitution (nameAtom typeAtom)
open Representation (registeredOperatorAtom)
open Mettapedia.Languages.HOLLight.TypeMatching

def entriesAtom (assignments : TypeSubst) : List (Atom × Atom) :=
  assignments.entries.map fun entry => (nameAtom entry.1, typeAtom registeredOperatorAtom entry.2)

def assignmentsAtom (assignments : TypeSubst) : Atom := Lookup.table (entriesAtom assignments)

def answer (result : Option TypeSubst) : Atom := Lookup.answer (result.map assignmentsAtom)

theorem encoded_lookup (assignments : TypeSubst) (name : Name) :
    (entriesAtom assignments).lookup (nameAtom name) =
      (assignments.lookup name).map (typeAtom registeredOperatorAtom) := by
  rcases assignments with ⟨entries⟩
  induction entries with
  | nil => rfl
  | cons first rest ih =>
      rcases first with ⟨key, value⟩
      by_cases same : name = key
      · simp [entriesAtom, TypeSubst.lookup, List.lookup, same]
      · simpa [entriesAtom, TypeSubst.lookup, List.lookup, beq_eq_decide,
          TypeSubstitution.nameAtom_injective.eq_iff, same] using ih

private def typeEquation : SpaceSemantics.Equation :=
  (syntaxSource.program.equations.filter
    (fun row => row.head == "hol-light:type-match"))[0]'(by decide)
private def listEquation : SpaceSemantics.Equation :=
  (syntaxSource.program.equations.filter
    (fun row => row.head == "hol-light:type-match-list"))[0]'(by decide)

private def typeCases : SpaceSemantics.Cases :=
  match typeEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def listCases : SpaceSemantics.Cases :=
  match listEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def newAssignmentBody : Atom := .expression [.symbol "Some", .expression
  [.symbol "HOL:Cons", .expression [.symbol "HOL:Entry", .var "name", .var "instance"],
    .var "assignments"]]
private def previousBody : Atom := .expression [.symbol "if",
  .expression [.symbol "==", .var "previous", .var "instance"],
  .expression [.symbol "Some", .var "assignments"], .symbol "None"]
private def variableBody : Atom := .expression [.symbol "case",
  .expression [.symbol "hol-light:lookup", .var "name", .var "assignments"], .expression
    [.expression [.symbol "None", newAssignmentBody],
     .expression [.expression [.symbol "Some", .var "previous"], previousBody],
     .expression [.var "malformed", .symbol "None"]]]
private def operatorSelected : Atom := .expression [.symbol "if",
  .expression [.symbol "==", .var "operator", .var "target"],
  .expression [.symbol "hol-light:type-match-list", .var "arguments", .var "values",
    .var "assignments"], .symbol "None"]
private def operatorBody : Atom := .expression [.symbol "case", .var "instance", .expression
  [.expression [.expression [.symbol "Tyapp", .var "target", .var "values"], operatorSelected],
   .expression [.var "malformed", .symbol "None"]]]
private def consBody : Atom := .expression [.symbol "case",
  .expression [.symbol "hol-light:type-match", .var "first", .var "value", .var "assignments"],
  .expression [.expression [.expression [.symbol "Some", .var "next"],
    .expression [.symbol "hol-light:type-match-list", .var "rest", .var "values", .var "next"]],
    .expression [.var "malformed", .symbol "None"]]]

private def rows (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression cases] => (readCases cases).getD []
  | _ => []

private def typeEnvironment (schema occurrence : Ty) (assignments : TypeSubst) : Subst :=
  [("assignments", assignmentsAtom assignments), ("instance", typeAtom registeredOperatorAtom occurrence),
    ("schema", typeAtom registeredOperatorAtom schema)]
private def listEnvironment (schemas occurrences : List Ty) (assignments : TypeSubst) : Subst :=
  [("assignments", assignmentsAtom assignments),
    ("instances", Premises.keys (occurrences.map (typeAtom registeredOperatorAtom))),
    ("schemas", Premises.keys (schemas.map (typeAtom registeredOperatorAtom)))]

private theorem type_unique :
    program.equations.filter (fun row => row.head == "hol-light:type-match") = [typeEquation] := by rfl
private theorem list_unique :
    program.equations.filter (fun row => row.head == "hol-light:type-match-list") = [listEquation] := by rfl
private theorem type_formals :
    typeEquation.arguments = [.var "schema", .var "instance", .var "assignments"] := by decide
private theorem list_formals :
    listEquation.arguments = [.var "schemas", .var "instances", .var "assignments"] := by decide
private theorem type_body_shape : typeEquation.body = .expression [.symbol "case", .var "schema",
    .expression (typeCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem list_body_shape : listEquation.body = .expression [.symbol "case",
    .expression [.var "schemas", .var "instances"],
    .expression (listCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem type_cases_shape : typeCases =
    [(.expression [.symbol "Tyvar", .var "name"], variableBody),
     (.expression [.symbol "Tyapp", .var "operator", .var "arguments"], operatorBody),
     (.var "malformed", .symbol "None")] := by decide
private theorem list_cases_shape : listCases =
    [(.expression [.symbol "HOL:Nil", .symbol "HOL:Nil"],
        .expression [.symbol "Some", .var "assignments"]),
     (.expression [.expression [.symbol "HOL:Cons", .var "first", .var "rest"],
        .expression [.symbol "HOL:Cons", .var "value", .var "values"]], consBody),
     (.var "malformed", .symbol "None")] := by decide
private theorem variable_rows : rows variableBody =
    [(.symbol "None", newAssignmentBody),
     (.expression [.symbol "Some", .var "previous"], previousBody),
     (.var "malformed", .symbol "None")] := by decide
private theorem operator_rows : rows operatorBody =
    [(.expression [.symbol "Tyapp", .var "target", .var "values"], operatorSelected),
     (.var "malformed", .symbol "None")] := by decide
private theorem cons_rows : rows consBody =
    [(.expression [.symbol "Some", .var "next"],
      .expression [.symbol "hol-light:type-match-list", .var "rest", .var "values", .var "next"]),
     (.var "malformed", .symbol "None")] := by decide
private theorem variable_shape : variableBody = .expression [.symbol "case",
    .expression [.symbol "hol-light:lookup", .var "name", .var "assignments"],
    .expression ((rows variableBody).map fun row => .expression [row.1, row.2])] := by decide
private theorem operator_shape : operatorBody = .expression [.symbol "case", .var "instance",
    .expression ((rows operatorBody).map fun row => .expression [row.1, row.2])] := by decide
private theorem cons_shape : consBody = .expression [.symbol "case",
    .expression [.symbol "hol-light:type-match", .var "first", .var "value", .var "assignments"],
    .expression ((rows consBody).map fun row => .expression [row.1, row.2])] := by decide

private theorem type_clause (schema occurrence : Ty) (assignments : TypeSubst) :
    clauses program "hol-light:type-match"
      [typeAtom registeredOperatorAtom schema, typeAtom registeredOperatorAtom occurrence,
        assignmentsAtom assignments] =
      [.evaluate (typeEnvironment schema occurrence assignments) typeEquation.body] := by
  rw [clauses_use_only_the_named_equations, type_unique]
  simp [type_formals, typeEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
private theorem list_clause (schemas occurrences : List Ty) (assignments : TypeSubst) :
    clauses program "hol-light:type-match-list"
      [Premises.keys (schemas.map (typeAtom registeredOperatorAtom)),
        Premises.keys (occurrences.map (typeAtom registeredOperatorAtom)), assignmentsAtom assignments] =
      [.evaluate (listEnvironment schemas occurrences assignments) listEquation.body] := by
  rw [clauses_use_only_the_named_equations, list_unique]
  simp [list_formals, listEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem new_assignment_return (bindings : Subst) (state : State)
    (name : Name) (occurrence : Ty) (assignments : TypeSubst)
    (nameFound : applySubst bindings (.var "name") = nameAtom name)
    (instanceFound : applySubst bindings (.var "instance") = typeAtom registeredOperatorAtom occurrence)
    (assignmentsFound : applySubst bindings (.var "assignments") = assignmentsAtom assignments) :
    BoundCalls.CorePath.PureReturns program bindings state newAssignmentBody state
      (answer (some ⟨(name, occurrence) :: assignments.entries⟩)) := by
  simp only [answer, Option.map_some, Lookup.answer, assignmentsAtom, entriesAtom,
    List.map_cons, Lookup.table, Premises.keys]
  unfold newAssignmentBody
  apply BoundCalls.CorePath.unary_constructor_of_returns program bindings state state "Some" _ _ (by decide) (by decide)
  apply BoundCalls.CorePath.binary_constructor_returns program bindings state state state "HOL:Cons" _ _ _ _
    (by decide) (by decide)
  · simpa only [List.map_cons, List.map_nil, nameFound, instanceFound] using
      BoundCalls.CorePath.constructor_variables_return program bindings state "HOL:Entry" ["name", "instance"]
        (by decide) (by decide)
  · simpa [assignmentsFound, assignmentsAtom, Lookup.table, entriesAtom, List.map_map] using BoundCalls.CorePath.variable_returns program bindings state "assignments"

private theorem type_comparison (context : DefinitionAdapters.TheoryContext) (left right : Ty)
    (leftFormed : TypeFormed context.signature left) (rightFormed : TypeFormed context.signature right) :
    (typeAtom registeredOperatorAtom left == typeAtom registeredOperatorAtom right) = Ty.same left right := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, Ty.same_eq_true_iff]
  exact ⟨Representation.registered_typeAtom_injective context left right leftFormed rightFormed,
    fun same => congrArg (typeAtom registeredOperatorAtom) same⟩

private theorem operator_comparison (context : DefinitionAdapters.TheoryContext)
    (left right : TypeOp) (leftArity rightArity : Nat)
    (leftFound : context.signature.typeOperators left = some leftArity)
    (rightFound : context.signature.typeOperators right = some rightArity) :
    (registeredOperatorAtom left == registeredOperatorAtom right) = TypeOp.same left right := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, TypeOp.same_eq_true_iff]
  constructor
  · intro same
    exact context.uniqueTypeNames left right leftArity rightArity leftFound rightFound
      (DefinitionAdapters.sourceOperatorName_injective (TypeSubstitution.nameAtom_injective same))
  · rintro rfl
    rfl

mutual
  private theorem type_body_returns (context : DefinitionAdapters.TheoryContext)
      (schema occurrence : Ty) (schemaFormed : TypeFormed context.signature schema)
      (occurrenceFormed : TypeFormed context.signature occurrence) (assignments : TypeSubst)
      (assignmentsFormed : AssignmentsFormed context.signature assignments) (state : State) :
      BoundCalls.CorePath.PureReturns program (typeEnvironment schema occurrence assignments) state typeEquation.body state
        (answer (matchType schema occurrence assignments)) := by
    rw [type_body_shape]
    cases schema with
    | var name =>
        let bound := ("name", nameAtom name) :: typeEnvironment (.var name) occurrence assignments
        apply BoundCalls.CorePath.case_returns program (typeEnvironment (.var name) occurrence assignments) bound state state state
          (.var "schema") (typeAtom registeredOperatorAtom (.var name)) variableBody _ _ typeCases
          (read_cases_encoded typeCases)
        · exact BoundCalls.CorePath.variable_returns program _ state "schema"
        · simp [type_cases_shape, bound, typeEnvironment, typeAtom, SpaceSemantics.selectCase,
            SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · rw [variable_shape]
          have lookupReturns := Lookup.authored_lookup_certificate bound state (nameAtom name)
            (entriesAtom assignments) "name" "assignments"
            (by simp [bound, typeEnvironment, applySubst, Subst.lookup])
            (by simp [bound, typeEnvironment, applySubst, Subst.lookup, assignmentsAtom])
          rw [encoded_lookup] at lookupReturns
          cases found : assignments.lookup name with
          | none =>
              apply BoundCalls.CorePath.case_returns program bound bound state state state _ (.symbol "None")
                newAssignmentBody _ _ (rows variableBody) (read_cases_encoded _)
              · simpa [found, Lookup.answer] using lookupReturns
              · simp [variable_rows, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
              · simpa [matchType, found] using new_assignment_return bound state name occurrence assignments
                  (by simp [bound, typeEnvironment, applySubst, Subst.lookup])
                  (by simp [bound, typeEnvironment, applySubst, Subst.lookup])
                  (by simp [bound, typeEnvironment, applySubst, Subst.lookup])
          | some previous =>
              let selected := ("previous", typeAtom registeredOperatorAtom previous) :: bound
              apply BoundCalls.CorePath.case_returns program bound selected state state state _
                (.expression [.symbol "Some", typeAtom registeredOperatorAtom previous]) previousBody _ _
                (rows variableBody) (read_cases_encoded _)
              · simpa [found, Lookup.answer] using lookupReturns
              · simp [variable_rows, selected, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                  SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bound, typeEnvironment]
              · unfold previousBody
                apply BoundCalls.CorePath.if_returns program selected state state state _ (boolean (Ty.same previous occurrence)) _ _ _
                · apply BoundCalls.CorePath.native_variable_call_returns program selected state state "==" ["previous", "instance"]
                    _ (by decide) (by decide) _ (by decide)
                  simp [StdLib.structural_equality, selected, bound, typeEnvironment, applySubst, Subst.lookup,
                    type_comparison context previous occurrence (assignmentsFormed name previous found) occurrenceFormed]
                · cases same : Ty.same previous occurrence with
                  | false =>
                      simpa [matchType, found, same, answer, Lookup.answer, boolean] using
                        BoundCalls.CorePath.symbol_returns program selected state "None"
                  | true =>
                      simpa [matchType, found, same, answer, Lookup.answer, boolean,
                        selected, bound, typeEnvironment, applySubst, Subst.lookup] using
                        BoundCalls.CorePath.unary_constructor_returns program selected state "Some" "assignments" (by decide) (by decide)
    | op operator arguments =>
        let bound := [("arguments", Premises.keys (arguments.map (typeAtom registeredOperatorAtom))),
          ("operator", registeredOperatorAtom operator)] ++ typeEnvironment (.op operator arguments) occurrence assignments
        apply BoundCalls.CorePath.case_returns program (typeEnvironment (.op operator arguments) occurrence assignments) bound state state state
          (.var "schema") (typeAtom registeredOperatorAtom (.op operator arguments)) operatorBody _ _ typeCases
          (read_cases_encoded typeCases)
        · exact BoundCalls.CorePath.variable_returns program _ state "schema"
        · simp [type_cases_shape, bound, typeEnvironment, typeAtom, SpaceSemantics.selectCase,
            SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · rw [operator_shape]
          cases occurrence with
          | var name =>
              let selected := ("malformed", typeAtom registeredOperatorAtom (.var name)) :: bound
              apply BoundCalls.CorePath.case_returns program bound selected state state state (.var "instance")
                (typeAtom registeredOperatorAtom (.var name)) (.symbol "None") _ _
                (rows operatorBody) (read_cases_encoded _)
              · exact BoundCalls.CorePath.variable_returns program _ state "instance"
              · simp [operator_rows, selected, bound, typeEnvironment, typeAtom, SpaceSemantics.selectCase,
                  SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
              · simpa [matchType, answer, Lookup.answer] using BoundCalls.CorePath.symbol_returns program selected state "None"
          | op target values =>
              let selected := [("values", Premises.keys (values.map (typeAtom registeredOperatorAtom))),
                ("target", registeredOperatorAtom target)] ++ bound
              apply BoundCalls.CorePath.case_returns program bound selected state state state (.var "instance")
                (typeAtom registeredOperatorAtom (.op target values)) operatorSelected _ _
                (rows operatorBody) (read_cases_encoded _)
              · exact BoundCalls.CorePath.variable_returns program _ state "instance"
              · simp [operator_rows, selected, bound, typeEnvironment, typeAtom, SpaceSemantics.selectCase,
                  SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
              · simp only [TypeFormed] at schemaFormed occurrenceFormed
                unfold operatorSelected
                apply BoundCalls.CorePath.if_returns program selected state state state _ (boolean (TypeOp.same operator target)) _ _ _
                · apply BoundCalls.CorePath.native_variable_call_returns program selected state state "==" ["operator", "target"] _
                    (by decide) (by decide) _ (by decide)
                  simp [StdLib.structural_equality, selected, bound, typeEnvironment, applySubst, Subst.lookup,
                    operator_comparison context operator target arguments.length values.length
                      schemaFormed.1 occurrenceFormed.1]
                · cases same : TypeOp.same operator target with
                  | false =>
                      simpa [matchType, same, answer, Lookup.answer, boolean] using
                        BoundCalls.CorePath.symbol_returns program selected state "None"
                  | true =>
                      simp only [boolean, BEq.rfl, ↓reduceIte]
                      apply BoundCalls.CorePath.authored_variable_call_returns program selected
                        (listEnvironment arguments values assignments) state state "hol-light:type-match-list"
                        ["arguments", "values", "assignments"] listEquation.body _
                        (by decide) (by decide) (by decide) _ _ (by decide)
                      · simpa [selected, bound, typeEnvironment, applySubst, Subst.lookup] using
                          list_clause arguments values assignments
                      · simpa [matchType, same] using list_body_returns context arguments values
                          schemaFormed.2 occurrenceFormed.2 assignments assignmentsFormed state
  termination_by sizeOf schema

  private theorem list_body_returns (context : DefinitionAdapters.TheoryContext)
      (schemas occurrences : List Ty)
      (schemasFormed : ∀ schema ∈ schemas, TypeFormed context.signature schema)
      (occurrencesFormed : ∀ occurrence ∈ occurrences, TypeFormed context.signature occurrence)
      (assignments : TypeSubst) (assignmentsFormed : AssignmentsFormed context.signature assignments) (state : State) :
      BoundCalls.CorePath.PureReturns program (listEnvironment schemas occurrences assignments) state listEquation.body state
        (answer (matchTypes schemas occurrences assignments)) := by
    rw [list_body_shape]
    have tupleReturns := BoundCalls.CorePath.tuple_variables_return program (listEnvironment schemas occurrences assignments)
      state ["schemas", "instances"]
      (by
        cases schemas <;> simp [BoundCalls.target, listEnvironment, applySubst, Subst.lookup, Premises.keys]
        decide)
    cases schemas with
    | nil =>
        cases occurrences with
        | nil =>
            apply BoundCalls.CorePath.case_returns program (listEnvironment [] [] assignments) (listEnvironment [] [] assignments)
              state state state _ (.expression [.symbol "HOL:Nil", .symbol "HOL:Nil"])
              (.expression [.symbol "Some", .var "assignments"]) _ _ listCases (read_cases_encoded listCases)
            · simpa [listEnvironment, applySubst, Subst.lookup, Premises.keys] using tupleReturns
            · simp [list_cases_shape, listEnvironment, Premises.keys, SpaceSemantics.selectCase,
                SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom]
            · simpa [matchTypes, answer, Lookup.answer, listEnvironment, applySubst, Subst.lookup] using
                BoundCalls.CorePath.unary_constructor_returns program (listEnvironment [] [] assignments) state "Some" "assignments"
                  (by decide) (by decide)
        | cons value values =>
            let tuple : Atom := .expression [.symbol "HOL:Nil",
              Premises.keys ((value :: values).map (typeAtom registeredOperatorAtom))]
            let selected := ("malformed", tuple) :: listEnvironment [] (value :: values) assignments
            apply BoundCalls.CorePath.case_returns program (listEnvironment [] (value :: values) assignments) selected state state state _
              tuple (.symbol "None") _ _ listCases (read_cases_encoded listCases)
            · simpa [tuple, listEnvironment, applySubst, Subst.lookup, Premises.keys] using tupleReturns
            · simp [list_cases_shape, selected, tuple, listEnvironment, Premises.keys, SpaceSemantics.selectCase,
                SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
            · simpa [matchTypes, answer, Lookup.answer] using BoundCalls.CorePath.symbol_returns program selected state "None"
    | cons first rest =>
        cases occurrences with
        | nil =>
            let tuple : Atom := .expression [Premises.keys ((first :: rest).map (typeAtom registeredOperatorAtom)),
              .symbol "HOL:Nil"]
            let selected := ("malformed", tuple) :: listEnvironment (first :: rest) [] assignments
            apply BoundCalls.CorePath.case_returns program (listEnvironment (first :: rest) [] assignments) selected state state state _
              tuple (.symbol "None") _ _ listCases (read_cases_encoded listCases)
            · simpa [tuple, listEnvironment, applySubst, Subst.lookup, Premises.keys] using tupleReturns
            · simp [list_cases_shape, selected, tuple, listEnvironment, Premises.keys, SpaceSemantics.selectCase,
                SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
            · simpa [matchTypes, answer, Lookup.answer] using BoundCalls.CorePath.symbol_returns program selected state "None"
        | cons value values =>
            let selected := [("values", Premises.keys (values.map (typeAtom registeredOperatorAtom))),
              ("value", typeAtom registeredOperatorAtom value),
              ("rest", Premises.keys (rest.map (typeAtom registeredOperatorAtom))),
              ("first", typeAtom registeredOperatorAtom first)] ++
              listEnvironment (first :: rest) (value :: values) assignments
            apply BoundCalls.CorePath.case_returns program (listEnvironment (first :: rest) (value :: values) assignments)
              selected state state state _ (.expression
                [Premises.keys ((first :: rest).map (typeAtom registeredOperatorAtom)),
                  Premises.keys ((value :: values).map (typeAtom registeredOperatorAtom))])
              consBody _ _ listCases (read_cases_encoded listCases)
            · simpa [listEnvironment, applySubst, Subst.lookup] using tupleReturns
            · simp [list_cases_shape, selected, listEnvironment, Premises.keys, SpaceSemantics.selectCase,
                SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
            · rw [cons_shape]
              have firstReturns : BoundCalls.CorePath.PureReturns program selected state
                  (.expression [.symbol "hol-light:type-match", .var "first", .var "value", .var "assignments"])
                  state (answer (matchType first value assignments)) := by
                apply BoundCalls.CorePath.authored_variable_call_returns program selected (typeEnvironment first value assignments)
                  state state "hol-light:type-match" ["first", "value", "assignments"] typeEquation.body _
                  (by decide) (by decide) (by decide) _
                  (type_body_returns context first value (schemasFormed first List.mem_cons_self)
                    (occurrencesFormed value List.mem_cons_self) assignments assignmentsFormed state) (by decide)
                simpa [selected, listEnvironment, applySubst, Subst.lookup] using type_clause first value assignments
              cases found : matchType first value assignments with
              | none =>
                  let refused := ("malformed", .symbol "None") :: selected
                  apply BoundCalls.CorePath.case_returns program selected refused state state state _ (.symbol "None")
                    (.symbol "None") _ _ (rows consBody) (read_cases_encoded _)
                  · simpa [found, answer, Lookup.answer] using firstReturns
                  · simp [cons_rows, refused, selected, listEnvironment, SpaceSemantics.selectCase,
                      SpaceSemantics.matchValue, matchAtom, Subst.lookup]
                  · simpa [matchTypes, found, answer, Lookup.answer] using BoundCalls.CorePath.symbol_returns program refused state "None"
              | some next =>
                  let entered := ("next", assignmentsAtom next) :: selected
                  apply BoundCalls.CorePath.case_returns program selected entered state state state _
                    (.expression [.symbol "Some", assignmentsAtom next])
                    (.expression [.symbol "hol-light:type-match-list", .var "rest", .var "values", .var "next"])
                    _ _ (rows consBody) (read_cases_encoded _)
                  · simpa [found, answer, Lookup.answer] using firstReturns
                  · simp [cons_rows, entered, selected, listEnvironment, SpaceSemantics.selectCase,
                      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
                  · apply BoundCalls.CorePath.authored_variable_call_returns program entered (listEnvironment rest values next)
                      state state "hol-light:type-match-list" ["rest", "values", "next"] listEquation.body _
                      (by decide) (by decide) (by decide) _ _ (by decide)
                    · simpa [entered, selected, listEnvironment, applySubst, Subst.lookup] using list_clause rest values next
                    · simpa [matchTypes, found] using list_body_returns context rest values
                        (fun schema member => schemasFormed schema (List.mem_cons_of_mem _ member))
                        (fun occurrence member => occurrencesFormed occurrence (List.mem_cons_of_mem _ member))
                        next (matchType_formed context.signature assignmentsFormed
                          (occurrencesFormed value List.mem_cons_self) found) state
  termination_by sizeOf schemas
end

/-- The retained source matcher executes to the shared substitution result,
including refusals, on arbitrary formed declaration schemas and occurrences. -/
theorem authored_match_certificate (context : DefinitionAdapters.TheoryContext)
    (schema occurrence : Ty) (schemaFormed : TypeFormed context.signature schema)
    (occurrenceFormed : TypeFormed context.signature occurrence) (assignments : TypeSubst)
    (assignmentsFormed : AssignmentsFormed context.signature assignments)
    (bindings : Subst) (state : State) (schemaKey instanceKey assignmentsKey : String)
    (schemaCaptured : applySubst bindings (.var schemaKey) = typeAtom registeredOperatorAtom schema)
    (instanceCaptured : applySubst bindings (.var instanceKey) = typeAtom registeredOperatorAtom occurrence)
    (assignmentsCaptured : applySubst bindings (.var assignmentsKey) = assignmentsAtom assignments) :
    BoundCalls.CorePath.PureReturns program bindings state (.expression [.symbol "hol-light:type-match",
      .var schemaKey, .var instanceKey, .var assignmentsKey]) state
      (answer (matchType schema occurrence assignments)) := by
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings (typeEnvironment schema occurrence assignments)
    state state "hol-light:type-match" [schemaKey, instanceKey, assignmentsKey] typeEquation.body _
    (by decide) (by decide) (by decide) _
    (type_body_returns context schema occurrence schemaFormed occurrenceFormed assignments assignmentsFormed state)
    (by decide)
  simpa only [List.map_cons, List.map_nil, schemaCaptured, instanceCaptured, assignmentsCaptured] using
    type_clause schema occurrence assignments

/-- Computed argument values enter the same source equation. In particular,
the source's literal empty assignment table requires no extra evaluator rule. -/
theorem authored_match_computed_return (context : DefinitionAdapters.TheoryContext)
    (schema occurrence : Ty) (schemaFormed : TypeFormed context.signature schema)
    (occurrenceFormed : TypeFormed context.signature occurrence) (assignments : TypeSubst)
    (assignmentsFormed : AssignmentsFormed context.signature assignments)
    (bindings : Subst) (state : State) (schemaExpr instanceExpr assignmentsExpr : Atom)
    (schemaComputed : PureReturns program bindings state schemaExpr state (typeAtom registeredOperatorAtom schema))
    (instanceComputed : PureReturns program bindings state instanceExpr state (typeAtom registeredOperatorAtom occurrence))
    (assignmentsComputed : PureReturns program bindings state assignmentsExpr state (assignmentsAtom assignments)) :
    PureReturns program bindings state (.expression [.symbol "hol-light:type-match",
      schemaExpr, instanceExpr, assignmentsExpr]) state (answer (matchType schema occurrence assignments)) := by
  apply call_returns program bindings state state "hol-light:type-match"
    [schemaExpr, instanceExpr, assignmentsExpr] _ (by decide) _ (by decide)
  apply evaluated_argument_returns program bindings state state state (.function "hol-light:type-match")
    schemaExpr _ _ [instanceExpr, assignmentsExpr] [] 0 (by decide) schemaComputed
  apply evaluated_argument_returns program bindings state state state (.function "hol-light:type-match")
    instanceExpr _ _ [assignmentsExpr] [_] 1 (by decide) instanceComputed
  apply evaluated_argument_returns program bindings state state state (.function "hol-light:type-match")
    assignmentsExpr _ _ [] [_, _] 2 (by decide) assignmentsComputed
  exact authored_function_arguments_return program bindings (typeEnvironment schema occurrence assignments) state state
    "hol-light:type-match" [_, _, _] 3 typeEquation.body _ (by decide) (by decide)
    (type_clause schema occurrence assignments)
    (type_body_returns context schema occurrence schemaFormed occurrenceFormed assignments assignmentsFormed state).original

theorem authored_match_return (context : DefinitionAdapters.TheoryContext)
    (schema occurrence : Ty) (schemaFormed : TypeFormed context.signature schema)
    (occurrenceFormed : TypeFormed context.signature occurrence) (assignments : TypeSubst)
    (assignmentsFormed : AssignmentsFormed context.signature assignments)
    (bindings : Subst) (state : State) (schemaKey instanceKey assignmentsKey : String)
    (schemaCaptured : applySubst bindings (.var schemaKey) = typeAtom registeredOperatorAtom schema)
    (instanceCaptured : applySubst bindings (.var instanceKey) = typeAtom registeredOperatorAtom occurrence)
    (assignmentsCaptured : applySubst bindings (.var assignmentsKey) = assignmentsAtom assignments) :
    PureReturns program bindings state (.expression [.symbol "hol-light:type-match",
      .var schemaKey, .var instanceKey, .var assignmentsKey]) state
      (answer (matchType schema occurrence assignments)) :=
  (authored_match_certificate context schema occurrence schemaFormed occurrenceFormed assignments assignmentsFormed bindings state schemaKey instanceKey assignmentsKey schemaCaptured instanceCaptured assignmentsCaptured).original

theorem authored_match_bound_return (context : DefinitionAdapters.TheoryContext)
    (schema occurrence : Ty) (schemaFormed : TypeFormed context.signature schema)
    (occurrenceFormed : TypeFormed context.signature occurrence) (assignments : TypeSubst)
    (assignmentsFormed : AssignmentsFormed context.signature assignments)
    (bindings : Subst) (state : State) (schemaKey instanceKey assignmentsKey : String)
    (schemaCaptured : applySubst bindings (.var schemaKey) = typeAtom registeredOperatorAtom schema)
    (instanceCaptured : applySubst bindings (.var instanceKey) = typeAtom registeredOperatorAtom occurrence)
    (assignmentsCaptured : applySubst bindings (.var assignmentsKey) = assignmentsAtom assignments) :
    BoundCalls.PureReturns program bindings state (.expression [.symbol "hol-light:type-match",
      .var schemaKey, .var instanceKey, .var assignmentsKey]) state
      (answer (matchType schema occurrence assignments)) :=
  (authored_match_certificate context schema occurrence schemaFormed occurrenceFormed assignments assignmentsFormed bindings state schemaKey instanceKey assignmentsKey schemaCaptured instanceCaptured assignmentsCaptured).extended

theorem authored_match_computed_certificate (context : DefinitionAdapters.TheoryContext)
    (schema occurrence : Ty) (schemaFormed : TypeFormed context.signature schema)
    (occurrenceFormed : TypeFormed context.signature occurrence) (assignments : TypeSubst)
    (assignmentsFormed : AssignmentsFormed context.signature assignments)
    (bindings : Subst) (state : State) (schemaExpr instanceExpr assignmentsExpr : Atom)
    (schemaComputed : BoundCalls.CorePath.PureReturns program bindings state schemaExpr state (typeAtom registeredOperatorAtom schema))
    (instanceComputed : BoundCalls.CorePath.PureReturns program bindings state instanceExpr state (typeAtom registeredOperatorAtom occurrence))
    (assignmentsComputed : BoundCalls.CorePath.PureReturns program bindings state assignmentsExpr state (assignmentsAtom assignments)) :
    BoundCalls.CorePath.PureReturns program bindings state (.expression [.symbol "hol-light:type-match",
      schemaExpr, instanceExpr, assignmentsExpr]) state (answer (matchType schema occurrence assignments)) := by
  apply BoundCalls.CorePath.call_returns program bindings state state "hol-light:type-match"
    [schemaExpr, instanceExpr, assignmentsExpr] _ (by decide) _ (by decide)
  apply BoundCalls.CorePath.evaluated_argument_returns program bindings state state state (.function "hol-light:type-match")
    schemaExpr _ _ [instanceExpr, assignmentsExpr] [] 0 (by decide) schemaComputed
  apply BoundCalls.CorePath.evaluated_argument_returns program bindings state state state (.function "hol-light:type-match")
    instanceExpr _ _ [assignmentsExpr] [_] 1 (by decide) instanceComputed
  apply BoundCalls.CorePath.evaluated_argument_returns program bindings state state state (.function "hol-light:type-match")
    assignmentsExpr _ _ [] [_, _] 2 (by decide) assignmentsComputed
  exact BoundCalls.CorePath.authored_function_arguments_return program bindings (typeEnvironment schema occurrence assignments) state state
    "hol-light:type-match" [_, _, _] 3 typeEquation.body _ (by decide) (by decide)
    (type_clause schema occurrence assignments)
    (type_body_returns context schema occurrence schemaFormed occurrenceFormed assignments assignmentsFormed state)


end Mettapedia.Languages.HOLLight.MeTTa.TypeMatching
