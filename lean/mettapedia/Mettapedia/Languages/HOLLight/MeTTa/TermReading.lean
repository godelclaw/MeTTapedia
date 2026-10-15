import Mettapedia.Languages.HOLLight.MeTTa.TypeMatching
import Mettapedia.Languages.HOLLight.MeTTa.ContextLookup
import Mettapedia.Languages.HOLLight.MeTTa.DeclarationTable
import Mettapedia.Languages.HOLLight.MeTTa.TermJudgment

/-!
# Source term admission through the authored HOL reader

Written names are resolved in the retained declaration and binder context.
The variable laws preserve typed nearest-binder lookup. The constant laws
execute polymorphic schema matching before returning the registered identity.
These laws concern the actual source reader; constructing an internal term
record alone does not authorize it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.TermReading

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open SignatureFormation
open Eval
open Effects (State boolean)
open TypeSubstitution (nameAtom typeAtom)
open Representation (registeredOperatorAtom termAtom sourceVariableAtom)

/-- Named source syntax uses the declaration name at a constant occurrence;
the reader, rather than its caller, recovers the registered identity payload. -/
def sourceAtom : SourceTerm → Atom
  | .var name type => sourceVariableAtom registeredOperatorAtom ⟨name, type⟩
  | .const constant type => .expression [.symbol "Const",
      nameAtom (DefinitionAdapters.constantName constant), typeAtom registeredOperatorAtom type]
  | .app function argument => .expression [.symbol "Comb", sourceAtom function, sourceAtom argument]
  | .abs name type body => .expression [.symbol "Abs",
      sourceVariableAtom registeredOperatorAtom ⟨name, type⟩, sourceAtom body]
termination_by structural source => source

private def equation : SpaceSemantics.Equation :=
  (syntaxSource.program.equations.filter (fun row => row.head == "hol-light:read-term"))[0]'(by decide)
private def cases : SpaceSemantics.Cases :=
  match equation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def indexBody : Atom := .expression [.symbol "case",
  .expression [.symbol "hol-light:bound-index", .var "source", .var "context", .grounded (.int 0)],
  .expression [.expression [.symbol "None", .expression [.symbol "Some",
    .expression [.symbol "HOL:Free", .var "name", .var "type"]]],
    .expression [.expression [.symbol "Some", .var "index"], .expression [.symbol "Some",
      .expression [.symbol "HOL:Bound", .var "index", .var "type"]]],
    .expression [.var "malformed", .symbol "None"]]]
private def variableBody : Atom := .expression [.symbol "if",
  .expression [.symbol "==", .expression [.symbol "get-type", .var "name"], .symbol "String"],
  .expression [.symbol "if", .expression [.symbol "hol-light:type-formed", .var "operators", .var "type"],
    indexBody, .symbol "None"], .symbol "None"]
private def matchedBody : Atom := .expression [.symbol "Some",
  .expression [.symbol "HOL:C", .var "identity", .var "type"]]
private def matchingBody : Atom := .expression [.symbol "case",
  .expression [.symbol "hol-light:type-match", .var "schema", .var "type", .symbol "HOL:Nil"],
  .expression [.expression [.expression [.symbol "Some", .var "assignments"], matchedBody],
    .expression [.var "malformed", .symbol "None"]]]
private def lookupBody : Atom := .expression [.symbol "case",
  .expression [.symbol "hol-light:lookup", .var "name", .var "constants"],
  .expression [.expression [.expression [.symbol "Some", .expression [.symbol "HOL:Constant",
    .var "schema", .var "identity"]], matchingBody],
    .expression [.var "unknown", .symbol "None"]]]
private def constantBody : Atom := .expression [.symbol "if",
  .expression [.symbol "hol-light:type-formed", .var "operators", .var "type"], lookupBody, .symbol "None"]
private def applicationSelected : Atom := .expression [.symbol "if", .expression [.symbol "==",
  .expression [.symbol "hol-light:term-type", .var "value"], .expression [.symbol "Some", .var "domain"]],
  .expression [.symbol "Some", .expression [.symbol "HOL:App", .var "fn", .var "value"]], .symbol "None"]
private def functionBody : Atom := .expression [.symbol "case",
  .expression [.symbol "hol-light:term-type", .var "fn"], .expression
    [.expression [.expression [.symbol "Some", .expression [.symbol "Tyapp", .grounded (.string "fun"),
      .expression [.symbol "HOL:Cons", .var "domain", .expression [.symbol "HOL:Cons", .var "codomain", .symbol "HOL:Nil"]]]],
      applicationSelected], .expression [.var "malformed", .symbol "None"]]]
private def applicationBody : Atom := .expression [.symbol "case", .expression
  [.expression [.symbol "hol-light:read-term", .var "operators", .var "constants", .var "context", .var "function"],
   .expression [.symbol "hol-light:read-term", .var "operators", .var "constants", .var "context", .var "argument"]],
  .expression [.expression [.expression [.expression [.symbol "Some", .var "fn"],
    .expression [.symbol "Some", .var "value"]], functionBody], .expression [.var "malformed", .symbol "None"]]]
private def lambdaRead : Atom := .expression [.symbol "hol-light:read-term", .var "operators", .var "constants",
  .expression [.symbol "HOL:Cons", .expression [.symbol "Var", .var "name", .var "type"], .var "context"], .var "body"]
private def lambdaResult : Atom := .expression [.symbol "case", lambdaRead, .expression
  [.expression [.expression [.symbol "Some", .var "value"], .expression [.symbol "Some",
    .expression [.symbol "HOL:Lam", .var "type", .var "value"]]], .expression [.var "malformed", .symbol "None"]]]
private def lambdaBody : Atom := .expression [.symbol "if",
  .expression [.symbol "==", .expression [.symbol "get-type", .var "name"], .symbol "String"],
  .expression [.symbol "if", .expression [.symbol "hol-light:type-formed", .var "operators", .var "type"],
    lambdaResult, .symbol "None"], .symbol "None"]

private def rows (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression cases] => (readCases cases).getD []
  | _ => []
private def environment (operators constants : Atom) (context : List SourceVar) (source : SourceTerm) : Subst :=
  [("source", sourceAtom source), ("context", ContextLookup.contextAtom context),
    ("constants", constants), ("operators", operators)]

private theorem unique :
    program.equations.filter (fun row => row.head == "hol-light:read-term") = [equation] := by rfl
private theorem formals : equation.arguments =
    [.var "operators", .var "constants", .var "context", .var "source"] := by decide
private theorem body_shape : equation.body = .expression [.symbol "case", .var "source",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem first_cases : cases =
    [(.expression [.symbol "Var", .var "name", .var "type"], variableBody),
     (.expression [.symbol "Const", .var "name", .var "type"], constantBody)] ++ cases.drop 2 := by decide
private theorem all_cases : cases =
    [(.expression [.symbol "Var", .var "name", .var "type"], variableBody),
     (.expression [.symbol "Const", .var "name", .var "type"], constantBody),
     (.expression [.symbol "Comb", .var "function", .var "argument"], applicationBody),
     (.expression [.symbol "Abs", .expression [.symbol "Var", .var "name", .var "type"], .var "body"], lambdaBody),
     (.var "malformed", .symbol "None")] := by decide
private theorem application_shape : applicationBody = .expression [.symbol "case", .expression
    [.expression [.symbol "hol-light:read-term", .var "operators", .var "constants", .var "context", .var "function"],
     .expression [.symbol "hol-light:read-term", .var "operators", .var "constants", .var "context", .var "argument"]],
    .expression ((rows applicationBody).map fun row => .expression [row.1, row.2])] := by decide
private theorem application_rows : rows applicationBody =
    [(.expression [.expression [.symbol "Some", .var "fn"], .expression [.symbol "Some", .var "value"]], functionBody),
     (.var "malformed", .symbol "None")] := by decide
private theorem function_shape : functionBody = .expression [.symbol "case",
    .expression [.symbol "hol-light:term-type", .var "fn"],
    .expression ((rows functionBody).map fun row => .expression [row.1, row.2])] := by decide
private theorem function_rows : rows functionBody =
    [(.expression [.symbol "Some", .expression [.symbol "Tyapp", .grounded (.string "fun"),
      .expression [.symbol "HOL:Cons", .var "domain", .expression [.symbol "HOL:Cons", .var "codomain", .symbol "HOL:Nil"]]]],
      applicationSelected), (.var "malformed", .symbol "None")] := by decide
private theorem lambda_shape : lambdaResult = .expression [.symbol "case", lambdaRead,
    .expression ((rows lambdaResult).map fun row => .expression [row.1, row.2])] := by decide
private theorem lambda_rows : rows lambdaResult =
    [(.expression [.symbol "Some", .var "value"], .expression [.symbol "Some",
      .expression [.symbol "HOL:Lam", .var "type", .var "value"]]), (.var "malformed", .symbol "None")] := by decide
private theorem index_shape : indexBody = .expression [.symbol "case",
    .expression [.symbol "hol-light:bound-index", .var "source", .var "context", .grounded (.int 0)],
    .expression ((rows indexBody).map fun row => .expression [row.1, row.2])] := by decide
private theorem index_rows : rows indexBody =
    [(.symbol "None", .expression [.symbol "Some", .expression [.symbol "HOL:Free", .var "name", .var "type"]]),
     (.expression [.symbol "Some", .var "index"], .expression [.symbol "Some",
       .expression [.symbol "HOL:Bound", .var "index", .var "type"]]),
     (.var "malformed", .symbol "None")] := by decide
private theorem lookup_shape : lookupBody = .expression [.symbol "case",
    .expression [.symbol "hol-light:lookup", .var "name", .var "constants"],
    .expression ((rows lookupBody).map fun row => .expression [row.1, row.2])] := by decide
private theorem lookup_rows : rows lookupBody =
    [(.expression [.symbol "Some", .expression [.symbol "HOL:Constant", .var "schema", .var "identity"]], matchingBody),
     (.var "unknown", .symbol "None")] := by decide
private theorem matching_shape : matchingBody = .expression [.symbol "case",
    .expression [.symbol "hol-light:type-match", .var "schema", .var "type", .symbol "HOL:Nil"],
    .expression ((rows matchingBody).map fun row => .expression [row.1, row.2])] := by decide
private theorem matching_rows : rows matchingBody =
    [(.expression [.symbol "Some", .var "assignments"], matchedBody),
     (.var "malformed", .symbol "None")] := by decide

private theorem clause (operators constants : Atom) (context : List SourceVar) (source : SourceTerm) :
    clauses program "hol-light:read-term" [operators, constants, ContextLookup.contextAtom context, sourceAtom source] =
      [.evaluate (environment operators constants context source) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem read_call_of_returns (operators constants : Atom) (context : List SourceVar) (source : SourceTerm)
    (bindings : Subst) (state : State) (operatorsExpr constantsExpr contextExpr sourceExpr value : Atom)
    (operatorsComputed : BoundCalls.CorePath.PureReturns program bindings state operatorsExpr state operators)
    (constantsComputed : BoundCalls.CorePath.PureReturns program bindings state constantsExpr state constants)
    (contextComputed : BoundCalls.CorePath.PureReturns program bindings state contextExpr state (ContextLookup.contextAtom context))
    (sourceComputed : BoundCalls.CorePath.PureReturns program bindings state sourceExpr state (sourceAtom source))
    (bodyComputed : BoundCalls.CorePath.PureReturns program (environment operators constants context source) state equation.body state value) :
    BoundCalls.CorePath.PureReturns program bindings state (.expression [.symbol "hol-light:read-term", operatorsExpr,
      constantsExpr, contextExpr, sourceExpr]) state value := by
  apply BoundCalls.CorePath.call_returns program bindings state state "hol-light:read-term" _ _ (by decide) _ (by decide)
  apply BoundCalls.CorePath.evaluated_argument_returns program bindings state state state (.function "hol-light:read-term")
    operatorsExpr _ _ [constantsExpr, contextExpr, sourceExpr] [] 0 (by decide) operatorsComputed
  apply BoundCalls.CorePath.evaluated_argument_returns program bindings state state state (.function "hol-light:read-term")
    constantsExpr _ _ [contextExpr, sourceExpr] [_] 1 (by decide) constantsComputed
  apply BoundCalls.CorePath.evaluated_argument_returns program bindings state state state (.function "hol-light:read-term")
    contextExpr _ _ [sourceExpr] [_, _] 2 (by decide) contextComputed
  apply BoundCalls.CorePath.evaluated_argument_returns program bindings state state state (.function "hol-light:read-term")
    sourceExpr _ _ [] [_, _, _] 3 (by decide) sourceComputed
  exact BoundCalls.CorePath.authored_function_arguments_return program bindings (environment operators constants context source)
    state state "hol-light:read-term" [_, _, _, _] 4 equation.body _ (by decide) (by decide)
    (clause operators constants context source) bodyComputed

private theorem data_pair_returns (bindings : Subst) (state : State) (left : List Atom) (right first second : Atom)
    (leftComputed : BoundCalls.CorePath.PureReturns program bindings state (.expression left) state first)
    (rightComputed : BoundCalls.CorePath.PureReturns program bindings state right state second) :
    BoundCalls.CorePath.PureReturns program bindings state (.expression [.expression left, right]) state (.expression [first, second]) := by
  let entered : Configuration := { state, control := .arguments bindings .data [.expression left, right] [] 0 }
  refine .step (middle := entered) rfl (step_transition rfl) ?_
  apply BoundCalls.CorePath.evaluated_argument_returns program bindings state state state .data (.expression left) first _
    [right] [] 0 rfl leftComputed
  apply BoundCalls.CorePath.evaluated_argument_returns program bindings state state state .data right second _ [] [first] 1 rfl rightComputed
  exact BoundCalls.CorePath.data_arguments_values_return program bindings state [first, second] 2

private theorem variable_body_returns (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (context : List SourceVar)
    (contextFormed : ∀ binder ∈ context, TypeFormed world.signature binder.ty)
    (needle : SourceVar) (globalName : needle.name.namespaceComponents = [])
    (formed : TypeFormed world.signature needle.ty)
    (resolved : TypeFormation.Resolved world.signature needle.ty) (state : State) :
    BoundCalls.CorePath.PureReturns program
      ([("type", typeAtom registeredOperatorAtom needle.ty), ("name", nameAtom needle.name)] ++
        environment (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
          context (.var needle.name needle.ty))
      state variableBody state (.expression [.symbol "Some",
        termAtom registeredOperatorAtom constants (context.map Var.ty)
          ((SourceTerm.var needle.name needle.ty).toDB context)]) := by
  let bound := [("type", typeAtom registeredOperatorAtom needle.ty), ("name", nameAtom needle.name)] ++
    environment (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
      context (.var needle.name needle.ty)
  unfold variableBody
  apply BoundCalls.CorePath.if_returns program bound state state state _ (boolean true) _ _ _
  · apply BoundCalls.CorePath.native_binary_call_returns program bound state state state state "==" _ (.symbol "String")
      (.symbol "String") (.symbol "String") (boolean true) (by decide) (by decide) (by decide) (by decide)
    · apply BoundCalls.CorePath.native_variable_call_returns program bound state state "get-type" ["name"] (.symbol "String")
        (by decide) (by decide) _ (by decide)
      simp [StdLib.string_type_is_string, bound, environment, applySubst, Subst.lookup, nameAtom, globalName]
    · exact BoundCalls.CorePath.symbol_returns program bound state "String"
    · rfl
    · decide
  · simp only [boolean, BEq.rfl, ↓reduceIte]
    apply BoundCalls.CorePath.if_returns program bound state state state _ (boolean true) _ _ _
    · have returned := TypeFormation.authored_type_formed_certificate world table.operators origins bound state
        needle.ty resolved "operators" "type"
        (by simp [bound, environment, applySubst, Subst.lookup])
        (by simp [bound, environment, applySubst, Subst.lookup])
      simpa [(typeFormedB_eq_true_iff world.signature needle.ty).mpr formed] using returned
    · simp only [boolean, BEq.rfl, ↓reduceIte]
      rw [index_shape]
      have indexed := ContextLookup.authored_bound_index_computed_certificate world needle formed context contextFormed
        0 bound state (.var "source") (.var "context") (.grounded (.int 0))
        (by simpa [bound, environment, sourceAtom, applySubst, Subst.lookup] using BoundCalls.CorePath.variable_returns program bound state "source")
        (by simpa [bound, environment, applySubst, Subst.lookup] using BoundCalls.CorePath.variable_returns program bound state "context")
        (BoundCalls.CorePath.grounded_returns program bound state (.int 0))
      cases found : boundIndex needle context with
      | none =>
          apply BoundCalls.CorePath.case_returns program bound bound state state state _ (.symbol "None")
            (.expression [.symbol "Some", .expression [.symbol "HOL:Free", .var "name", .var "type"]])
            _ _ (rows indexBody) (read_cases_encoded _)
          · simpa [ContextLookup.indexAnswer, found, Lookup.answer] using indexed
          · simp [index_rows, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
          · apply BoundCalls.CorePath.unary_constructor_of_returns program bound state state "Some" _ _ (by decide) (by decide)
            simpa [SourceTerm.toDB, found, termAtom, Representation.variableAtom, bound, environment,
              applySubst, Subst.lookup] using BoundCalls.CorePath.constructor_variables_return program bound state "HOL:Free"
                ["name", "type"] (by decide) (by decide)
      | some index =>
          let selected := ("index", Atom.grounded (.int index)) :: bound
          apply BoundCalls.CorePath.case_returns program bound selected state state state _
            (.expression [.symbol "Some", .grounded (.int index)])
            (.expression [.symbol "Some", .expression [.symbol "HOL:Bound", .var "index", .var "type"]])
            _ _ (rows indexBody) (read_cases_encoded _)
          · simpa [ContextLookup.indexAnswer, found, Lookup.answer] using indexed
          · simp [index_rows, selected, bound, environment, SpaceSemantics.selectCase,
              SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
          · apply BoundCalls.CorePath.unary_constructor_of_returns program selected state state "Some" _ _ (by decide) (by decide)
            simpa [SourceTerm.toDB, found, termAtom, DBTerm.boundIndex_preserves_type found, selected, bound,
              environment, applySubst, Subst.lookup] using BoundCalls.CorePath.constructor_variables_return program selected state "HOL:Bound"
                ["index", "type"] (by decide) (by decide)

/-- A written variable resolves to the nearest matching typed binder, or
remains the same typed free variable. Spelling alone never determines a slot. -/
theorem authored_variable_read_certificate (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (context : List SourceVar) (contextFormed : ∀ binder ∈ context, TypeFormed world.signature binder.ty)
    (needle : SourceVar) (globalName : needle.name.namespaceComponents = [])
    (formed : TypeFormed world.signature needle.ty) (resolved : TypeFormation.Resolved world.signature needle.ty)
    (bindings : Subst) (state : State) (operatorsKey constantsKey contextKey sourceKey : String)
    (operatorsCaptured : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table.operators origins)
    (constantsCaptured : applySubst bindings (.var constantsKey) = DeclarationTable.tableAtom table constants)
    (contextCaptured : applySubst bindings (.var contextKey) = ContextLookup.contextAtom context)
    (sourceCaptured : applySubst bindings (.var sourceKey) = sourceAtom (.var needle.name needle.ty)) :
    BoundCalls.CorePath.PureReturns program bindings state (.expression [.symbol "hol-light:read-term", .var operatorsKey,
      .var constantsKey, .var contextKey, .var sourceKey]) state (.expression [.symbol "Some",
        termAtom registeredOperatorAtom constants (context.map Var.ty)
          ((SourceTerm.var needle.name needle.ty).toDB context)]) := by
  let initial := environment (OperatorTable.tableAtom table.operators origins)
    (DeclarationTable.tableAtom table constants) context (.var needle.name needle.ty)
  let bound := [("type", typeAtom registeredOperatorAtom needle.ty), ("name", nameAtom needle.name)] ++ initial
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings initial state state "hol-light:read-term"
    [operatorsKey, constantsKey, contextKey, sourceKey] equation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, operatorsCaptured, constantsCaptured, contextCaptured, sourceCaptured] using
      clause (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
        context (.var needle.name needle.ty)
  · rw [body_shape]
    apply BoundCalls.CorePath.case_returns program initial bound state state state (.var "source")
      (sourceAtom (.var needle.name needle.ty)) variableBody _ _ cases (read_cases_encoded cases)
    · exact BoundCalls.CorePath.variable_returns program _ state "source"
    · rw [first_cases]
      simp [initial, bound, environment, sourceAtom, sourceVariableAtom, SpaceSemantics.selectCase,
        SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · exact variable_body_returns world table origins constants context contextFormed needle globalName formed resolved state

private theorem constant_body_returns (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (context : List SourceVar) (constant : Const) (schema occurrence : Ty)
    (registered : world.signature.constants constant = some schema)
    (schemaFormed : TypeFormed world.signature schema) (occurrenceFormed : TypeFormed world.signature occurrence)
    (resolved : TypeFormation.Resolved world.signature occurrence) (state : State) :
    BoundCalls.CorePath.PureReturns program
      ([("type", typeAtom registeredOperatorAtom occurrence),
        ("name", nameAtom (DefinitionAdapters.constantName constant))] ++
        environment (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
          context (.const constant occurrence))
      state constantBody state
      (if (HOLLight.TypeMatching.matchType schema occurrence TypeSubst.empty).isSome then
        .expression [.symbol "Some", termAtom registeredOperatorAtom constants (context.map Var.ty) (.const constant occurrence)]
       else .symbol "None") := by
  let bound := [("type", typeAtom registeredOperatorAtom occurrence),
    ("name", nameAtom (DefinitionAdapters.constantName constant))] ++
    environment (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
      context (.const constant occurrence)
  unfold constantBody
  apply BoundCalls.CorePath.if_returns program bound state state state _ (boolean true) _ _ _
  · have returned := TypeFormation.authored_type_formed_certificate world table.operators origins bound state occurrence resolved
      "operators" "type" (by simp [bound, environment, applySubst, Subst.lookup])
      (by simp [bound, environment, applySubst, Subst.lookup])
    simpa [(typeFormedB_eq_true_iff world.signature occurrence).mpr occurrenceFormed] using returned
  · simp only [boolean, BEq.rfl, ↓reduceIte]
    rw [lookup_shape]
    let selected := [("identity", constants constant), ("schema", typeAtom registeredOperatorAtom schema)] ++ bound
    apply BoundCalls.CorePath.case_returns program bound selected state state state _ (.expression [.symbol "Some",
      .expression [.symbol "HOL:Constant", typeAtom registeredOperatorAtom schema, constants constant]])
      matchingBody _ _ (rows lookupBody) (read_cases_encoded _)
    · have returned := Lookup.authored_lookup_certificate bound state (nameAtom (DefinitionAdapters.constantName constant))
        (DeclarationTable.entriesAtom table constants) "name" "constants"
        (by simp [bound, environment, applySubst, Subst.lookup])
        (by simp [bound, environment, applySubst, Subst.lookup, DeclarationTable.tableAtom])
      simpa [DeclarationTable.lookup_registered table constants constant schema registered, Lookup.answer] using returned
    · simp [lookup_rows, selected, bound, environment, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · rw [matching_shape]
      have matched := TypeMatching.authored_match_computed_certificate world schema occurrence schemaFormed occurrenceFormed
        TypeSubst.empty (by simp [HOLLight.TypeMatching.AssignmentsFormed, TypeSubst.empty, TypeSubst.lookup])
        selected state (.var "schema") (.var "type") (.symbol "HOL:Nil")
        (by simpa [selected, bound, environment, applySubst, Subst.lookup] using BoundCalls.CorePath.variable_returns program selected state "schema")
        (by simpa [selected, bound, environment, applySubst, Subst.lookup] using BoundCalls.CorePath.variable_returns program selected state "type")
        (by simpa [TypeMatching.assignmentsAtom, TypeMatching.entriesAtom, TypeSubst.empty, Lookup.table, Premises.keys] using
          BoundCalls.CorePath.symbol_returns program selected state "HOL:Nil")
      cases found : HOLLight.TypeMatching.matchType schema occurrence TypeSubst.empty with
      | none =>
          let refused := ("malformed", Atom.symbol "None") :: selected
          apply BoundCalls.CorePath.case_returns program selected refused state state state _ (.symbol "None") (.symbol "None")
            _ _ (rows matchingBody) (read_cases_encoded _)
          · simpa [found, TypeMatching.answer, Lookup.answer] using matched
          · simp [matching_rows, refused, selected, bound, environment, SpaceSemantics.selectCase,
              SpaceSemantics.matchValue, matchAtom, Subst.lookup]
          · simpa [found] using BoundCalls.CorePath.symbol_returns program refused state "None"
      | some assignments =>
          let entered := ("assignments", TypeMatching.assignmentsAtom assignments) :: selected
          apply BoundCalls.CorePath.case_returns program selected entered state state state _
            (.expression [.symbol "Some", TypeMatching.assignmentsAtom assignments]) matchedBody
            _ _ (rows matchingBody) (read_cases_encoded _)
          · simpa [found, TypeMatching.answer, Lookup.answer] using matched
          · simp [matching_rows, entered, selected, bound, environment, SpaceSemantics.selectCase,
              SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
          · unfold matchedBody
            simp only [Option.isSome_some, ↓reduceIte]
            apply BoundCalls.CorePath.unary_constructor_of_returns program entered state state "Some" _ _ (by decide) (by decide)
            simpa [termAtom, entered, selected, bound, environment, applySubst, Subst.lookup] using
              BoundCalls.CorePath.constructor_variables_return program entered state "HOL:C" ["identity", "type"] (by decide) (by decide)

/-- A registered constant occurrence is returned exactly when its displayed
type is an instance of that declaration's schema. The result retains the
registered definition identity and the full supplied source context. -/
theorem authored_constant_read_certificate (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (context : List SourceVar) (constant : Const) (schema occurrence : Ty)
    (registered : world.signature.constants constant = some schema)
    (schemaFormed : TypeFormed world.signature schema) (occurrenceFormed : TypeFormed world.signature occurrence)
    (resolved : TypeFormation.Resolved world.signature occurrence)
    (bindings : Subst) (state : State) (operatorsKey constantsKey contextKey sourceKey : String)
    (operatorsCaptured : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table.operators origins)
    (constantsCaptured : applySubst bindings (.var constantsKey) = DeclarationTable.tableAtom table constants)
    (contextCaptured : applySubst bindings (.var contextKey) = ContextLookup.contextAtom context)
    (sourceCaptured : applySubst bindings (.var sourceKey) = sourceAtom (.const constant occurrence)) :
    BoundCalls.CorePath.PureReturns program bindings state (.expression [.symbol "hol-light:read-term", .var operatorsKey,
      .var constantsKey, .var contextKey, .var sourceKey]) state
      (if (HOLLight.TypeMatching.matchType schema occurrence TypeSubst.empty).isSome then
        .expression [.symbol "Some", termAtom registeredOperatorAtom constants (context.map Var.ty) (.const constant occurrence)]
       else .symbol "None") := by
  let initial := environment (OperatorTable.tableAtom table.operators origins)
    (DeclarationTable.tableAtom table constants) context (.const constant occurrence)
  let bound := [("type", typeAtom registeredOperatorAtom occurrence),
    ("name", nameAtom (DefinitionAdapters.constantName constant))] ++ initial
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings initial state state "hol-light:read-term"
    [operatorsKey, constantsKey, contextKey, sourceKey] equation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, operatorsCaptured, constantsCaptured, contextCaptured, sourceCaptured] using
      clause (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
        context (.const constant occurrence)
  · rw [body_shape]
    apply BoundCalls.CorePath.case_returns program initial bound state state state (.var "source")
      (sourceAtom (.const constant occurrence)) constantBody _ _ cases (read_cases_encoded cases)
    · exact BoundCalls.CorePath.variable_returns program _ state "source"
    · rw [first_cases]
      simp [initial, bound, environment, sourceAtom, SpaceSemantics.selectCase,
        SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · exact constant_body_returns world table origins constants context constant schema occurrence registered
        schemaFormed occurrenceFormed resolved state

/-- Every actual instance of a declaration has a successful source read,
including schemas with repeated parameters and simultaneous instantiation. -/
theorem authored_constant_instance_certificate (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (context : List SourceVar) (constant : Const) (schema occurrence : Ty)
    (registered : world.signature.constants constant = some schema)
    (schemaFormed : TypeFormed world.signature schema) (occurrenceFormed : TypeFormed world.signature occurrence)
    (resolved : TypeFormation.Resolved world.signature occurrence)
    (instantiated : ConstantInstance world.signature constant occurrence)
    (bindings : Subst) (state : State) (operatorsKey constantsKey contextKey sourceKey : String)
    (operatorsCaptured : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table.operators origins)
    (constantsCaptured : applySubst bindings (.var constantsKey) = DeclarationTable.tableAtom table constants)
    (contextCaptured : applySubst bindings (.var contextKey) = ContextLookup.contextAtom context)
    (sourceCaptured : applySubst bindings (.var sourceKey) = sourceAtom (.const constant occurrence)) :
    BoundCalls.CorePath.PureReturns program bindings state (.expression [.symbol "hol-light:read-term", .var operatorsKey,
      .var constantsKey, .var contextKey, .var sourceKey]) state
      (.expression [.symbol "Some", termAtom registeredOperatorAtom constants (context.map Var.ty) (.const constant occurrence)]) := by
  obtain ⟨after, matched⟩ :=
    (HOLLight.TypeMatching.constant_admission_iff world.signature constant schema occurrence registered).mpr instantiated
  simpa [matched] using authored_constant_read_certificate world table origins constants context constant schema occurrence
    registered schemaFormed occurrenceFormed resolved bindings state operatorsKey constantsKey contextKey sourceKey
    operatorsCaptured constantsCaptured contextCaptured sourceCaptured

/-- A formed carrier annotation still cannot authorize a constant occurrence
when it is not an instance of the constant's declaration schema. -/
theorem authored_wrong_constant_instance_refused_certificate (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (context : List SourceVar) (constant : Const) (schema occurrence : Ty)
    (registered : world.signature.constants constant = some schema)
    (schemaFormed : TypeFormed world.signature schema) (occurrenceFormed : TypeFormed world.signature occurrence)
    (resolved : TypeFormation.Resolved world.signature occurrence)
    (wrong : ¬ ConstantInstance world.signature constant occurrence)
    (bindings : Subst) (state : State) (operatorsKey constantsKey contextKey sourceKey : String)
    (operatorsCaptured : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table.operators origins)
    (constantsCaptured : applySubst bindings (.var constantsKey) = DeclarationTable.tableAtom table constants)
    (contextCaptured : applySubst bindings (.var contextKey) = ContextLookup.contextAtom context)
    (sourceCaptured : applySubst bindings (.var sourceKey) = sourceAtom (.const constant occurrence)) :
    BoundCalls.CorePath.PureReturns program bindings state (.expression [.symbol "hol-light:read-term", .var operatorsKey,
      .var constantsKey, .var contextKey, .var sourceKey]) state (.symbol "None") := by
  have rejected : HOLLight.TypeMatching.matchType schema occurrence TypeSubst.empty = none := by
    cases matched : HOLLight.TypeMatching.matchType schema occurrence TypeSubst.empty with
    | none => rfl
    | some after =>
        exact False.elim (wrong ((HOLLight.TypeMatching.constant_admission_iff world.signature constant schema occurrence
          registered).mp ⟨after, matched⟩))
  simpa [rejected] using authored_constant_read_certificate world table origins constants context constant schema occurrence
    registered schemaFormed occurrenceFormed resolved bindings state operatorsKey constantsKey contextKey sourceKey
    operatorsCaptured constantsCaptured contextCaptured sourceCaptured

/-- Source names and type names are resolved separately from shared typing
and declaration formation. Applications and binders retain these obligations
at every position, including beneath nested abstractions. -/
def SourceResolved (signature : Signature) : SourceTerm → Prop
  | .var name type => name.namespaceComponents = [] ∧ TypeFormation.Resolved signature type
  | .const _ type => TypeFormation.Resolved signature type
  | .app function argument => SourceResolved signature function ∧ SourceResolved signature argument
  | .abs name domain body => name.namespaceComponents = [] ∧
      TypeFormation.Resolved signature domain ∧ SourceResolved signature body
termination_by source => sizeOf source

private theorem context_types_formed (signature : Signature) (context : List SourceVar)
    (formed : ∀ binder ∈ context, TypeFormed signature binder.ty) : ContextFormed signature (context.map Var.ty) := by
  intro type member
  obtain ⟨binder, binderMember, rfl⟩ := List.mem_map.mp member
  exact formed binder binderMember

private theorem body_returns (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (source : SourceTerm) (resolved : SourceResolved world.signature source)
    (context : List SourceVar) (contextFormed : ∀ binder ∈ context, TypeFormed world.signature binder.ty)
    (annotations : AnnotationsFormed world.signature (source.toDB context))
    (type : Ty) (typed : source.inferType = some type) (state : State) :
    BoundCalls.CorePath.PureReturns program
      (environment (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) context source)
      state equation.body state
      (.expression [.symbol "Some", termAtom registeredOperatorAtom constants (context.map Var.ty) (source.toDB context)]) := by
  let operators := OperatorTable.tableAtom table.operators origins
  let declarations := DeclarationTable.tableAtom table constants
  rw [body_shape]
  cases source with
  | var name annotation =>
      simp only [SourceResolved] at resolved
      let needle : SourceVar := ⟨name, annotation⟩
      let initial := environment operators declarations context (.var name annotation)
      let bound := [("type", typeAtom registeredOperatorAtom annotation), ("name", nameAtom name)] ++ initial
      have formed : TypeFormed world.signature annotation := by
        cases found : boundIndex needle context with
        | none =>
            simp only [needle] at found
            simp only [SourceTerm.toDB, found] at annotations
            cases annotations with
            | free formed => exact formed
        | some index =>
            exact (context_types_formed world.signature context contextFormed).lookup world.signature
              (DBTerm.boundIndex_preserves_type found)
      apply BoundCalls.CorePath.case_returns program initial bound state state state (.var "source") (sourceAtom (.var name annotation))
        variableBody _ _ cases (read_cases_encoded cases)
      · exact BoundCalls.CorePath.variable_returns program _ state "source"
      · simp [all_cases, initial, bound, environment, sourceAtom, sourceVariableAtom, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · exact variable_body_returns world table origins constants context contextFormed needle resolved.1 formed resolved.2 state
  | const constant annotation =>
      simp only [SourceResolved] at resolved
      simp only [SourceTerm.toDB] at annotations
      cases annotations with
      | constant formed instantiated =>
          obtain ⟨schema, witness, registered, realized⟩ := instantiated
          obtain ⟨after, matched⟩ :=
            (HOLLight.TypeMatching.matching_iff_instance schema annotation).mpr ⟨witness, realized⟩
          let initial := environment operators declarations context (.const constant annotation)
          let bound := [("type", typeAtom registeredOperatorAtom annotation),
            ("name", nameAtom (DefinitionAdapters.constantName constant))] ++ initial
          apply BoundCalls.CorePath.case_returns program initial bound state state state (.var "source") (sourceAtom (.const constant annotation))
            constantBody _ _ cases (read_cases_encoded cases)
          · exact BoundCalls.CorePath.variable_returns program _ state "source"
          · simp [all_cases, initial, bound, environment, sourceAtom, SpaceSemantics.selectCase,
              SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
          · simpa [matched, bound, initial, operators, declarations] using constant_body_returns world table origins constants context constant schema annotation
              registered (world.constantTypes constant schema registered) formed resolved state
  | app function argument =>
      simp only [SourceResolved] at resolved
      simp only [SourceTerm.toDB] at annotations
      cases annotations with
      | app functionFormed argumentFormed =>
          have applicationChecked := (DBTerm.inferType_toDB context (.app function argument)).trans typed
          simp only [SourceTerm.toDB] at applicationChecked
          obtain ⟨domain, functionChecked, argumentChecked⟩ := DBTerm.inferType_app_eq_some_iff.mp applicationChecked
          let initial := environment operators declarations context (.app function argument)
          let bound := [("argument", sourceAtom argument), ("function", sourceAtom function)] ++ initial
          let fn := termAtom registeredOperatorAtom constants (context.map Var.ty) (function.toDB context)
          let value := termAtom registeredOperatorAtom constants (context.map Var.ty) (argument.toDB context)
          apply BoundCalls.CorePath.case_returns program initial bound state state state (.var "source") (sourceAtom (.app function argument))
            applicationBody _ _ cases (read_cases_encoded cases)
          · exact BoundCalls.CorePath.variable_returns program _ state "source"
          · simp [all_cases, initial, bound, environment, sourceAtom, SpaceSemantics.selectCase,
              SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
          · rw [application_shape]
            let entered := [("value", value), ("fn", fn)] ++ bound
            apply BoundCalls.CorePath.case_returns program bound entered state state state _
              (.expression [.expression [.symbol "Some", fn], .expression [.symbol "Some", value]])
              functionBody _ _ (rows applicationBody) (read_cases_encoded _)
            · apply data_pair_returns bound state
                [.symbol "hol-light:read-term", .var "operators", .var "constants", .var "context", .var "function"]
                _ _ _
              · apply read_call_of_returns operators declarations context function bound state
                  (.var "operators") (.var "constants") (.var "context") (.var "function") _
                  (by simpa [bound, initial, environment, applySubst, Subst.lookup] using BoundCalls.CorePath.variable_returns program bound state "operators")
                  (by simpa [bound, initial, environment, applySubst, Subst.lookup] using BoundCalls.CorePath.variable_returns program bound state "constants")
                  (by simpa [bound, initial, environment, applySubst, Subst.lookup] using BoundCalls.CorePath.variable_returns program bound state "context")
                  (by simpa [bound, initial, environment, applySubst, Subst.lookup] using BoundCalls.CorePath.variable_returns program bound state "function")
                exact body_returns world table origins constants function resolved.1 context contextFormed functionFormed
                  (.function domain type) ((DBTerm.inferType_toDB context function).symm.trans functionChecked) state
              · apply read_call_of_returns operators declarations context argument bound state
                  (.var "operators") (.var "constants") (.var "context") (.var "argument") _
                  (by simpa [bound, initial, environment, applySubst, Subst.lookup] using BoundCalls.CorePath.variable_returns program bound state "operators")
                  (by simpa [bound, initial, environment, applySubst, Subst.lookup] using BoundCalls.CorePath.variable_returns program bound state "constants")
                  (by simpa [bound, initial, environment, applySubst, Subst.lookup] using BoundCalls.CorePath.variable_returns program bound state "context")
                  (by simpa [bound, initial, environment, applySubst, Subst.lookup] using BoundCalls.CorePath.variable_returns program bound state "argument")
                exact body_returns world table origins constants argument resolved.2 context contextFormed argumentFormed
                  domain ((DBTerm.inferType_toDB context argument).symm.trans argumentChecked) state
            · simp [application_rows, entered, bound, initial, environment, SpaceSemantics.selectCase,
                SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
            · rw [function_shape]
              let classified := [("codomain", typeAtom registeredOperatorAtom type),
                ("domain", typeAtom registeredOperatorAtom domain)] ++ entered
              apply BoundCalls.CorePath.case_returns program entered classified state state state _
                (.expression [.symbol "Some", typeAtom registeredOperatorAtom (.function domain type)])
                applicationSelected _ _ (rows functionBody) (read_cases_encoded _)
              · exact TermJudgment.authored_term_type_certificate constants entered state (context.map Var.ty)
                  (function.toDB context) (.function domain type) functionChecked "fn"
                  (by simp [entered, fn, applySubst, Subst.lookup])
              · simp [function_rows, classified, entered, bound, initial, environment, Ty.function, typeAtom,
                  Premises.keys, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                  SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
              · unfold applicationSelected
                apply BoundCalls.CorePath.if_returns program classified state state state _ (boolean true) _ _ _
                · apply BoundCalls.CorePath.native_binary_call_returns program classified state state state state "==" _ _
                    (.expression [.symbol "Some", typeAtom registeredOperatorAtom domain])
                    (.expression [.symbol "Some", typeAtom registeredOperatorAtom domain]) (boolean true)
                    (by decide) (by decide) (by decide) (by decide)
                  · exact TermJudgment.authored_term_type_certificate constants classified state (context.map Var.ty)
                      (argument.toDB context) domain argumentChecked "value"
                      (by simp [classified, entered, value, applySubst, Subst.lookup])
                  · simpa [classified, applySubst, Subst.lookup] using
                      BoundCalls.CorePath.unary_constructor_returns program classified state "Some" "domain" (by decide) (by decide)
                  · simp [StdLib.structural_equality, boolean]
                  · decide
                · simp only [boolean, BEq.rfl, ↓reduceIte]
                  apply BoundCalls.CorePath.unary_constructor_of_returns program classified state state "Some" _ _ (by decide) (by decide)
                  simpa [SourceTerm.toDB, termAtom, classified, entered, fn, value, applySubst, Subst.lookup] using
                    BoundCalls.CorePath.constructor_variables_return program classified state "HOL:App" ["fn", "value"] (by decide) (by decide)
  | abs name domain body =>
      simp only [SourceResolved] at resolved
      simp only [SourceTerm.toDB] at annotations
      cases annotations with
      | abs domainFormed bodyFormed =>
          have lambdaChecked := (DBTerm.inferType_toDB context (.abs name domain body)).trans typed
          simp only [SourceTerm.toDB] at lambdaChecked
          obtain ⟨codomain, bodyChecked, _⟩ := DBTerm.inferType_abs_eq_some_iff.mp lambdaChecked
          let initial := environment operators declarations context (.abs name domain body)
          let bound := [("body", sourceAtom body), ("type", typeAtom registeredOperatorAtom domain),
            ("name", nameAtom name)] ++ initial
          let bodyContext : List SourceVar := ⟨name, domain⟩ :: context
          let value := termAtom registeredOperatorAtom constants (bodyContext.map Var.ty) (body.toDB bodyContext)
          apply BoundCalls.CorePath.case_returns program initial bound state state state (.var "source") (sourceAtom (.abs name domain body))
            lambdaBody _ _ cases (read_cases_encoded cases)
          · exact BoundCalls.CorePath.variable_returns program _ state "source"
          · simp [all_cases, initial, bound, environment, sourceAtom, sourceVariableAtom, SpaceSemantics.selectCase,
              SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
          · unfold lambdaBody
            apply BoundCalls.CorePath.if_returns program bound state state state _ (boolean true) _ _ _
            · apply BoundCalls.CorePath.native_binary_call_returns program bound state state state state "==" _ (.symbol "String")
                (.symbol "String") (.symbol "String") (boolean true) (by decide) (by decide) (by decide) (by decide)
              · apply BoundCalls.CorePath.native_variable_call_returns program bound state state "get-type" ["name"] (.symbol "String")
                  (by decide) (by decide) _ (by decide)
                simp [StdLib.string_type_is_string, bound, initial, environment, applySubst, Subst.lookup, nameAtom,
                  show name.namespaceComponents = [] from resolved.1]
              · exact BoundCalls.CorePath.symbol_returns program bound state "String"
              · rfl
              · decide
            · simp only [boolean, BEq.rfl, ↓reduceIte]
              apply BoundCalls.CorePath.if_returns program bound state state state _ (boolean true) _ _ _
              · have returned := TypeFormation.authored_type_formed_certificate world table.operators origins bound state
                  domain resolved.2.1 "operators" "type"
                  (by simp [bound, initial, environment, applySubst, Subst.lookup, operators])
                  (by simp [bound, initial, environment, applySubst, Subst.lookup])
                simpa [(typeFormedB_eq_true_iff world.signature domain).mpr domainFormed] using returned
              · simp only [boolean, BEq.rfl, ↓reduceIte]
                rw [lambda_shape]
                let entered := ("value", value) :: bound
                apply BoundCalls.CorePath.case_returns program bound entered state state state lambdaRead
                  (.expression [.symbol "Some", value])
                  (.expression [.symbol "Some", .expression [.symbol "HOL:Lam", .var "type", .var "value"]])
                  _ _ (rows lambdaResult) (read_cases_encoded _)
                · have contextReturned : BoundCalls.CorePath.PureReturns program bound state
                      (.expression [.symbol "HOL:Cons", .expression [.symbol "Var", .var "name", .var "type"], .var "context"])
                      state (ContextLookup.contextAtom bodyContext) := by
                    simp only [bodyContext, ContextLookup.contextAtom, List.map_cons, Premises.keys]
                    apply BoundCalls.CorePath.binary_constructor_returns program bound state state state "HOL:Cons" _ _ _ _ (by decide) (by decide)
                    · simpa [sourceVariableAtom, bound, initial, environment, applySubst, Subst.lookup] using
                        BoundCalls.CorePath.constructor_variables_return program bound state "Var" ["name", "type"] (by decide) (by decide)
                    · simpa [bound, initial, environment, applySubst, Subst.lookup, ContextLookup.contextAtom] using
                        BoundCalls.CorePath.variable_returns program bound state "context"
                  have recursiveReturned := body_returns world table origins constants body resolved.2.2 bodyContext
                    (by
                      intro binder member
                      rcases List.mem_cons.mp member with rfl | member
                      · exact domainFormed
                      · exact contextFormed binder member)
                    bodyFormed codomain ((DBTerm.inferType_toDB bodyContext body).symm.trans bodyChecked) state
                  exact read_call_of_returns operators declarations bodyContext body bound state
                    (.var "operators") (.var "constants") _ (.var "body") _
                    (by simpa [bound, initial, environment, applySubst, Subst.lookup] using BoundCalls.CorePath.variable_returns program bound state "operators")
                    (by simpa [bound, initial, environment, applySubst, Subst.lookup] using BoundCalls.CorePath.variable_returns program bound state "constants")
                    contextReturned
                    (by simpa [bound, initial, environment, applySubst, Subst.lookup] using BoundCalls.CorePath.variable_returns program bound state "body")
                    recursiveReturned
                · simp [lambda_rows, entered, bound, initial, environment, SpaceSemantics.selectCase,
                    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
                · apply BoundCalls.CorePath.unary_constructor_of_returns program entered state state "Some" _ _ (by decide) (by decide)
                  simpa [SourceTerm.toDB, termAtom, bodyContext, value, entered, bound, initial, environment,
                    applySubst, Subst.lookup] using
                    BoundCalls.CorePath.constructor_variables_return program entered state "HOL:Lam" ["type", "value"] (by decide) (by decide)
termination_by sizeOf source

/-- Every resolved, well-typed source term with formed declarations is read
to its existing positional elaboration, through actual source execution.
The statement covers arbitrary applications and nested abstractions. -/
theorem authored_read_computed_certificate (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (source : SourceTerm) (resolved : SourceResolved world.signature source)
    (context : List SourceVar) (contextFormed : ∀ binder ∈ context, TypeFormed world.signature binder.ty)
    (annotations : AnnotationsFormed world.signature (source.toDB context))
    (type : Ty) (typed : source.inferType = some type)
    (bindings : Subst) (state : State) (operatorsExpression constantsExpression contextExpression sourceExpression : Atom)
    (operatorsReturned : BoundCalls.CorePath.PureReturns program bindings state operatorsExpression state
      (OperatorTable.tableAtom table.operators origins))
    (constantsReturned : BoundCalls.CorePath.PureReturns program bindings state constantsExpression state
      (DeclarationTable.tableAtom table constants))
    (contextReturned : BoundCalls.CorePath.PureReturns program bindings state contextExpression state (ContextLookup.contextAtom context))
    (sourceReturned : BoundCalls.CorePath.PureReturns program bindings state sourceExpression state (sourceAtom source)) :
    BoundCalls.CorePath.PureReturns program bindings state (.expression [.symbol "hol-light:read-term", operatorsExpression,
      constantsExpression, contextExpression, sourceExpression]) state
      (.expression [.symbol "Some", termAtom registeredOperatorAtom constants (context.map Var.ty) (source.toDB context)]) := by
  exact read_call_of_returns _ _ context source bindings state operatorsExpression constantsExpression
    contextExpression sourceExpression _ operatorsReturned constantsReturned contextReturned sourceReturned
    (body_returns world table origins constants source resolved context contextFormed annotations type typed state)

/-- Captured source arguments use the same reader computation. -/
theorem authored_read_certificate (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (source : SourceTerm) (resolved : SourceResolved world.signature source)
    (context : List SourceVar) (contextFormed : ∀ binder ∈ context, TypeFormed world.signature binder.ty)
    (annotations : AnnotationsFormed world.signature (source.toDB context))
    (type : Ty) (typed : source.inferType = some type)
    (bindings : Subst) (state : State) (operatorsKey constantsKey contextKey sourceKey : String)
    (operatorsCaptured : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table.operators origins)
    (constantsCaptured : applySubst bindings (.var constantsKey) = DeclarationTable.tableAtom table constants)
    (contextCaptured : applySubst bindings (.var contextKey) = ContextLookup.contextAtom context)
    (sourceCaptured : applySubst bindings (.var sourceKey) = sourceAtom source) :
    BoundCalls.CorePath.PureReturns program bindings state (.expression [.symbol "hol-light:read-term", .var operatorsKey,
      .var constantsKey, .var contextKey, .var sourceKey]) state
      (.expression [.symbol "Some", termAtom registeredOperatorAtom constants (context.map Var.ty) (source.toDB context)]) := by
  exact authored_read_computed_certificate world table origins constants source resolved context contextFormed annotations
    type typed bindings state (.var operatorsKey) (.var constantsKey) (.var contextKey) (.var sourceKey)
    (by simpa [operatorsCaptured] using BoundCalls.CorePath.variable_returns program bindings state operatorsKey)
    (by simpa [constantsCaptured] using BoundCalls.CorePath.variable_returns program bindings state constantsKey)
    (by simpa [contextCaptured] using BoundCalls.CorePath.variable_returns program bindings state contextKey)
    (by simpa [sourceCaptured] using BoundCalls.CorePath.variable_returns program bindings state sourceKey)


private theorem original_read_call_of_returns (operators constants : Atom) (context : List SourceVar) (source : SourceTerm)
    (bindings : Subst) (state : State) (operatorsExpr constantsExpr contextExpr sourceExpr value : Atom)
    (operatorsComputed : PureReturns program bindings state operatorsExpr state operators)
    (constantsComputed : PureReturns program bindings state constantsExpr state constants)
    (contextComputed : PureReturns program bindings state contextExpr state (ContextLookup.contextAtom context))
    (sourceComputed : PureReturns program bindings state sourceExpr state (sourceAtom source))
    (bodyComputed : PureReturns program (environment operators constants context source) state equation.body state value) :
    PureReturns program bindings state (.expression [.symbol "hol-light:read-term", operatorsExpr,
      constantsExpr, contextExpr, sourceExpr]) state value := by
  apply call_returns program bindings state state "hol-light:read-term" _ _ (by decide) _ (by decide)
  apply evaluated_argument_returns program bindings state state state (.function "hol-light:read-term")
    operatorsExpr _ _ [constantsExpr, contextExpr, sourceExpr] [] 0 (by decide) operatorsComputed
  apply evaluated_argument_returns program bindings state state state (.function "hol-light:read-term")
    constantsExpr _ _ [contextExpr, sourceExpr] [_] 1 (by decide) constantsComputed
  apply evaluated_argument_returns program bindings state state state (.function "hol-light:read-term")
    contextExpr _ _ [sourceExpr] [_, _] 2 (by decide) contextComputed
  apply evaluated_argument_returns program bindings state state state (.function "hol-light:read-term")
    sourceExpr _ _ [] [_, _, _] 3 (by decide) sourceComputed
  exact authored_function_arguments_return program bindings (environment operators constants context source)
    state state "hol-light:read-term" [_, _, _, _] 4 equation.body _ (by decide) (by decide)
    (clause operators constants context source) bodyComputed

theorem authored_read_computed_return (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (source : SourceTerm) (resolved : SourceResolved world.signature source)
    (context : List SourceVar) (contextFormed : ∀ binder ∈ context, TypeFormed world.signature binder.ty)
    (annotations : AnnotationsFormed world.signature (source.toDB context))
    (type : Ty) (typed : source.inferType = some type)
    (bindings : Subst) (state : State) (operatorsExpression constantsExpression contextExpression sourceExpression : Atom)
    (operatorsReturned : PureReturns program bindings state operatorsExpression state
      (OperatorTable.tableAtom table.operators origins))
    (constantsReturned : PureReturns program bindings state constantsExpression state
      (DeclarationTable.tableAtom table constants))
    (contextReturned : PureReturns program bindings state contextExpression state (ContextLookup.contextAtom context))
    (sourceReturned : PureReturns program bindings state sourceExpression state (sourceAtom source)) :
    PureReturns program bindings state (.expression [.symbol "hol-light:read-term", operatorsExpression,
      constantsExpression, contextExpression, sourceExpression]) state
      (.expression [.symbol "Some", termAtom registeredOperatorAtom constants (context.map Var.ty) (source.toDB context)]) := by
  exact original_read_call_of_returns _ _ context source bindings state operatorsExpression constantsExpression
    contextExpression sourceExpression _ operatorsReturned constantsReturned contextReturned sourceReturned
    (body_returns world table origins constants source resolved context contextFormed annotations type typed state).original

theorem authored_variable_read_return (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (context : List SourceVar) (contextFormed : ∀ binder ∈ context, TypeFormed world.signature binder.ty)
    (needle : SourceVar) (globalName : needle.name.namespaceComponents = [])
    (formed : TypeFormed world.signature needle.ty) (resolved : TypeFormation.Resolved world.signature needle.ty)
    (bindings : Subst) (state : State) (operatorsKey constantsKey contextKey sourceKey : String)
    (operatorsCaptured : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table.operators origins)
    (constantsCaptured : applySubst bindings (.var constantsKey) = DeclarationTable.tableAtom table constants)
    (contextCaptured : applySubst bindings (.var contextKey) = ContextLookup.contextAtom context)
    (sourceCaptured : applySubst bindings (.var sourceKey) = sourceAtom (.var needle.name needle.ty)) :
    PureReturns program bindings state (.expression [.symbol "hol-light:read-term", .var operatorsKey,
      .var constantsKey, .var contextKey, .var sourceKey]) state (.expression [.symbol "Some",
        termAtom registeredOperatorAtom constants (context.map Var.ty)
          ((SourceTerm.var needle.name needle.ty).toDB context)]) :=
  (authored_variable_read_certificate world table origins constants context contextFormed needle globalName formed resolved bindings state operatorsKey constantsKey contextKey sourceKey operatorsCaptured constantsCaptured contextCaptured sourceCaptured).original

theorem authored_variable_read_bound_return (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (context : List SourceVar) (contextFormed : ∀ binder ∈ context, TypeFormed world.signature binder.ty)
    (needle : SourceVar) (globalName : needle.name.namespaceComponents = [])
    (formed : TypeFormed world.signature needle.ty) (resolved : TypeFormation.Resolved world.signature needle.ty)
    (bindings : Subst) (state : State) (operatorsKey constantsKey contextKey sourceKey : String)
    (operatorsCaptured : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table.operators origins)
    (constantsCaptured : applySubst bindings (.var constantsKey) = DeclarationTable.tableAtom table constants)
    (contextCaptured : applySubst bindings (.var contextKey) = ContextLookup.contextAtom context)
    (sourceCaptured : applySubst bindings (.var sourceKey) = sourceAtom (.var needle.name needle.ty)) :
    BoundCalls.PureReturns program bindings state (.expression [.symbol "hol-light:read-term", .var operatorsKey,
      .var constantsKey, .var contextKey, .var sourceKey]) state (.expression [.symbol "Some",
        termAtom registeredOperatorAtom constants (context.map Var.ty)
          ((SourceTerm.var needle.name needle.ty).toDB context)]) :=
  (authored_variable_read_certificate world table origins constants context contextFormed needle globalName formed resolved bindings state operatorsKey constantsKey contextKey sourceKey operatorsCaptured constantsCaptured contextCaptured sourceCaptured).extended

theorem authored_constant_read_return (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (context : List SourceVar) (constant : Const) (schema occurrence : Ty)
    (registered : world.signature.constants constant = some schema)
    (schemaFormed : TypeFormed world.signature schema) (occurrenceFormed : TypeFormed world.signature occurrence)
    (resolved : TypeFormation.Resolved world.signature occurrence)
    (bindings : Subst) (state : State) (operatorsKey constantsKey contextKey sourceKey : String)
    (operatorsCaptured : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table.operators origins)
    (constantsCaptured : applySubst bindings (.var constantsKey) = DeclarationTable.tableAtom table constants)
    (contextCaptured : applySubst bindings (.var contextKey) = ContextLookup.contextAtom context)
    (sourceCaptured : applySubst bindings (.var sourceKey) = sourceAtom (.const constant occurrence)) :
    PureReturns program bindings state (.expression [.symbol "hol-light:read-term", .var operatorsKey,
      .var constantsKey, .var contextKey, .var sourceKey]) state
      (if (HOLLight.TypeMatching.matchType schema occurrence TypeSubst.empty).isSome then
        .expression [.symbol "Some", termAtom registeredOperatorAtom constants (context.map Var.ty) (.const constant occurrence)]
       else .symbol "None") :=
  (authored_constant_read_certificate world table origins constants context constant schema occurrence registered schemaFormed occurrenceFormed resolved bindings state operatorsKey constantsKey contextKey sourceKey operatorsCaptured constantsCaptured contextCaptured sourceCaptured).original

theorem authored_constant_read_bound_return (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (context : List SourceVar) (constant : Const) (schema occurrence : Ty)
    (registered : world.signature.constants constant = some schema)
    (schemaFormed : TypeFormed world.signature schema) (occurrenceFormed : TypeFormed world.signature occurrence)
    (resolved : TypeFormation.Resolved world.signature occurrence)
    (bindings : Subst) (state : State) (operatorsKey constantsKey contextKey sourceKey : String)
    (operatorsCaptured : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table.operators origins)
    (constantsCaptured : applySubst bindings (.var constantsKey) = DeclarationTable.tableAtom table constants)
    (contextCaptured : applySubst bindings (.var contextKey) = ContextLookup.contextAtom context)
    (sourceCaptured : applySubst bindings (.var sourceKey) = sourceAtom (.const constant occurrence)) :
    BoundCalls.PureReturns program bindings state (.expression [.symbol "hol-light:read-term", .var operatorsKey,
      .var constantsKey, .var contextKey, .var sourceKey]) state
      (if (HOLLight.TypeMatching.matchType schema occurrence TypeSubst.empty).isSome then
        .expression [.symbol "Some", termAtom registeredOperatorAtom constants (context.map Var.ty) (.const constant occurrence)]
       else .symbol "None") :=
  (authored_constant_read_certificate world table origins constants context constant schema occurrence registered schemaFormed occurrenceFormed resolved bindings state operatorsKey constantsKey contextKey sourceKey operatorsCaptured constantsCaptured contextCaptured sourceCaptured).extended

theorem authored_constant_instance_return (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (context : List SourceVar) (constant : Const) (schema occurrence : Ty)
    (registered : world.signature.constants constant = some schema)
    (schemaFormed : TypeFormed world.signature schema) (occurrenceFormed : TypeFormed world.signature occurrence)
    (resolved : TypeFormation.Resolved world.signature occurrence)
    (instantiated : ConstantInstance world.signature constant occurrence)
    (bindings : Subst) (state : State) (operatorsKey constantsKey contextKey sourceKey : String)
    (operatorsCaptured : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table.operators origins)
    (constantsCaptured : applySubst bindings (.var constantsKey) = DeclarationTable.tableAtom table constants)
    (contextCaptured : applySubst bindings (.var contextKey) = ContextLookup.contextAtom context)
    (sourceCaptured : applySubst bindings (.var sourceKey) = sourceAtom (.const constant occurrence)) :
    PureReturns program bindings state (.expression [.symbol "hol-light:read-term", .var operatorsKey,
      .var constantsKey, .var contextKey, .var sourceKey]) state
      (.expression [.symbol "Some", termAtom registeredOperatorAtom constants (context.map Var.ty) (.const constant occurrence)]) :=
  (authored_constant_instance_certificate world table origins constants context constant schema occurrence registered schemaFormed occurrenceFormed resolved instantiated bindings state operatorsKey constantsKey contextKey sourceKey operatorsCaptured constantsCaptured contextCaptured sourceCaptured).original

theorem authored_constant_instance_bound_return (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (context : List SourceVar) (constant : Const) (schema occurrence : Ty)
    (registered : world.signature.constants constant = some schema)
    (schemaFormed : TypeFormed world.signature schema) (occurrenceFormed : TypeFormed world.signature occurrence)
    (resolved : TypeFormation.Resolved world.signature occurrence)
    (instantiated : ConstantInstance world.signature constant occurrence)
    (bindings : Subst) (state : State) (operatorsKey constantsKey contextKey sourceKey : String)
    (operatorsCaptured : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table.operators origins)
    (constantsCaptured : applySubst bindings (.var constantsKey) = DeclarationTable.tableAtom table constants)
    (contextCaptured : applySubst bindings (.var contextKey) = ContextLookup.contextAtom context)
    (sourceCaptured : applySubst bindings (.var sourceKey) = sourceAtom (.const constant occurrence)) :
    BoundCalls.PureReturns program bindings state (.expression [.symbol "hol-light:read-term", .var operatorsKey,
      .var constantsKey, .var contextKey, .var sourceKey]) state
      (.expression [.symbol "Some", termAtom registeredOperatorAtom constants (context.map Var.ty) (.const constant occurrence)]) :=
  (authored_constant_instance_certificate world table origins constants context constant schema occurrence registered schemaFormed occurrenceFormed resolved instantiated bindings state operatorsKey constantsKey contextKey sourceKey operatorsCaptured constantsCaptured contextCaptured sourceCaptured).extended

theorem authored_wrong_constant_instance_refused (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (context : List SourceVar) (constant : Const) (schema occurrence : Ty)
    (registered : world.signature.constants constant = some schema)
    (schemaFormed : TypeFormed world.signature schema) (occurrenceFormed : TypeFormed world.signature occurrence)
    (resolved : TypeFormation.Resolved world.signature occurrence)
    (wrong : ¬ ConstantInstance world.signature constant occurrence)
    (bindings : Subst) (state : State) (operatorsKey constantsKey contextKey sourceKey : String)
    (operatorsCaptured : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table.operators origins)
    (constantsCaptured : applySubst bindings (.var constantsKey) = DeclarationTable.tableAtom table constants)
    (contextCaptured : applySubst bindings (.var contextKey) = ContextLookup.contextAtom context)
    (sourceCaptured : applySubst bindings (.var sourceKey) = sourceAtom (.const constant occurrence)) :
    PureReturns program bindings state (.expression [.symbol "hol-light:read-term", .var operatorsKey,
      .var constantsKey, .var contextKey, .var sourceKey]) state (.symbol "None") :=
  (authored_wrong_constant_instance_refused_certificate world table origins constants context constant schema occurrence registered schemaFormed occurrenceFormed resolved wrong bindings state operatorsKey constantsKey contextKey sourceKey operatorsCaptured constantsCaptured contextCaptured sourceCaptured).original

theorem authored_wrong_constant_instance_bound_refused (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (context : List SourceVar) (constant : Const) (schema occurrence : Ty)
    (registered : world.signature.constants constant = some schema)
    (schemaFormed : TypeFormed world.signature schema) (occurrenceFormed : TypeFormed world.signature occurrence)
    (resolved : TypeFormation.Resolved world.signature occurrence)
    (wrong : ¬ ConstantInstance world.signature constant occurrence)
    (bindings : Subst) (state : State) (operatorsKey constantsKey contextKey sourceKey : String)
    (operatorsCaptured : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table.operators origins)
    (constantsCaptured : applySubst bindings (.var constantsKey) = DeclarationTable.tableAtom table constants)
    (contextCaptured : applySubst bindings (.var contextKey) = ContextLookup.contextAtom context)
    (sourceCaptured : applySubst bindings (.var sourceKey) = sourceAtom (.const constant occurrence)) :
    BoundCalls.PureReturns program bindings state (.expression [.symbol "hol-light:read-term", .var operatorsKey,
      .var constantsKey, .var contextKey, .var sourceKey]) state (.symbol "None") :=
  (authored_wrong_constant_instance_refused_certificate world table origins constants context constant schema occurrence registered schemaFormed occurrenceFormed resolved wrong bindings state operatorsKey constantsKey contextKey sourceKey operatorsCaptured constantsCaptured contextCaptured sourceCaptured).extended

theorem authored_read_return (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (source : SourceTerm) (resolved : SourceResolved world.signature source)
    (context : List SourceVar) (contextFormed : ∀ binder ∈ context, TypeFormed world.signature binder.ty)
    (annotations : AnnotationsFormed world.signature (source.toDB context))
    (type : Ty) (typed : source.inferType = some type)
    (bindings : Subst) (state : State) (operatorsKey constantsKey contextKey sourceKey : String)
    (operatorsCaptured : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table.operators origins)
    (constantsCaptured : applySubst bindings (.var constantsKey) = DeclarationTable.tableAtom table constants)
    (contextCaptured : applySubst bindings (.var contextKey) = ContextLookup.contextAtom context)
    (sourceCaptured : applySubst bindings (.var sourceKey) = sourceAtom source) :
    PureReturns program bindings state (.expression [.symbol "hol-light:read-term", .var operatorsKey,
      .var constantsKey, .var contextKey, .var sourceKey]) state
      (.expression [.symbol "Some", termAtom registeredOperatorAtom constants (context.map Var.ty) (source.toDB context)]) :=
  (authored_read_certificate world table origins constants source resolved context contextFormed annotations type typed bindings state operatorsKey constantsKey contextKey sourceKey operatorsCaptured constantsCaptured contextCaptured sourceCaptured).original

theorem authored_read_bound_return (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (source : SourceTerm) (resolved : SourceResolved world.signature source)
    (context : List SourceVar) (contextFormed : ∀ binder ∈ context, TypeFormed world.signature binder.ty)
    (annotations : AnnotationsFormed world.signature (source.toDB context))
    (type : Ty) (typed : source.inferType = some type)
    (bindings : Subst) (state : State) (operatorsKey constantsKey contextKey sourceKey : String)
    (operatorsCaptured : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table.operators origins)
    (constantsCaptured : applySubst bindings (.var constantsKey) = DeclarationTable.tableAtom table constants)
    (contextCaptured : applySubst bindings (.var contextKey) = ContextLookup.contextAtom context)
    (sourceCaptured : applySubst bindings (.var sourceKey) = sourceAtom source) :
    BoundCalls.PureReturns program bindings state (.expression [.symbol "hol-light:read-term", .var operatorsKey,
      .var constantsKey, .var contextKey, .var sourceKey]) state
      (.expression [.symbol "Some", termAtom registeredOperatorAtom constants (context.map Var.ty) (source.toDB context)]) :=
  (authored_read_certificate world table origins constants source resolved context contextFormed annotations type typed bindings state operatorsKey constantsKey contextKey sourceKey operatorsCaptured constantsCaptured contextCaptured sourceCaptured).extended

end Mettapedia.Languages.HOLLight.MeTTa.TermReading
