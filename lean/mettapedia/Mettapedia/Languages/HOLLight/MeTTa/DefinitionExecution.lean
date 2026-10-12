import Mettapedia.Languages.HOLLight.MeTTa.DeclarationExecution
import Mettapedia.Languages.HOLLight.MeTTa.TypeVariables

/-!
# Authored constant definitions in a registered theory context

The source operation reads a definition in the old declaration context,
checks closedness and hidden parameters, constructs its retained identity,
and publishes the defining equation. Publication still checks both addresses.
The logical interpretation uses the existing constant-definition admission;
an executable theorem-shaped value is never a substitute for its derivation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.DefinitionExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters
open Eval (clauses clauses_use_only_the_named_equations read_cases_encoded)
open Effects (State boolean)
open Representation (registeredOperatorAtom termAtom)
open TypeSubstitution (typeAtom)

private theorem false_test : (boolean false == boolean true) = false := by decide

def definedConstant (name : String) (body : CheckedSourceTerm) : Const :=
  .mk (Name.global name) (.defined body.source)

def definitionIdentity (constants : Const → Atom) (name : String) (body : CheckedSourceTerm) : Atom :=
  .expression [.symbol "HOL:Defined", .grounded (.string name), typeAtom registeredOperatorAtom body.ty,
    termAtom registeredOperatorAtom constants [] body.canonical.term]

def definitionRequest (name : String) (body : CheckedSourceTerm) : Atom :=
  .expression [.symbol "DEFINITION", .grounded (.string name), typeAtom registeredOperatorAtom body.ty,
    TermReading.sourceAtom body.source]

def extendedConstants (constants : Atom) (identity : Const → Atom) (name : String) (body : CheckedSourceTerm) : Atom :=
  .expression [.symbol "HOL:Cons", .expression [.symbol "HOL:Entry", .grounded (.string name),
    .expression [.symbol "HOL:Constant", typeAtom registeredOperatorAtom body.ty,
      definitionIdentity identity name body]], constants]

def definedIdentities (before : Const → Atom) (name : String) (body : CheckedSourceTerm) : Const → Atom :=
  DeclarationTable.extendIdentity before (definedConstant name body) (definitionIdentity before name body)

def definingEquation (body : CheckedSourceTerm) (name : String) : DBTerm :=
  CanonicalTerm.equalityDB body.ty (.const (definedConstant name body) body.ty) body.canonical.term

def definitionResult (context : TheoryContext) (table : DeclarationTable.Table context)
    (origins : TypeOp → Atom) (constants : Const → Atom) (axioms key : Atom)
    (name : String) (body : CheckedSourceTerm) (cache : List (Atom × Atom))
    (receipts : List ReceiptKeys.Entry) : Atom :=
  Publication.result (OperatorTable.tableAtom table.operators origins)
    (extendedConstants (DeclarationTable.tableAtom table constants) constants name body) axioms key
    (definitionRequest name body) (.symbol "HOL:Nil")
    (termAtom registeredOperatorAtom (definedIdentities constants name body) [] (definingEquation body name))
    (.symbol "HOL:Nil") [] cache receipts

/-- Classification retains both actual definition guards before publication. -/
def classifiedResult (context : TheoryContext) (table : DeclarationTable.Table context)
    (origins : TypeOp → Atom) (constants : Const → Atom) (axioms key : Atom)
    (name : String) (body : CheckedSourceTerm) (cache : List (Atom × Atom))
    (receipts : List ReceiptKeys.Entry) : Atom :=
  if FreeVariables.freeAtoms registeredOperatorAtom body.canonical.term = [] then
    if body.canonical.term.typeVariables ⊆ body.ty.typeVariables then
      definitionResult context table origins constants axioms key name body cache receipts
    else .symbol "None"
  else .symbol "None"

private def equation : SpaceSemantics.Equation :=
  (definitionsSource.program.equations.filter (fun row => row.head == "hol-light:definition"))[0]'(by decide)
private def identityExpression : Atom :=
  .expression [.symbol "HOL:Defined", .var "name", .var "schema", .var "body"]
private def extendedExpression : Atom := .expression [.symbol "HOL:State", .var "operators",
  .expression [.symbol "HOL:Cons", .expression [.symbol "HOL:Entry", .var "name",
    .expression [.symbol "HOL:Constant", .var "schema", .var "identity"]], .var "constants"],
  .var "axioms", .var "cache", .var "receipts"]
private def requestExpression : Atom := .expression [.symbol "DEFINITION", .var "name", .var "schema", .var "source"]
private def theoremExpression : Atom := .expression [.symbol "hol-light:theorem-eq", .symbol "HOL:Nil",
  .expression [.symbol "HOL:C", .var "identity", .var "schema"], .var "body", .symbol "HOL:Nil", .symbol "DEFINITION"]
private def publicationExpression : Atom := .expression [.symbol "hol-light:publish", .var "extended", .var "key",
  requestExpression, theoremExpression]
private def extensionBody : Atom := .expression [.symbol "let", .var "identity", identityExpression,
  .expression [.symbol "let", .var "extended", extendedExpression, publicationExpression]]
private def parameterGuard : Atom := .expression [.symbol "if", .expression [.symbol "hol-light:subset",
  .expression [.symbol "hol-light:term-type-vars", .var "body"],
  .expression [.symbol "hol-light:type-vars", .var "schema"]], extensionBody, .symbol "None"]
private def closedGuard : Atom := .expression [.symbol "if", .expression [.symbol "==",
  .expression [.symbol "hol-light:free-vars", .var "body"], .symbol "HOL:Nil"], parameterGuard, .symbol "None"]
private def typeGuard : Atom := .expression [.symbol "if", .expression [.symbol "==",
  .expression [.symbol "hol-light:term-type", .var "body"], .expression [.symbol "Some", .var "schema"]],
  closedGuard, .symbol "None"]
private def readCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "None", .expression [.symbol "Some", .var "body"]], typeGuard),
   (.var "malformed", .symbol "None")]
private def readBody : Atom := .expression [.symbol "case", .expression [
  .expression [.symbol "hol-light:lookup", .var "name", .var "constants"],
  .expression [.symbol "hol-light:read", .var "state", .var "source"]],
  .expression (readCases.map fun row => .expression [row.1, row.2])]
private def formationGuard : Atom := .expression [.symbol "if",
  .expression [.symbol "hol-light:type-formed", .var "operators", .var "schema"], readBody, .symbol "None"]
private def nameGuard : Atom := .expression [.symbol "if", .expression [.symbol "==",
  .expression [.symbol "get-type", .var "name"], .symbol "String"], formationGuard, .symbol "None"]
private def worldExpression : Atom := .expression [.symbol "HOL:State", .var "operators", .var "constants",
  .var "axioms", .var "cache", .var "receipts"]
private def environment (operators declarations axioms key : Atom) (name : String) (body : CheckedSourceTerm)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) : Subst :=
  [("source", TermReading.sourceAtom body.source), ("schema", typeAtom registeredOperatorAtom body.ty),
   ("name", .grounded (.string name)), ("key", key), ("receipts", ReceiptKeys.table receipts),
   ("cache", Lookup.table cache), ("axioms", axioms), ("constants", declarations), ("operators", operators)]

private theorem shape : equation.body = .expression [.symbol "let", .var "state", worldExpression, nameGuard] := by decide
private theorem clause (operators declarations axioms key : Atom) (name : String) (body : CheckedSourceTerm)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) :
    clauses program "hol-light:definition"
      [ProofLookup.sourceState operators declarations axioms (ReceiptKeys.table receipts) cache,
       key, .grounded (.string name), typeAtom registeredOperatorAtom body.ty, TermReading.sourceAtom body.source] =
      [.evaluate (environment operators declarations axioms key name body cache receipts) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:definition") = [equation] := rfl
  rw [unique]
  have formals : equation.arguments =
      [.expression [.symbol "HOL:State", .var "operators", .var "constants", .var "axioms", .var "cache", .var "receipts"],
       .var "key", .var "name", .var "schema", .var "source"] := by decide
  simp [formals, environment, ProofLookup.sourceState, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem extension_returns (context : TheoryContext) (table : DeclarationTable.Table context)
    (origins : TypeOp → Atom) (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (axioms key : Atom) (name : String) (body : CheckedSourceTerm)
    (formed : AnnotationsFormed context.signature body.canonical.term)
    (fresh : .constant (Name.global name) ∉ context.names)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) (state : State) :
    BoundCalls.PureReturns program
      (("body", termAtom registeredOperatorAtom constants [] body.canonical.term) ::
       ("state", ProofLookup.sourceState (OperatorTable.tableAtom table.operators origins)
         (DeclarationTable.tableAtom table constants) axioms (ReceiptKeys.table receipts) cache) ::
       environment (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
         axioms key name body cache receipts) state extensionBody state
      (definitionResult context table origins constants axioms key name body cache receipts) := by
  let before := environment (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
    axioms key name body cache receipts
  let world := ProofLookup.sourceState (OperatorTable.tableAtom table.operators origins)
    (DeclarationTable.tableAtom table constants) axioms (ReceiptKeys.table receipts) cache
  let bound := ("body", termAtom registeredOperatorAtom constants [] body.canonical.term) :: ("state", world) :: before
  let identityBound := ("identity", definitionIdentity constants name body) :: bound
  let extendedWorld := ProofLookup.sourceState (OperatorTable.tableAtom table.operators origins)
    (extendedConstants (DeclarationTable.tableAtom table constants) constants name body) axioms
    (ReceiptKeys.table receipts) cache
  let extendedBound := ("extended", extendedWorld) :: identityBound
  have identityReturned : BoundCalls.CorePath.PureReturns program bound state identityExpression state
      (definitionIdentity constants name body) := by
    unfold identityExpression definitionIdentity
    simpa [bound, before, environment, applySubst, Subst.lookup] using
      BoundCalls.CorePath.constructor_variables_return program bound state "HOL:Defined" ["name", "schema", "body"]
        (by decide) (by decide)
  have extendedReturned : BoundCalls.CorePath.PureReturns program identityBound state extendedExpression state extendedWorld := by
    unfold extendedExpression extendedWorld ProofLookup.sourceState
    apply BoundCalls.CorePath.constructor_return program identityBound state "HOL:State" _ _ (by decide) (by decide)
    refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil))))
    · simpa [identityBound, bound, before, environment, applySubst, Subst.lookup] using
        BoundCalls.CorePath.variable_returns program identityBound state "operators"
    · unfold extendedConstants
      apply BoundCalls.CorePath.constructor_return program identityBound state "HOL:Cons" _ _ (by decide) (by decide)
      refine .cons ?_ (.cons ?_ .nil)
      · apply BoundCalls.CorePath.constructor_return program identityBound state "HOL:Entry" _ _ (by decide) (by decide)
        refine .cons ?_ (.cons ?_ .nil)
        · simpa [identityBound, bound, before, environment, applySubst, Subst.lookup] using
            BoundCalls.CorePath.variable_returns program identityBound state "name"
        · simpa [identityBound, bound, before, environment, applySubst, Subst.lookup] using
            BoundCalls.CorePath.constructor_variables_return program identityBound state "HOL:Constant" ["schema", "identity"]
              (by decide) (by decide)
      · simpa [identityBound, bound, before, environment, applySubst, Subst.lookup] using
          BoundCalls.CorePath.variable_returns program identityBound state "constants"
    · simpa [identityBound, bound, before, environment, applySubst, Subst.lookup] using
        BoundCalls.CorePath.variable_returns program identityBound state "axioms"
    · simpa [identityBound, bound, before, environment, applySubst, Subst.lookup] using
        BoundCalls.CorePath.variable_returns program identityBound state "cache"
    · simpa [identityBound, bound, before, environment, applySubst, Subst.lookup] using
        BoundCalls.CorePath.variable_returns program identityBound state "receipts"
  have newIdentity : definedIdentities constants name body (definedConstant name body) = definitionIdentity constants name body := by
    simp [definedIdentities, DeclarationTable.extendIdentity, Const.same_eq_true_iff]
  have oldBody : termAtom registeredOperatorAtom (definedIdentities constants name body) [] body.canonical.term =
      termAtom registeredOperatorAtom constants [] body.canonical.term := by
    apply CacheAuthorization.term_atom_fresh_identity context (definedConstant name body)
      (context.constant_unregistered _ (by simpa [definedConstant, constantName] using fresh))
      constants (definitionIdentity constants name body) body.canonical.term formed []
  have equalityRetained : definedIdentities constants name body Const.equality =
      DeclarationTable.primitiveIdentity Const.equality := by
    simpa [definedIdentities, DeclarationTable.extendIdentity, Const.same_eq_true_iff, definedConstant, Const.equality] using equalityIdentity
  have theoremReturned : BoundCalls.CorePath.PureReturns program extendedBound state theoremExpression state
      (.expression [.symbol "Some", Publication.value (.symbol "HOL:Nil")
        (termAtom registeredOperatorAtom (definedIdentities constants name body) [] (definingEquation body name))
        (.symbol "HOL:Nil") (.symbol "DEFINITION")]) := by
    unfold theoremExpression Publication.value definingEquation
    apply Equality.authored_theorem_equality_computed_certificate (definedIdentities constants name body)
      extendedBound state [] (.const (definedConstant name body) body.ty) body.canonical.term body.ty
      (by simp [DBTerm.inferType]) body.canonical.checked equalityRetained
      (.symbol "HOL:Nil") (.symbol "HOL:Nil") (.symbol "DEFINITION")
    · exact BoundCalls.CorePath.symbol_returns program extendedBound state "HOL:Nil"
    · simp only [termAtom, newIdentity]
      simpa [extendedBound, identityBound, bound, before, environment, applySubst, Subst.lookup] using
        BoundCalls.CorePath.constructor_variables_return program extendedBound state "HOL:C" ["identity", "schema"]
          (by decide) (by decide)
    · rw [oldBody]
      simpa [extendedBound, identityBound, bound, applySubst, Subst.lookup] using
        BoundCalls.CorePath.variable_returns program extendedBound state "body"
    · exact BoundCalls.CorePath.symbol_returns program extendedBound state "HOL:Nil"
    · exact BoundCalls.CorePath.symbol_returns program extendedBound state "DEFINITION"
  have published : BoundCalls.PureReturns program extendedBound state publicationExpression state
      (definitionResult context table origins constants axioms key name body cache receipts) := by
    unfold publicationExpression definitionResult
    apply Publication.authored_publish_computed_arguments_bound_return
      (OperatorTable.tableAtom table.operators origins)
      (extendedConstants (DeclarationTable.tableAtom table constants) constants name body) axioms key
      (.symbol "HOL:Nil")
      (termAtom registeredOperatorAtom (definedIdentities constants name body) [] (definingEquation body name))
      (.symbol "HOL:Nil") (.symbol "DEFINITION") (definitionRequest name body) []
      (fun bindings phase captured => Premises.authored_definition_premises_certificate bindings phase
        (.grounded (.string name)) (typeAtom registeredOperatorAtom body.ty) (TermReading.sourceAtom body.source) "request" captured)
      cache receipts extendedBound state (.var "extended") (.var "key") requestExpression theoremExpression
    · simpa [extendedBound, applySubst, Subst.lookup] using BoundCalls.variable_returns program extendedBound state "extended"
    · simpa [extendedBound, identityBound, bound, before, environment, applySubst, Subst.lookup] using
        BoundCalls.variable_returns program extendedBound state "key"
    · have requestReturned : BoundCalls.CorePath.PureReturns program extendedBound state requestExpression state
          (definitionRequest name body) := by
        unfold requestExpression definitionRequest
        simpa [extendedBound, identityBound, bound, before, environment, applySubst, Subst.lookup] using
          BoundCalls.CorePath.constructor_variables_return program extendedBound state "DEFINITION" ["name", "schema", "source"]
            (by decide) (by decide)
      exact requestReturned.extended
    · exact theoremReturned.extended
  unfold extensionBody
  refine BoundCalls.let_returns program bound identityBound state state state (.var "identity") identityExpression
    _ (definitionIdentity constants name body) _ identityReturned.extended ?_ ?_
  · simp [identityBound, bound, before, environment, SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
  · refine BoundCalls.let_returns program identityBound extendedBound state state state (.var "extended") extendedExpression
      publicationExpression extendedWorld _ extendedReturned.extended ?_ published
    simp [extendedBound, identityBound, bound, before, environment, SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]

private theorem body_returns (context : TheoryContext) (table : DeclarationTable.Table context)
    (origins : TypeOp → Atom) (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (axioms key : Atom) (name : String) (body : CheckedSourceTerm)
    (sourceResolved : TermReading.SourceResolved context.signature body.source)
    (schemaResolved : TypeFormation.Resolved context.signature body.ty)
    (formed : AnnotationsFormed context.signature body.canonical.term)
    (schemaFormed : TypeFormed context.signature body.ty)
    (fresh : .constant (Name.global name) ∉ context.names)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) (state : State) :
    BoundCalls.PureReturns program
      (environment (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
        axioms key name body cache receipts) state equation.body state
      (classifiedResult context table origins constants axioms key name body cache receipts) := by
  let before := environment (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
    axioms key name body cache receipts
  let world := ProofLookup.sourceState (OperatorTable.tableAtom table.operators origins)
    (DeclarationTable.tableAtom table constants) axioms (ReceiptKeys.table receipts) cache
  let withState := ("state", world) :: before
  let withBody := ("body", termAtom registeredOperatorAtom constants [] body.canonical.term) :: withState
  have worldReturned : BoundCalls.CorePath.PureReturns program before state worldExpression state world := by
    unfold worldExpression world ProofLookup.sourceState
    simpa [before, environment, applySubst, Subst.lookup] using
      BoundCalls.CorePath.constructor_variables_return program before state "HOL:State"
        ["operators", "constants", "axioms", "cache", "receipts"] (by decide) (by decide)
  rw [shape]
  refine BoundCalls.let_returns program before withState state state state (.var "state") worldExpression
    nameGuard world _ worldReturned.extended ?_ ?_
  · simp [withState, before, environment, SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
  · unfold nameGuard
    apply BoundCalls.if_returns program withState state state state _ (boolean true) _ _ _
    · have nameReturned : BoundCalls.CorePath.PureReturns program withState state
          (.expression [.symbol "==", .expression [.symbol "get-type", .var "name"], .symbol "String"])
          state (boolean true) := by
        apply BoundCalls.CorePath.native_binary_call_returns program withState state state state state "=="
          _ (.symbol "String") (.symbol "String") (.symbol "String") (boolean true)
          (by decide) (by decide) (by decide) (by decide) _ _ _ (by decide)
        · apply BoundCalls.CorePath.native_variable_call_returns program withState state state "get-type"
            ["name"] (.symbol "String") (by decide) (by decide) _ (by decide)
          simp [withState, before, environment, applySubst, Subst.lookup, StdLib.string_type_is_string]
        · exact BoundCalls.CorePath.symbol_returns program withState state "String"
        · simp [StdLib.structural_equality, boolean]
      exact nameReturned.extended
    · simp only [boolean, BEq.rfl, ↓reduceIte]
      unfold formationGuard
      apply BoundCalls.if_returns program withState state state state _ (boolean true) _ _ _
      · have formedReturned := TypeFormation.authored_type_formed_certificate context table.operators origins
          withState state body.ty schemaResolved "operators" "schema"
          (by simp [withState, before, environment, applySubst, Subst.lookup])
          (by simp [withState, before, environment, applySubst, Subst.lookup])
        have valid := (typeFormedB_eq_true_iff _ _).mpr schemaFormed
        simpa only [valid] using formedReturned.extended
      · simp only [boolean, BEq.rfl, ↓reduceIte]
        unfold readBody
        apply BoundCalls.case_returns program withState withBody state state state _
          (.expression [.symbol "None", .expression [.symbol "Some",
            termAtom registeredOperatorAtom constants [] body.canonical.term]]) typeGuard _ _ readCases
          (read_cases_encoded readCases)
        · have bothReturned : BoundCalls.CorePath.PureReturns program withState state
              (.expression [.expression [.symbol "hol-light:lookup", .var "name", .var "constants"],
                .expression [.symbol "hol-light:read", .var "state", .var "source"]]) state
              (.expression [.symbol "None", .expression [.symbol "Some",
                termAtom registeredOperatorAtom constants [] body.canonical.term]]) := by
            refine .step rfl (Eval.step_transition rfl) ?_
            apply BoundCalls.CorePath.arguments_return program withState state _ _ _ [] 0
            refine .cons ?_ (.cons ?_ .nil)
            · have absent := DeclarationTable.fresh_name_absent table constants (Name.global name) fresh
              have lookupReturned := Lookup.authored_lookup_certificate withState state (.grounded (.string name))
                (DeclarationTable.entriesAtom table constants) "name" "constants"
                (by simp [withState, before, environment, applySubst, Subst.lookup])
                (by simp [withState, before, environment, DeclarationTable.tableAtom, applySubst, Subst.lookup])
              have absentSource : (DeclarationTable.entriesAtom table constants).lookup (.grounded (.string name)) = none := absent
              simpa only [absentSource, Lookup.answer] using lookupReturned
            · exact InferenceExecution.authored_state_read_certificate context table origins constants body.source sourceResolved
                formed body.ty body.checked withState state axioms (ReceiptKeys.table receipts) cache "state" "source"
                (by simp [withState, world, before, environment, applySubst, Subst.lookup])
                (by simp [withState, before, environment, applySubst, Subst.lookup])
          exact bothReturned.extended
        · simp [readCases, withBody, withState, before, environment, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · unfold typeGuard
          apply BoundCalls.if_returns program withBody state state state _ (boolean true) _ _ _
          · have typedReturned : BoundCalls.CorePath.PureReturns program withBody state
                (.expression [.symbol "==", .expression [.symbol "hol-light:term-type", .var "body"],
                  .expression [.symbol "Some", .var "schema"]]) state (boolean true) := by
              apply BoundCalls.CorePath.native_binary_call_returns program withBody state state state state "==" _ _
                (.expression [.symbol "Some", typeAtom registeredOperatorAtom body.ty])
                (.expression [.symbol "Some", typeAtom registeredOperatorAtom body.ty]) (boolean true)
                (by decide) (by decide) (by decide) (by decide) _ _ _ (by decide)
              · exact TermJudgment.authored_term_type_certificate constants withBody state [] body.canonical.term body.ty
                  body.canonical.checked "body" (by simp [withBody, applySubst, Subst.lookup])
              · simpa [withBody, withState, before, environment, applySubst, Subst.lookup] using
                  BoundCalls.CorePath.unary_constructor_returns program withBody state "Some" "schema" (by decide) (by decide)
              · simp [StdLib.structural_equality, boolean]
            exact typedReturned.extended
          · simp only [boolean, BEq.rfl, ↓reduceIte]
            unfold closedGuard
            apply BoundCalls.if_returns program withBody state state state _
              (boolean (decide (FreeVariables.freeAtoms registeredOperatorAtom body.canonical.term = []))) _ _ _
            · exact (TypeVariables.authored_closed_body_certificate registeredOperatorAtom constants []
                body.canonical.term withBody state "body" (by simp [withBody, applySubst, Subst.lookup])).extended
            · by_cases closed : FreeVariables.freeAtoms registeredOperatorAtom body.canonical.term = []
              · simp only [closed, decide_true, boolean, BEq.rfl, ↓reduceIte, classifiedResult]
                unfold parameterGuard
                apply BoundCalls.if_returns program withBody state state state _
                  (boolean (decide (body.canonical.term.typeVariables ⊆ body.ty.typeVariables))) _ _ _
                · exact (TypeVariables.authored_hidden_parameters_certificate registeredOperatorAtom constants
                    body.canonical.term body.ty body.canonical.checked withBody state "body" "schema"
                    (by simp [withBody, applySubst, Subst.lookup])
                    (by simp [withBody, withState, before, environment, applySubst, Subst.lookup])).extended
                · by_cases parameters : body.canonical.term.typeVariables ⊆ body.ty.typeVariables
                  · simp only [parameters, decide_true, boolean, BEq.rfl, ↓reduceIte]
                    exact extension_returns context table origins constants equalityIdentity axioms key name body
                      formed fresh cache receipts state
                  · simpa only [parameters, decide_false, false_test, Bool.false_eq_true, ↓reduceIte] using
                      BoundCalls.symbol_returns program withBody state "None"
              · simpa only [closed, decide_false, false_test, Bool.false_eq_true, ↓reduceIte, classifiedResult] using
                  BoundCalls.symbol_returns program withBody state "None"

/-- Every resolved checked body executes the actual source operation,
including the reader and both definition guards. Admitted definitions reach
the publisher; occupied publication addresses retain its refusal. -/
theorem authored_definition_classified_return (context : TheoryContext) (table : DeclarationTable.Table context)
    (origins : TypeOp → Atom) (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (axioms key : Atom) (name : String) (body : CheckedSourceTerm)
    (sourceResolved : TermReading.SourceResolved context.signature body.source)
    (schemaResolved : TypeFormation.Resolved context.signature body.ty)
    (formed : AnnotationsFormed context.signature body.canonical.term)
    (schemaFormed : TypeFormed context.signature body.ty)
    (fresh : .constant (Name.global name) ∉ context.names)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : State) (stateKey keyName nameKey schemaKey sourceKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
      axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (nameCaptured : applySubst bindings (.var nameKey) = .grounded (.string name))
    (schemaCaptured : applySubst bindings (.var schemaKey) = typeAtom registeredOperatorAtom body.ty)
    (sourceCaptured : applySubst bindings (.var sourceKey) = TermReading.sourceAtom body.source) :
    BoundCalls.PureReturns program bindings state
      (.expression [.symbol "hol-light:definition", .var stateKey, .var keyName, .var nameKey, .var schemaKey, .var sourceKey]) state
      (classifiedResult context table origins constants axioms key name body cache receipts) := by
  apply BoundCalls.authored_variable_call_returns program bindings
    (environment (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
      axioms key name body cache receipts) state state "hol-light:definition"
    [stateKey, keyName, nameKey, schemaKey, sourceKey] equation.body _
    (by decide) (by decide) (by decide) _
    (body_returns context table origins constants equalityIdentity axioms key name body sourceResolved schemaResolved
      formed schemaFormed fresh cache receipts state) (by decide)
  simpa only [List.map_cons, List.map_nil, stateCaptured, keyCaptured, nameCaptured, schemaCaptured, sourceCaptured] using
    clause (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
      axioms key name body cache receipts

/-- Successful side conditions specialize the classified operation; address
freshness is still decided by the actual publisher. -/
theorem authored_definition_return (context : TheoryContext) (table : DeclarationTable.Table context)
    (origins : TypeOp → Atom) (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (axioms key : Atom) (name : String) (body : CheckedSourceTerm)
    (sourceResolved : TermReading.SourceResolved context.signature body.source)
    (schemaResolved : TypeFormation.Resolved context.signature body.ty)
    (formed : AnnotationsFormed context.signature body.canonical.term)
    (schemaFormed : TypeFormed context.signature body.ty)
    (fresh : .constant (Name.global name) ∉ context.names)
    (closed : body.canonical.term.HasNoFreeVariables)
    (parameters : body.canonical.term.typeVariables ⊆ body.ty.typeVariables)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : State) (stateKey keyName nameKey schemaKey sourceKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
      axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (nameCaptured : applySubst bindings (.var nameKey) = .grounded (.string name))
    (schemaCaptured : applySubst bindings (.var schemaKey) = typeAtom registeredOperatorAtom body.ty)
    (sourceCaptured : applySubst bindings (.var sourceKey) = TermReading.sourceAtom body.source) :
    BoundCalls.PureReturns program bindings state
      (.expression [.symbol "hol-light:definition", .var stateKey, .var keyName, .var nameKey, .var schemaKey, .var sourceKey]) state
      (definitionResult context table origins constants axioms key name body cache receipts) := by
  have returned := authored_definition_classified_return context table origins constants equalityIdentity axioms key name body
    sourceResolved schemaResolved formed schemaFormed fresh cache receipts bindings state
    stateKey keyName nameKey schemaKey sourceKey stateCaptured keyCaptured nameCaptured schemaCaptured sourceCaptured
  have empty := (FreeVariables.free_atoms_nil_iff registeredOperatorAtom body.canonical.term).mpr closed
  simpa only [classifiedResult, empty, parameters, ↓reduceIte] using returned

theorem source_check (body : CheckedSourceTerm) : body.source.check = some body.canonical := by
  unfold SourceTerm.check
  dsimp only
  have checked : (body.source.toDB []).inferType [] = some body.ty := body.canonical.checked
  split
  · rename_i type inferred
    have equal : type = body.ty := Option.some.inj (inferred.symm.trans checked)
    subst type
    rfl
  · rename_i refused
    rw [refused] at checked
    cases checked

/-- The two computed source conditions are exactly the existing definition
admission conditions on a checked source body. Name freshness stays separate. -/
theorem side_conditions_iff (context : TheoryContext) (name : String) (body : CheckedSourceTerm) :
    ConstantAdmissible context.names (Name.global name) body.source ↔
      .constant (Name.global name) ∉ context.names ∧
      body.canonical.term.HasNoFreeVariables ∧ body.canonical.term.typeVariables ⊆ body.ty.typeVariables := by
  simp [ConstantAdmissible, ConstantDefinitionAdmissible, source_check body, CheckedSourceTerm.canonical]

def registeredResult (context : TheoryContext) (name : String) (body : CheckedSourceTerm)
    (formed : TypeFormed context.signature body.ty) (fresh : .constant (Name.global name) ∉ context.names) :
    ContextConstantDefinitionResult :=
  { context := context.addConstant (definedConstant name body) body.ty formed fresh
    definition := body.canonical
    output := makeConstantDefinition (Name.global name) body.source body.canonical }

/-- Formation supplies actual instance witnesses, after which the existing
source admission computes the retained definition and registered extension. -/
theorem registered_admission_constructed (context : TheoryContext) (name : String) (body : CheckedSourceTerm)
    (formed : AnnotationsFormed context.signature body.canonical.term)
    (schemaFormed : TypeFormed context.signature body.ty)
    (fresh : .constant (Name.global name) ∉ context.names)
    (closed : body.canonical.term.HasNoFreeVariables)
    (parameters : body.canonical.term.typeVariables ⊆ body.ty.typeVariables) :
    ∃ witnesses, admitConstantInTheory context witnesses (Name.global name) body.source =
      some (registeredResult context name body schemaFormed fresh) := by
  obtain ⟨witnesses, sourceChecked⟩ := checkSource_complete context.signature (source_check body) formed
  refine ⟨witnesses, ?_⟩
  have schemaAccepted : typeFormedB context.signature body.canonical.ty = true :=
    (typeFormedB_eq_true_iff _ _).mpr schemaFormed
  have parametersAccepted : body.canonical.term.typeVariables ⊆ body.canonical.ty.typeVariables := parameters
  have closedAccepted := (DBTerm.hasNoFreeVariables_eq_true_iff _).mpr closed
  simp [admitConstantInTheory, sourceChecked, schemaAccepted, fresh, admitConstant,
    checkConstantDefinition, source_check body, closedAccepted, parametersAccepted, registeredResult, definedConstant]
  rfl

/-- The admitted source output has a real registered derivation. Formation of
the equality declaration is required in the old signature and transported;
formation of the new constant and the entire equation is constructed here. -/
theorem registered_definition_derives (policy : AxiomPolicy) (context : TheoryContext)
    (name : String) (body : CheckedSourceTerm)
    (formed : AnnotationsFormed context.signature body.canonical.term)
    (schemaFormed : TypeFormed context.signature body.ty)
    (fresh : .constant (Name.global name) ∉ context.names)
    (closed : body.canonical.term.HasNoFreeVariables)
    (parameters : body.canonical.term.typeVariables ⊆ body.ty.typeVariables)
    (equalityFormed : TypeFormed context.signature (Ty.equality body.ty))
    (equalityRegistered : ConstantInstance context.signature Const.equality (Ty.equality body.ty)) :
    TheoryDerives policy (registeredResult context name body schemaFormed fresh).context
      (registeredResult context name body schemaFormed fresh).output.definitionTheorem := by
  obtain ⟨witnesses, accepted⟩ := registered_admission_constructed context name body formed schemaFormed fresh closed parameters
  apply TheoryDerives.constantDefinition accepted
  let extended := context.addConstant (definedConstant name body) body.ty schemaFormed fresh
  have included := context.addConstant_includes (definedConstant name body) body.ty schemaFormed fresh
  have constantFormed : AnnotationsFormed extended.signature (.const (definedConstant name body) body.ty) := by
    apply AnnotationsFormed.constant (schemaFormed.mono included)
    exact ⟨body.ty, TypeSubst.empty, context.addConstant_registered (definedConstant name body) body.ty schemaFormed fresh, by simp⟩
  have equationFormed : AnnotationsFormed extended.signature (definingEquation body name) :=
    .app (.app (.constant (equalityFormed.mono included) (equalityRegistered.mono included)) constantFormed)
      (formed.mono included)
  change (AnnotationsFormed extended.signature (definingEquation body name) ∧
    ∀ hypothesis ∈ (∅ : Finset CanonicalTerm), AnnotationsFormed extended.signature hypothesis.term) ∧
    ∀ commitment ∈ (∅ : Finset Sequent), SequentFormed extended.signature commitment
  exact ⟨⟨equationFormed, by simp⟩, by simp⟩

/-- Every old earned proof and its encoded identity, hypothesis, dependency
and origin survive this exact registered definition extension. -/
theorem definition_preserves_old_cache (policy : AxiomPolicy) (context : TheoryContext)
    (constants : Const → Atom) (name : String) (body : CheckedSourceTerm)
    (schemaFormed : TypeFormed context.signature body.ty)
    (fresh : .constant (Name.global name) ∉ context.names)
    (cache : CacheAuthorization.Cache) (valid : CacheAuthorization.Valid policy context cache) :
    CacheAuthorization.Valid policy (registeredResult context name body schemaFormed fresh).context cache ∧
      CacheAuthorization.entries (definedIdentities constants name body) cache = CacheAuthorization.entries constants cache :=
  CacheAuthorization.add_constant_transports_cache policy context (definedConstant name body) body.ty schemaFormed fresh
    constants (definitionIdentity constants name body) cache valid

end Mettapedia.Languages.HOLLight.MeTTa.DefinitionExecution
