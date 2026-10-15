import Mettapedia.Languages.HOLLight.MeTTa.CacheAuthorization
import Mettapedia.Languages.MeTTa.PeTTa.CoreExecution

/-!
# Registered declarations through the authored HOL state operations

The retained declaration body checks the source name, the formed schema and
the first matching declaration row. Its successful result is the existing
registered context extension. Cached derivations keep their identities,
dependencies and origins under that extension. This module concerns global
source names and resolved schema syntax; definition admission and model
extension are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.DeclarationExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters
open Eval (clauses read_cases_encoded clauses_use_only_the_named_equations)
open Effects (State boolean)
open TypeSubstitution (nameAtom typeAtom)
open Representation (registeredOperatorAtom)

/-- Constructed declaration histories contain exactly the constant names
registered in their signatures. An arbitrary context may additionally reserve
names, so the converse is proved as a history invariant rather than assumed
for every context record. -/
def ConstantNamesExact (context : TheoryContext) : Prop :=
  ∀ name, .constant name ∈ context.names ↔
    ∃ constant schema, context.signature.constants constant = some schema ∧ constantName constant = name

theorem empty_constant_names_exact : ConstantNamesExact TheoryContext.empty := by
  intro name
  simp [TheoryContext.empty]

theorem add_operator_constant_names_exact (context : TheoryContext)
    (exactNames : ConstantNamesExact context) (operator : TypeOp) (arity : Nat)
    (fresh : .typeOperator (operatorName operator) ∉ context.names) :
    ConstantNamesExact (context.addTypeOperator operator arity fresh) := by
  intro name
  simpa [TheoryContext.addTypeOperator, Signature.addTypeOperator] using exactNames name

theorem add_constant_names_exact (context : TheoryContext)
    (exactNames : ConstantNamesExact context) (constant : Const) (schema : Ty)
    (formed : TypeFormed context.signature schema)
    (fresh : .constant (constantName constant) ∉ context.names) :
    ConstantNamesExact (context.addConstant constant schema formed fresh) := by
  intro name
  constructor
  · intro member
    have membership : name = constantName constant ∨ .constant name ∈ context.names := by
      simpa [TheoryContext.addConstant] using member
    rcases membership with rfl | earlier
    · exact ⟨constant, schema, context.addConstant_registered constant schema formed fresh, rfl⟩
    · obtain ⟨old, oldSchema, registered, named⟩ := (exactNames name).mp earlier
      exact ⟨old, oldSchema, (context.addConstant_includes constant schema formed fresh).2 _ _ registered, named⟩
  · rintro ⟨candidate, candidateSchema, registered, named⟩
    by_cases same : Const.same candidate constant = true
    · have equal := (Const.same_eq_true_iff candidate constant).mp same
      subst candidate
      simp [TheoryContext.addConstant, ← named]
    · have old : context.signature.constants candidate = some candidateSchema := by
        simpa [TheoryContext.addConstant, Signature.addConstant, same] using registered
      have before := (exactNames name).mpr ⟨candidate, candidateSchema, old, named⟩
      exact Finset.mem_insert_of_mem before

theorem primitive_constant_names_exact : ConstantNamesExact SourceProfile.primitiveContext := by
  have booleanNames := add_operator_constant_names_exact TheoryContext.empty empty_constant_names_exact
    TypeOp.bool 0 (by simp [TheoryContext.empty])
  have baseNames := add_operator_constant_names_exact ContextControls.booleanContext booleanNames
    TypeOp.function 2 (by simp [ContextControls.booleanContext, TheoryContext.addTypeOperator,
      TheoryContext.empty, operatorName, TypeOp.bool, TypeOp.function, Name.global])
  have coreNames := add_constant_names_exact ContextControls.baseContext baseNames
    Const.equality (Ty.equality (.var ContextControls.equalityParameter)) ContextControls.equality_schema_formed
    (by simp [ContextControls.baseContext, ContextControls.booleanContext, TheoryContext.addTypeOperator,
      TheoryContext.empty, constantName, Const.equality])
  have individualNames := add_operator_constant_names_exact ContextControls.coreContext coreNames
    SourceProfile.individualOperator 0 (by simp [ContextControls.coreContext, ContextControls.baseContext,
      ContextControls.booleanContext, TheoryContext.addConstant, TheoryContext.addTypeOperator,
      TheoryContext.empty, operatorName, SourceProfile.individualOperator, TypeOp.bool, TypeOp.function, Name.global])
  exact add_constant_names_exact SourceProfile.individualContext individualNames
    ModelInterpretation.selectionConstant (ModelInterpretation.selectionType (.var ContextControls.equalityParameter))
    SourceProfile.selection_schema_formed
    (by simp [SourceProfile.individualContext, ContextControls.coreContext, ContextControls.baseContext,
      ContextControls.booleanContext, TheoryContext.addConstant, TheoryContext.addTypeOperator,
      TheoryContext.empty, constantName, ModelInterpretation.selectionConstant, Const.equality, Name.global])

/-- First-match source absence is exactly semantic name freshness in a
constructed history. Reserved names in arbitrary contexts are not forgotten. -/
theorem constant_name_absent_iff (context : TheoryContext)
    (exactNames : ConstantNamesExact context) (table : DeclarationTable.Table context)
    (identity : Const → Atom) (name : Name) :
    (DeclarationTable.entriesAtom table identity).lookup (nameAtom name) = none ↔
      .constant name ∉ context.names := by
  constructor
  · intro absent member
    obtain ⟨constant, schema, registered, named⟩ := (exactNames name).mp member
    have found := DeclarationTable.lookup_registered table identity constant schema registered
    rw [named, absent] at found
    cases found
  · exact DeclarationTable.fresh_name_absent table identity name

def constant (name : String) : Const := .mk (Name.global name) .undefined

def constantRequest (name : String) (schema : Ty) : Atom :=
  .expression [.symbol "DECLARE_CONSTANT", .grounded (.string name),
    typeAtom registeredOperatorAtom schema]

def constantIdentity (name : String) : Atom :=
  .expression [.symbol "HOL:Primitive", .grounded (.string name)]

def constantAfter (operators constants axioms key : Atom) (name : String) (schema : Ty)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) : Atom :=
  ProofLookup.sourceState operators
    (.expression [.symbol "HOL:Cons", .expression [.symbol "HOL:Entry",
      .grounded (.string name), .expression [.symbol "HOL:Constant",
        typeAtom registeredOperatorAtom schema, constantIdentity name]], constants])
    axioms (ReceiptKeys.table (⟨key, constantRequest name schema, []⟩ :: receipts)) cache

def constantResult (context : TheoryContext) (table : DeclarationTable.Table context)
    (origin : TypeOp → Atom) (identity : Const → Atom) (axioms key : Atom)
    (name : String) (schema : Ty) (cache : List (Atom × Atom))
    (receipts : List ReceiptKeys.Entry) : Atom :=
  if typeFormedB context.signature schema then
    if (DeclarationTable.entriesAtom table identity).lookup (.grounded (.string name)) = none then
      .expression [.symbol "Some", constantAfter (OperatorTable.tableAtom table.operators origin)
        (DeclarationTable.tableAtom table identity) axioms key name schema cache receipts]
    else .symbol "None"
  else .symbol "None"

/-- For constructed contexts, the real source result admits exactly a formed
schema at a fresh name. The execution certificate below computes this result. -/
theorem constant_result_admitted_iff (context : TheoryContext)
    (exactNames : ConstantNamesExact context) (table : DeclarationTable.Table context)
    (origin : TypeOp → Atom) (identity : Const → Atom) (axioms key : Atom)
    (name : String) (schema : Ty) (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) :
    constantResult context table origin identity axioms key name schema cache receipts ≠ .symbol "None" ↔
      TypeFormed context.signature schema ∧ .constant (Name.global name) ∉ context.names := by
  have freshness := constant_name_absent_iff context exactNames table identity (Name.global name)
  cases formed : typeFormedB context.signature schema with
  | false =>
      have unformed : ¬ TypeFormed context.signature schema := by
        intro typed
        have accepted := (typeFormedB_eq_true_iff _ _).mpr typed
        rw [formed] at accepted
        cases accepted
      simp [constantResult, formed, unformed]
  | true =>
      have typed := (typeFormedB_eq_true_iff _ _).mp formed
      rw [← freshness]
      by_cases absent : (DeclarationTable.entriesAtom table identity).lookup (.grounded (.string name)) = none
      · simp [constantResult, formed, typed, absent]
      · simp [constantResult, formed, typed, absent]

private def constantEquation : SpaceSemantics.Equation :=
  (definitionsSource.program.equations.filter
    (fun row => row.head == "hol-light:declare-constant"))[0]'(by decide)

private def constantInsertion : Atom := .expression [.symbol "Some",
  .expression [.symbol "HOL:State", .var "operators",
    .expression [.symbol "HOL:Cons", .expression [.symbol "HOL:Entry", .var "name",
      .expression [.symbol "HOL:Constant", .var "schema",
        .expression [.symbol "HOL:Primitive", .var "name"]]], .var "constants"],
    .var "axioms", .var "cache",
    .expression [.symbol "HOL:Cons", .expression [.symbol "HOL:Receipt", .var "key",
      .expression [.symbol "DECLARE_CONSTANT", .var "name", .var "schema"], .symbol "HOL:Nil"],
      .var "receipts"]]]

private def constantCases : SpaceSemantics.Cases :=
  [(.symbol "None", constantInsertion), (.var "duplicate", .symbol "None")]

private def constantLookup : Atom := .expression [.symbol "case",
  .expression [.symbol "hol-light:lookup", .var "name", .var "constants"],
  .expression (constantCases.map fun row => .expression [row.1, row.2])]

private def constantGuard : Atom := .expression [.symbol "if",
  .expression [.symbol "hol-light:type-formed", .var "operators", .var "schema"],
  constantLookup, .symbol "None"]

private def constantEnvironment (operators constants axioms key : Atom) (name : String)
    (schema : Ty) (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) : Subst :=
  [("schema", typeAtom registeredOperatorAtom schema), ("name", .grounded (.string name)),
    ("key", key), ("receipts", ReceiptKeys.table receipts), ("cache", Lookup.table cache),
    ("axioms", axioms), ("constants", constants), ("operators", operators)]

private theorem constant_body_shape : constantEquation.body = .expression [.symbol "if",
    .expression [.symbol "==", .expression [.symbol "get-type", .var "name"], .symbol "String"],
    constantGuard, .symbol "None"] := by decide

private theorem constant_clause (operators constants axioms key : Atom) (name : String)
    (schema : Ty) (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) :
    clauses program "hol-light:declare-constant"
      [ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache,
        key, .grounded (.string name), typeAtom registeredOperatorAtom schema] =
      [.evaluate (constantEnvironment operators constants axioms key name schema cache receipts)
        constantEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:declare-constant") =
      [constantEquation] := rfl
  rw [unique]
  have formals : constantEquation.arguments =
      [.expression [.symbol "HOL:State", .var "operators", .var "constants", .var "axioms",
        .var "cache", .var "receipts"], .var "key", .var "name", .var "schema"] := by decide
  simp [formals, constantEnvironment, ProofLookup.sourceState, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem constant_insertion_certificate (operators constants axioms key : Atom)
    (name : String) (schema : Ty) (cache : List (Atom × Atom))
    (receipts : List ReceiptKeys.Entry) (state : State) :
    BoundCalls.CorePath.PureReturns program
      (constantEnvironment operators constants axioms key name schema cache receipts)
      state constantInsertion state
      (.expression [.symbol "Some", constantAfter operators constants axioms key name schema cache receipts]) := by
  let bound := constantEnvironment operators constants axioms key name schema cache receipts
  unfold constantInsertion
  apply BoundCalls.CorePath.unary_constructor_of_returns program bound state state "Some" _ _
    (by decide) (by decide)
  unfold constantAfter ProofLookup.sourceState
  apply BoundCalls.CorePath.constructor_return program bound state "HOL:State" _ _
    (by decide) (by decide)
  refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil))))
  · simpa [bound, constantEnvironment, applySubst, Subst.lookup] using
      BoundCalls.CorePath.variable_returns program bound state "operators"
  · apply BoundCalls.CorePath.constructor_return program bound state "HOL:Cons" _ _
      (by decide) (by decide)
    refine .cons ?_ (.cons ?_ .nil)
    · apply BoundCalls.CorePath.constructor_return program bound state "HOL:Entry" _ _
        (by decide) (by decide)
      refine .cons ?_ (.cons ?_ .nil)
      · simpa [bound, constantEnvironment, applySubst, Subst.lookup] using
          BoundCalls.CorePath.variable_returns program bound state "name"
      · apply BoundCalls.CorePath.constructor_return program bound state "HOL:Constant" _ _
          (by decide) (by decide)
        refine .cons ?_ (.cons ?_ .nil)
        · simpa [bound, constantEnvironment, applySubst, Subst.lookup] using
            BoundCalls.CorePath.variable_returns program bound state "schema"
        · unfold constantIdentity
          simpa [bound, constantEnvironment, applySubst, Subst.lookup] using
            BoundCalls.CorePath.unary_constructor_returns program bound state "HOL:Primitive" "name"
              (by decide) (by decide)
    · simpa [bound, constantEnvironment, applySubst, Subst.lookup] using
        BoundCalls.CorePath.variable_returns program bound state "constants"
  · simpa [bound, constantEnvironment, applySubst, Subst.lookup] using
      BoundCalls.CorePath.variable_returns program bound state "axioms"
  · simpa [bound, constantEnvironment, applySubst, Subst.lookup] using
      BoundCalls.CorePath.variable_returns program bound state "cache"
  · change BoundCalls.CorePath.PureReturns program bound state _ state
      (.expression [.symbol "HOL:Cons", ReceiptKeys.entryAtom ⟨key, constantRequest name schema, []⟩,
        ReceiptKeys.table receipts])
    apply BoundCalls.CorePath.constructor_return program bound state "HOL:Cons" _ _
      (by decide) (by decide)
    refine .cons ?_ (.cons ?_ .nil)
    · unfold ReceiptKeys.entryAtom
      apply BoundCalls.CorePath.constructor_return program bound state "HOL:Receipt" _ _
        (by decide) (by decide)
      refine .cons ?_ (.cons ?_ (.cons ?_ .nil))
      · simpa [bound, constantEnvironment, applySubst, Subst.lookup] using
          BoundCalls.CorePath.variable_returns program bound state "key"
      · unfold constantRequest
        apply BoundCalls.CorePath.constructor_return program bound state "DECLARE_CONSTANT" _ _
          (by decide) (by decide)
        refine .cons ?_ (.cons ?_ .nil)
        · simpa [bound, constantEnvironment, applySubst, Subst.lookup] using
            BoundCalls.CorePath.variable_returns program bound state "name"
        · simpa [bound, constantEnvironment, applySubst, Subst.lookup] using
            BoundCalls.CorePath.variable_returns program bound state "schema"
      · exact BoundCalls.CorePath.symbol_returns program bound state "HOL:Nil"
    · simpa [bound, constantEnvironment, applySubst, Subst.lookup] using
        BoundCalls.CorePath.variable_returns program bound state "receipts"

private theorem constant_body_certificate (context : TheoryContext)
    (table : DeclarationTable.Table context) (origin : TypeOp → Atom) (identity : Const → Atom)
    (axioms key : Atom) (name : String) (schema : Ty)
    (resolved : TypeFormation.Resolved context.signature schema)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) (state : State) :
    BoundCalls.CorePath.PureReturns program
      (constantEnvironment (OperatorTable.tableAtom table.operators origin)
        (DeclarationTable.tableAtom table identity) axioms key name schema cache receipts)
      state constantEquation.body state
      (constantResult context table origin identity axioms key name schema cache receipts) := by
  let operators := OperatorTable.tableAtom table.operators origin
  let constants := DeclarationTable.tableAtom table identity
  let bound := constantEnvironment operators constants axioms key name schema cache receipts
  rw [constant_body_shape]
  apply BoundCalls.CorePath.if_returns program bound state state state _ (boolean true) _ _ _
  · apply BoundCalls.CorePath.native_binary_call_returns program bound state state state state "=="
      _ (.symbol "String") (.symbol "String") (.symbol "String") (boolean true)
      (by decide) (by decide) (by decide) (by decide)
    · apply BoundCalls.CorePath.native_variable_call_returns program bound state state "get-type"
        ["name"] (.symbol "String") (by decide) (by decide) _ (by decide)
      simp [bound, constantEnvironment, applySubst, Subst.lookup, StdLib.string_type_is_string]
    · exact BoundCalls.CorePath.symbol_returns program bound state "String"
    · rfl
    · decide
  · simp only [boolean, BEq.rfl, ↓reduceIte]
    unfold constantGuard
    apply BoundCalls.CorePath.if_returns program bound state state state _
      (boolean (typeFormedB context.signature schema)) _ _ _
    · exact TypeFormation.authored_type_formed_certificate context table.operators origin
        bound state schema resolved "operators" "schema"
        (by simp [bound, constantEnvironment, operators, applySubst, Subst.lookup])
        (by simp [bound, constantEnvironment, applySubst, Subst.lookup])
    · cases formed : typeFormedB context.signature schema with
      | false =>
          simpa [constantResult, formed, boolean] using
            BoundCalls.CorePath.symbol_returns program bound state "None"
      | true =>
          simp only [boolean, BEq.rfl, ↓reduceIte]
          unfold constantLookup
          cases found : (DeclarationTable.entriesAtom table identity).lookup (.grounded (.string name)) with
          | none =>
              apply BoundCalls.CorePath.case_returns program bound bound state state state _
                (.symbol "None") constantInsertion _ _ constantCases (read_cases_encoded constantCases)
              · simpa [found, Lookup.answer] using
                  Lookup.authored_lookup_certificate bound state (.grounded (.string name))
                    (DeclarationTable.entriesAtom table identity) "name" "constants"
                    (by simp [bound, constantEnvironment, applySubst, Subst.lookup])
                    (by simp [bound, constantEnvironment, constants, DeclarationTable.tableAtom,
                      applySubst, Subst.lookup])
              · simp [constantCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
              · simpa [constantResult, formed, found, operators, constants, bound] using
                  constant_insertion_certificate operators constants axioms key name schema cache receipts state
          | some payload =>
              let occupied := ("duplicate", .expression [.symbol "Some", payload]) :: bound
              apply BoundCalls.CorePath.case_returns program bound occupied state state state _
                (.expression [.symbol "Some", payload]) (.symbol "None") _ _ constantCases
                (read_cases_encoded constantCases)
              · simpa [found, Lookup.answer] using
                  Lookup.authored_lookup_certificate bound state (.grounded (.string name))
                    (DeclarationTable.entriesAtom table identity) "name" "constants"
                    (by simp [bound, constantEnvironment, applySubst, Subst.lookup])
                    (by simp [bound, constantEnvironment, constants, DeclarationTable.tableAtom,
                      applySubst, Subst.lookup])
              · simp [constantCases, occupied, bound, constantEnvironment, SpaceSemantics.selectCase,
                  SpaceSemantics.matchValue, matchAtom, Subst.lookup]
              · simpa [constantResult, formed, found] using
                  BoundCalls.CorePath.symbol_returns program occupied state "None"

/-- The actual authored declaration classifies every resolved schema and
registered finite table, including duplicate names and wrong operator arity. -/
theorem authored_constant_certificate (context : TheoryContext)
    (table : DeclarationTable.Table context) (origin : TypeOp → Atom) (identity : Const → Atom)
    (axioms key : Atom) (name : String) (schema : Ty)
    (resolved : TypeFormation.Resolved context.signature schema)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : State) (stateName keyName nameName schemaName : String)
    (worldCaptured : applySubst bindings (.var stateName) =
      ProofLookup.sourceState (OperatorTable.tableAtom table.operators origin)
        (DeclarationTable.tableAtom table identity) axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (nameCaptured : applySubst bindings (.var nameName) = .grounded (.string name))
    (schemaCaptured : applySubst bindings (.var schemaName) = typeAtom registeredOperatorAtom schema) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:declare-constant", .var stateName, .var keyName,
        .var nameName, .var schemaName]) state
      (constantResult context table origin identity axioms key name schema cache receipts) := by
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings
    (constantEnvironment (OperatorTable.tableAtom table.operators origin)
      (DeclarationTable.tableAtom table identity) axioms key name schema cache receipts)
    state state "hol-light:declare-constant" [stateName, keyName, nameName, schemaName]
    constantEquation.body _ (by decide) (by decide) (by decide) _
    (constant_body_certificate context table origin identity axioms key name schema resolved cache receipts state)
    (by decide)
  simpa only [List.map_cons, List.map_nil, worldCaptured, keyCaptured, nameCaptured, schemaCaptured] using
    constant_clause (OperatorTable.tableAtom table.operators origin)
      (DeclarationTable.tableAtom table identity) axioms key name schema cache receipts

/-- Successful source insertion is the existing signature extension, with a
fresh primitive identity and the full ordered receipt. -/
theorem constant_after_registered (context : TheoryContext) (table : DeclarationTable.Table context)
    (origin : TypeOp → Atom) (identity : Const → Atom) (axioms key : Atom)
    (name : String) (schema : Ty) (formed : TypeFormed context.signature schema)
    (fresh : .constant (Name.global name) ∉ context.names)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) :
    constantAfter (OperatorTable.tableAtom table.operators origin)
      (DeclarationTable.tableAtom table identity) axioms key name schema cache receipts =
    ProofLookup.sourceState
      (OperatorTable.tableAtom (DeclarationTable.addConstant table (constant name) schema formed fresh).operators origin)
      (DeclarationTable.tableAtom (DeclarationTable.addConstant table (constant name) schema formed fresh)
        (DeclarationTable.extendIdentity identity (constant name) (constantIdentity name))) axioms
      (ReceiptKeys.table (⟨key, constantRequest name schema, []⟩ :: receipts)) cache := by
  have oldRows : table.constants.map (DeclarationTable.entryAtom
      (DeclarationTable.extendIdentity identity (constant name) (constantIdentity name))) =
      table.constants.map (DeclarationTable.entryAtom identity) := by
    apply List.map_congr_left
    intro entry member
    have retained := DeclarationTable.old_constant_identity_preserved context (constant name)
      entry.1 entry.2 identity (constantIdentity name) fresh (table.registered entry member)
    simp only [DeclarationTable.entryAtom, retained]
  have extended : DeclarationTable.tableAtom
      (DeclarationTable.addConstant table (constant name) schema formed fresh)
      (DeclarationTable.extendIdentity identity (constant name) (constantIdentity name)) =
      .expression [.symbol "HOL:Cons", .expression [.symbol "HOL:Entry",
        .grounded (.string name), .expression [.symbol "HOL:Constant",
          typeAtom registeredOperatorAtom schema, constantIdentity name]],
        DeclarationTable.tableAtom table identity] := by
    simp only [DeclarationTable.tableAtom, DeclarationTable.entriesAtom,
      DeclarationTable.addConstant, List.map_cons, oldRows]
    simp [DeclarationTable.entryAtom, DeclarationTable.extendIdentity,
      constant, constantName, Lookup.table, Premises.keys, Const.same_eq_true_iff]
  rw [extended]
  rfl

/-- The declaration's cache is the same ordered evidence, valid in the
extended context. No source theorem name or arbitrary cache is authorized. -/
theorem constant_preserves_authorized_cache (policy : AxiomPolicy) (context : TheoryContext)
    (identity : Const → Atom) (name : String) (schema : Ty)
    (formed : TypeFormed context.signature schema)
    (fresh : .constant (Name.global name) ∉ context.names)
    (cache : CacheAuthorization.Cache) (valid : CacheAuthorization.Valid policy context cache) :
    CacheAuthorization.Valid policy (context.addConstant (constant name) schema formed fresh) cache ∧
      CacheAuthorization.entries
        (DeclarationTable.extendIdentity identity (constant name) (constantIdentity name)) cache =
        CacheAuthorization.entries identity cache :=
  CacheAuthorization.add_constant_transports_cache policy context (constant name) schema formed fresh
    identity (constantIdentity name) cache valid

/-- Every already registered spelling is refused, regardless of the old
definition's provenance or the proposed replacement schema. -/
theorem constant_duplicate_refused (context : TheoryContext)
    (table : DeclarationTable.Table context) (origin : TypeOp → Atom) (identity : Const → Atom)
    (axioms key : Atom) (name : String) (schema : Ty)
    (old : Const) (oldSchema : Ty) (registered : context.signature.constants old = some oldSchema)
    (named : constantName old = Name.global name)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) :
    constantResult context table origin identity axioms key name schema cache receipts = .symbol "None" := by
  have found := DeclarationTable.lookup_registered table identity old oldSchema registered
  rw [named, TypeSubstitution.nameAtom_global] at found
  simp [constantResult, found]

/-- A resolved but unformed schema never reaches insertion. In particular,
knowing an operator's name does not admit an incorrect argument count. -/
theorem constant_unformed_refused (context : TheoryContext)
    (table : DeclarationTable.Table context) (origin : TypeOp → Atom) (identity : Const → Atom)
    (axioms key : Atom) (name : String) (schema : Ty)
    (unformed : ¬ TypeFormed context.signature schema)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) :
    constantResult context table origin identity axioms key name schema cache receipts = .symbol "None" := by
  have rejected : typeFormedB context.signature schema = false := by
    cases found : typeFormedB context.signature schema with
    | false => rfl
    | true => exact False.elim (unformed ((typeFormedB_eq_true_iff _ _).mp found))
  simp [constantResult, rejected]

end Mettapedia.Languages.HOLLight.MeTTa.DeclarationExecution
