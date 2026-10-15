import Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionConstruction

/-!
# The authored type-definition command and its guards

The outer command executes its three name checks, name distinction, three
declaration lookups, proof-cache lookup, predicate closedness and witness
typing before entering the existing construction and publication helper.
The source path retains the actual cache, dependency list and proof origin.
Logical authorization of the retrieved premise is a separate history law.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters
open Effects (State boolean)
open Representation (registeredOperatorAtom termAtom)
open TypeDefinitionConstruction (Input)

private def equation : SpaceSemantics.Equation :=
  (definitionsSource.program.equations.filter (fun row => row.head == "hol-light:type-definition"))[0]'(by decide)

private def helperCall : Atom := .expression (.symbol "hol-light:extend-type" ::
  TypeDefinitionConstruction.sourceNames.map Atom.var)
private def witnessCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "Some", .var "representation"], helperCall), (.var "malformed", .symbol "None")]
private def witnessBody : Atom := .expression [.symbol "case",
  .expression [.symbol "hol-light:term-type", .var "witness"],
  .expression (witnessCases.map fun row => .expression [row.1, row.2])]
private def closedGuard : Atom := .expression [.symbol "if", .expression [.symbol "==",
  .expression [.symbol "hol-light:free-vars", .var "predicate"], .symbol "HOL:Nil"], witnessBody, .symbol "None"]
private def lookupPattern : Atom := .expression [.symbol "None", .symbol "None", .symbol "None",
  .expression [.symbol "Some", .expression [.symbol "HOL:Thm", .symbol "HOL:Nil",
    .expression [.symbol "HOL:App", .var "predicate", .var "witness"], .var "dependencies", .var "origin"]]]
private def lookupCases : SpaceSemantics.Cases :=
  [(lookupPattern, closedGuard), (.var "malformed", .symbol "None")]
private def lookupCalls : List Atom :=
  [.expression [.symbol "hol-light:lookup", .var "name", .var "operators"],
   .expression [.symbol "hol-light:lookup", .var "absname", .var "constants"],
   .expression [.symbol "hol-light:lookup", .var "repname", .var "constants"],
   .expression [.symbol "hol-light:known", .var "state", .var "premise"]]
private def lookupBody : Atom := .expression [.symbol "case", .expression lookupCalls,
  .expression (lookupCases.map fun row => .expression [row.1, row.2])]
private def differentGuard : Atom := .expression [.symbol "if",
  .expression [.symbol "==", .var "absname", .var "repname"], .symbol "None", lookupBody]
private def stringGuard (name : String) (body : Atom) : Atom := .expression [.symbol "if",
  .expression [.symbol "==", .expression [.symbol "get-type", .var name], .symbol "String"], body, .symbol "None"]
private def worldExpression : Atom := .expression [.symbol "HOL:State", .var "operators", .var "constants",
  .var "axioms", .var "cache", .var "receipts"]

def world (input : Input) : Atom := ProofLookup.sourceState input.operators input.declarations input.axioms
  (ReceiptKeys.table input.receipts) input.cache

def environment (input : Input) : Subst :=
  [("premise", input.premise), ("repname", .grounded (.string input.representationName)),
   ("absname", .grounded (.string input.abstractionName)), ("name", .grounded (.string input.typeName)),
   ("key", input.key), ("receipts", ReceiptKeys.table input.receipts), ("cache", Lookup.table input.cache),
   ("axioms", input.axioms), ("constants", input.declarations), ("operators", input.operators)]

def sourceNames : List String := ["state", "key", "name", "absname", "repname", "premise"]
def sourceArguments (input : Input) : List Atom :=
  [world input, input.key, .grounded (.string input.typeName), .grounded (.string input.abstractionName),
   .grounded (.string input.representationName), input.premise]

def premiseValue (input : Input) (constants : Const → Atom)
    (predicate : CheckedSourceTerm) (witness : CanonicalTerm) (origin : Atom) : Atom :=
  .expression [.symbol "HOL:Thm", .symbol "HOL:Nil",
    .expression [.symbol "HOL:App", termAtom registeredOperatorAtom constants [] predicate.canonical.term,
      termAtom registeredOperatorAtom constants [] witness.term], input.dependencies, origin]

private def withProof (input : Input) (constants : Const → Atom)
    (predicate : CheckedSourceTerm) (witness : CanonicalTerm) (origin : Atom) : Subst :=
  [("origin", origin), ("dependencies", input.dependencies),
   ("witness", termAtom registeredOperatorAtom constants [] witness.term),
   ("predicate", termAtom registeredOperatorAtom constants [] predicate.canonical.term)] ++
    ("state", world input) :: environment input

private theorem source_shape : equation.body = .expression [.symbol "let", .var "state", worldExpression,
    stringGuard "name" (stringGuard "absname" (stringGuard "repname" differentGuard))] := by decide

theorem source_clause (input : Input) :
    Eval.clauses program "hol-light:type-definition" (sourceArguments input) =
      [.evaluate (environment input) equation.body] := by
  rw [Eval.clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:type-definition") = [equation] := rfl
  rw [unique]
  have formals : equation.arguments =
      [.expression [.symbol "HOL:State", .var "operators", .var "constants", .var "axioms", .var "cache", .var "receipts"],
       .var "key", .var "name", .var "absname", .var "repname", .var "premise"] := by decide
  simp [formals, sourceArguments, world, environment, ProofLookup.sourceState, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem string_test_returns (bindings : Subst) (state : State) (name text : String)
    (captured : applySubst bindings (.var name) = .grounded (.string text)) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "==", .expression [.symbol "get-type", .var name], .symbol "String"])
      state (boolean true) := by
  apply BoundCalls.CorePath.native_binary_call_returns program bindings state state state state "=="
    _ (.symbol "String") (.symbol "String") (.symbol "String") (boolean true)
    (by decide) (by decide) (by decide) (by decide) _ _ _ (by decide)
  · apply BoundCalls.CorePath.native_variable_call_returns program bindings state state "get-type"
      [name] (.symbol "String") (by decide) (by decide) _ (by decide)
    simpa only [List.map_cons, List.map_nil, captured] using
      StdLib.string_type_is_string state text
  · exact BoundCalls.CorePath.symbol_returns program bindings state "String"
  · simp [StdLib.structural_equality, boolean]

private theorem string_guard_returns (bindings : Subst) (state : State) (name text : String)
    (body value : Atom) (captured : applySubst bindings (.var name) = .grounded (.string text))
    (returned : BoundCalls.PureReturns program bindings state body state value) :
    BoundCalls.PureReturns program bindings state (stringGuard name body) state value := by
  unfold stringGuard
  apply BoundCalls.if_returns program bindings state state state _ (boolean true) _ _ _
    (string_test_returns bindings state name text captured).extended
  simpa only [boolean, BEq.rfl, ↓reduceIte] using returned

/-- All command guards and the helper execute on the actual retained source.
The premise is retrieved by the real cache lookup, not supplied as a command
argument. Publication still retains its own address checks. -/
theorem authored_command_returns (input : Input) (context : TheoryContext)
    (table : DeclarationTable.Table context) (origins : TypeOp → Atom) (constants : Const → Atom)
    (operatorTable : input.operators = OperatorTable.tableAtom table.operators origins)
    (constantTable : input.declarations = DeclarationTable.tableAtom table constants)
    (predicate : CheckedSourceTerm) (witness : CanonicalTerm) (origin : Atom)
    (found : input.cache.lookup input.premise = some (premiseValue input constants predicate witness origin))
    (typeFresh : .typeOperator (sourceOperatorName (Name.global input.typeName)) ∉ context.names)
    (absFresh : .constant (Name.global input.abstractionName) ∉ context.names)
    (repFresh : .constant (Name.global input.representationName) ∉ context.names)
    (different : input.abstractionName ≠ input.representationName)
    (global : TypeParameterOrdering.globalParameters predicate.canonical.term)
    (typed : predicate.ty = .function witness.ty Ty.bool)
    (formed : AnnotationsFormed context.signature predicate.canonical.term)
    (closed : predicate.canonical.term.HasNoFreeVariables)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (receiptFresh : ReceiptKeys.presentB input.key input.receipts = false)
    (cacheFresh : input.cache.lookup input.key = none)
    (bindings : Subst) (state : State) (callNames : List String)
    (captured : callNames.map (fun name => applySubst bindings (.var name)) = sourceArguments input) :
    ∃ texts, texts.map Name.global = sortedParameters predicate.source ∧
      BoundCalls.PureReturns program bindings state
        (.expression (.symbol "hol-light:type-definition" :: callNames.map Atom.var)) state
        (TypeDefinitionConstruction.result input constants predicate witness.ty texts) := by
  let before := environment input
  let withState := ("state", world input) :: before
  let proofBindings := withProof input constants predicate witness origin
  let witnessBindings := ("representation", TypeSubstitution.typeAtom registeredOperatorAtom witness.ty) :: proofBindings
  obtain ⟨texts, ordered, helper⟩ := TypeDefinitionConstruction.authored_helper_call_returns input constants
    predicate witness.ty witnessBindings state (by
      simp [TypeDefinitionConstruction.sourceNames, TypeDefinitionConstruction.sourceArguments,
        witnessBindings, proofBindings, withProof, environment, world, applySubst, Subst.lookup])
    global typed context formed absFresh repFresh equalityIdentity receiptFresh cacheFresh
  refine ⟨texts, ordered, ?_⟩
  apply BoundCalls.authored_variable_call_returns program bindings before state state "hol-light:type-definition"
    callNames equation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
  · rw [captured]
    exact source_clause input
  · rw [source_shape]
    have worldReturned : BoundCalls.CorePath.PureReturns program before state worldExpression state (world input) := by
      unfold worldExpression world ProofLookup.sourceState
      simpa [before, environment, applySubst, Subst.lookup] using
        BoundCalls.CorePath.constructor_variables_return program before state "HOL:State"
          ["operators", "constants", "axioms", "cache", "receipts"] (by decide) (by decide)
    apply BoundCalls.let_returns program before withState state state state (.var "state") worldExpression _
      (world input) _ worldReturned.extended
    · simp [withState, before, environment, SpaceSemantics.matchBinding,
        SpaceSemantics.matchValue, matchAtom, Subst.lookup]
    · apply string_guard_returns withState state "name" input.typeName _ _
        (by simp [withState, before, environment, applySubst, Subst.lookup])
      apply string_guard_returns withState state "absname" input.abstractionName _ _
        (by simp [withState, before, environment, applySubst, Subst.lookup])
      apply string_guard_returns withState state "repname" input.representationName _ _
        (by simp [withState, before, environment, applySubst, Subst.lookup])
      unfold differentGuard
      apply BoundCalls.if_returns program withState state state state _ (boolean false) _ _ _
      · have tested : BoundCalls.CorePath.PureReturns program withState state
            (.expression [.symbol "==", .var "absname", .var "repname"]) state (boolean false) := by
          apply BoundCalls.CorePath.native_variable_call_returns program withState state state "=="
            ["absname", "repname"] (boolean false) (by decide) (by decide) _ (by decide)
          simp [withState, before, environment, applySubst, Subst.lookup,
            StdLib.structural_equality, different, boolean, beq_eq_decide]
        exact tested.extended
      · simp only [boolean]
        unfold lookupBody
        apply BoundCalls.case_returns program withState proofBindings state state state _
          (.expression [.symbol "None", .symbol "None", .symbol "None",
            .expression [.symbol "Some", premiseValue input constants predicate witness origin]])
          closedGuard _ _ lookupCases (Eval.read_cases_encoded lookupCases)
        · have looked : BoundCalls.CorePath.PureReturns program withState state (.expression lookupCalls) state
              (.expression [.symbol "None", .symbol "None", .symbol "None",
                .expression [.symbol "Some", premiseValue input constants predicate witness origin]]) := by
            apply BoundCalls.CorePath.expression_return program withState state _ _
              (by intro head args same; cases same) (by rfl)
            unfold lookupCalls
            refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))
            · let operator : TypeOp := .mk (sourceOperatorName (Name.global input.typeName)) .undefined
              have absent := OperatorTable.fresh_name_absent table.operators origins operator typeFresh
              have spelling : registeredOperatorAtom operator = .grounded (.string input.typeName) := by
                simp [operator, registeredOperatorAtom, operatorName, sourceOperatorName_roundtrip,
                  TypeSubstitution.nameAtom, Name.global]
              rw [spelling] at absent
              have lookup := Lookup.authored_lookup_certificate withState state (.grounded (.string input.typeName))
                (OperatorTable.entriesAtom table.operators origins) "name" "operators"
                (by simp [withState, before, environment, applySubst, Subst.lookup])
                (by simp [withState, before, environment, operatorTable, OperatorTable.tableAtom, applySubst, Subst.lookup])
              simpa only [absent, Lookup.answer] using lookup
            · have absent := DeclarationTable.fresh_name_absent table constants (Name.global input.abstractionName) absFresh
              have lookup := Lookup.authored_lookup_certificate withState state (.grounded (.string input.abstractionName))
                (DeclarationTable.entriesAtom table constants) "absname" "constants"
                (by simp [withState, before, environment, applySubst, Subst.lookup])
                (by simp [withState, before, environment, constantTable, DeclarationTable.tableAtom, applySubst, Subst.lookup])
              have absentSource : (DeclarationTable.entriesAtom table constants).lookup
                  (.grounded (.string input.abstractionName)) = none := absent
              simpa only [absentSource, Lookup.answer] using lookup
            · have absent := DeclarationTable.fresh_name_absent table constants (Name.global input.representationName) repFresh
              have lookup := Lookup.authored_lookup_certificate withState state (.grounded (.string input.representationName))
                (DeclarationTable.entriesAtom table constants) "repname" "constants"
                (by simp [withState, before, environment, applySubst, Subst.lookup])
                (by simp [withState, before, environment, constantTable, DeclarationTable.tableAtom, applySubst, Subst.lookup])
              have absentSource : (DeclarationTable.entriesAtom table constants).lookup
                  (.grounded (.string input.representationName)) = none := absent
              simpa only [absentSource, Lookup.answer] using lookup
            · simpa only [found, Lookup.answer] using
                ProofLookup.authored_known_certificate withState state input.operators input.declarations input.axioms
                  (ReceiptKeys.table input.receipts) input.premise input.cache "state" "premise"
                  (by simp [withState, before, world, applySubst, Subst.lookup])
                  (by simp [withState, before, environment, applySubst, Subst.lookup])
          exact looked.extended
        · simp [lookupCases, lookupPattern, premiseValue, proofBindings, withProof, withState, before,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
            environment, Subst.lookup]
        · unfold closedGuard
          apply BoundCalls.if_returns program proofBindings state state state _ (boolean true) _ _ _
          · have nil := (FreeVariables.free_atoms_nil_iff registeredOperatorAtom predicate.canonical.term).mpr closed
            simpa only [nil, decide_true] using
              (TypeVariables.authored_closed_body_certificate registeredOperatorAtom constants [] predicate.canonical.term
                proofBindings state "predicate" (by simp [proofBindings, withProof, applySubst, Subst.lookup])).extended
          · simp only [boolean, BEq.rfl, ↓reduceIte]
            unfold witnessBody
            apply BoundCalls.case_returns program proofBindings witnessBindings state state state _
              (.expression [.symbol "Some", TypeSubstitution.typeAtom registeredOperatorAtom witness.ty]) helperCall _ _
              witnessCases (Eval.read_cases_encoded witnessCases)
            · exact (TermJudgment.authored_term_type_certificate constants proofBindings state [] witness.term witness.ty
                witness.checked "witness" (by simp [proofBindings, withProof, applySubst, Subst.lookup])).extended
            · simp [witnessCases, witnessBindings, proofBindings, withProof, environment,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                matchAtom, Subst.lookup]
            · exact helper

/-- The command refuses coincident abstraction and representation names
before consulting the cache or constructing a declaration. The original
store, output and source world are retained. -/
theorem authored_equal_names_refused (input : Input)
    (same : input.abstractionName = input.representationName)
    (bindings : Subst) (state : State) (callNames : List String)
    (captured : callNames.map (fun name => applySubst bindings (.var name)) = sourceArguments input) :
    BoundCalls.PureReturns program bindings state
      (.expression (.symbol "hol-light:type-definition" :: callNames.map Atom.var)) state (.symbol "None") := by
  let before := environment input
  let withState := ("state", world input) :: before
  apply BoundCalls.authored_variable_call_returns program bindings before state state "hol-light:type-definition"
    callNames equation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
  · rw [captured]
    exact source_clause input
  · rw [source_shape]
    have worldReturned : BoundCalls.CorePath.PureReturns program before state worldExpression state (world input) := by
      unfold worldExpression world ProofLookup.sourceState
      simpa [before, environment, applySubst, Subst.lookup] using
        BoundCalls.CorePath.constructor_variables_return program before state "HOL:State"
          ["operators", "constants", "axioms", "cache", "receipts"] (by decide) (by decide)
    apply BoundCalls.let_returns program before withState state state state (.var "state") worldExpression _
      (world input) _ worldReturned.extended
    · simp [withState, before, environment, SpaceSemantics.matchBinding,
        SpaceSemantics.matchValue, matchAtom, Subst.lookup]
    · apply string_guard_returns withState state "name" input.typeName _ _
        (by simp [withState, before, environment, applySubst, Subst.lookup])
      apply string_guard_returns withState state "absname" input.abstractionName _ _
        (by simp [withState, before, environment, applySubst, Subst.lookup])
      apply string_guard_returns withState state "repname" input.representationName _ _
        (by simp [withState, before, environment, applySubst, Subst.lookup])
      unfold differentGuard
      apply BoundCalls.if_returns program withState state state state _ (boolean true) _ _ _
      · have tested : BoundCalls.CorePath.PureReturns program withState state
            (.expression [.symbol "==", .var "absname", .var "repname"]) state (boolean true) := by
          apply BoundCalls.CorePath.native_variable_call_returns program withState state state "=="
            ["absname", "repname"] (boolean true) (by decide) (by decide) _ (by decide)
          simp [withState, before, environment, applySubst, Subst.lookup, StdLib.structural_equality, same, boolean]
        exact tested.extended
      · simpa only [boolean, BEq.rfl, ↓reduceIte] using BoundCalls.symbol_returns program withState state "None"

end Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionExecution
