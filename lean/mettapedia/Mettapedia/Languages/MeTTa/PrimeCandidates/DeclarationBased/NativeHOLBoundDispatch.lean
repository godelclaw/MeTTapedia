import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativePeTTaBoundCalls
import Mettapedia.Languages.HOLLight.MeTTa.AxiomCacheHistory
import Mettapedia.Languages.HOLLight.MeTTa.DeclarationEvents
import Mettapedia.Languages.HOLLight.MeTTa.DefinitionHistory
import Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionCacheHistory
import Mettapedia.Languages.HOLLight.MeTTa.InferenceHistory

/-!
# Actual captured HOL dispatch over the native typed configuration graph

The existing wire, native Data formation and constructor interpretation are
reused. Source reading, a dispatcher prefix and full refusal paths produce
native state paths. These are operational executions, separate from dependent
conversion and native proofs of successful HOL propositions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeHOLBoundDispatch

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.MeTTa
open Mettapedia.Languages.OpenTheory
open SignatureFormation
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open NativePeTTaConfigurations (encode)

/-- The complete general TRANS event runs over the existing native typed
configuration graph and earns its registered HOL cache derivation. The native
path is operational evidence; it is not a native proof of the conclusion. -/
theorem trans_event_earns_cache (policy : AxiomPolicy) (world : TheoryContext)
    (constants : Const → Atom) (identified : DeclarationTable.Identifies world constants)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (cache : CacheAuthorization.Cache) (valid : CacheAuthorization.Valid policy world cache)
    (left right : CacheAuthorization.Record) (first second : Atom)
    (firstSelected : cache.lookup first = some left) (secondSelected : cache.lookup second = some right)
    (initial middle final : CanonicalTerm)
    (leftView : CanonicalTerm.EqualityViewSemantics left.conclusion initial middle)
    (rightView : CanonicalTerm.EqualityViewSemantics right.conclusion middle final)
    (receipts : List ReceiptKeys.Entry) (operators declarations axioms key : Atom)
    (receiptFresh : ReceiptKeys.presentB key receipts = false)
    (cacheFresh : (CacheAuthorization.entries constants cache).lookup key = none)
    (bindings : Subst) (state : Effects.State) (stateKey keyName requestName : String)
    (worldCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      operators declarations axioms (ReceiptKeys.table receipts) (CacheAuthorization.entries constants cache))
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = .expression [.symbol "TRANS", first, second])
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    ∃ next : CacheAuthorization.Record, ∃ finalNames,
      Mettapedia.Languages.HOLLight.InferenceRequest.Semantics (.trans left.fact right.fact) next.fact ∧
      TheoryDerives policy world next.fact ∧
      CacheAuthorization.Valid policy world ((key, next) :: cache) ∧
      (NativePeTTaConfigurations.theory program).MultiStep
        (encode { state, control := .evaluate bindings (.expression
          [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName]) } names)
        (encode (Eval.finished state [.expression [.symbol "Some", ProofLookup.sourceState operators declarations axioms
          (ReceiptKeys.table (⟨key, .expression [.symbol "TRANS", first, second], [first, second]⟩ :: receipts))
          (CacheAuthorization.entries constants ((key, next) :: cache))]] [] []) finalNames) ∧
      NamedSpaces.Store.EmptyTail state [] ∧
      (∀ name, name ∉ finalNames → state.cells name = none) := by
  obtain ⟨next, _, _, _, _, semantics, derived, authorized, returned⟩ :=
    InferenceHistory.authored_trans_preserves_valid policy world constants identified equalityIdentity
      cache valid left right first second firstSelected secondSelected initial middle final leftView rightView
      receipts operators declarations axioms key receiptFresh cacheFresh bindings state stateKey keyName requestName
      worldCaptured keyCaptured requestCaptured
  obtain ⟨finalNames, path, retained, support⟩ := NativePeTTaConfigurations.path_lifts returned names vacant covers
  exact ⟨next, finalNames, semantics, derived, authorized, path, retained, support⟩

/-- The complete source TYPE_DEFINITION event, including command guards,
captured dispatch and both publications, runs in the existing typed state
graph. This is an execution path, separate from native proposition evidence. -/
theorem type_definition_event (input : TypeDefinitionConstruction.Input) (context : TheoryContext)
    (table : DeclarationTable.Table context) (origins : TypeOp → Atom) (constants : Const → Atom)
    (operatorTable : input.operators = OperatorTable.tableAtom table.operators origins)
    (constantTable : input.declarations = DeclarationTable.tableAtom table constants)
    (predicate : CheckedSourceTerm) (witness : CanonicalTerm) (origin : Atom)
    (found : input.cache.lookup input.premise =
      some (TypeDefinitionExecution.premiseValue input constants predicate witness origin))
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
    (bindings : Subst) (state : Effects.State) (stateKey keyName requestName : String)
    (worldCaptured : applySubst bindings (.var stateKey) = TypeDefinitionExecution.world input)
    (keyCaptured : applySubst bindings (.var keyName) = input.key)
    (requestCaptured : applySubst bindings (.var requestName) = TypeDefinitionEvents.command input)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    ∃ texts finalNames, texts.map Name.global = sortedParameters predicate.source ∧
      (NativePeTTaBoundCalls.theory program).MultiStep
        (encode { state, control := .evaluate bindings (.expression
          [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName]) } names)
        (encode (Eval.finished state [TypeDefinitionConstruction.result input constants predicate witness.ty texts] [] []) finalNames) ∧
      NamedSpaces.Store.EmptyTail state [] ∧
      (∀ name, name ∉ finalNames → state.cells name = none) := by
  obtain ⟨texts, ordered, returned⟩ := TypeDefinitionEvents.authored_step_returns input context table origins constants
    operatorTable constantTable predicate witness origin found typeFresh absFresh repFresh different global typed formed closed
    equalityIdentity receiptFresh cacheFresh bindings state stateKey keyName requestName
    worldCaptured keyCaptured requestCaptured
  obtain ⟨finalNames, path, retained, support⟩ := NativePeTTaBoundCalls.path_lifts returned names vacant covers
  exact ⟨texts, finalNames, ordered, path, retained, support⟩

/-- The complete retained helper call executes its twelve bindings and both
publications in the existing typed configuration model. The outer command's
guards and native proposition inhabitants are independent obligations. -/
theorem type_definition_helper (input : TypeDefinitionConstruction.Input) (before : Const → Atom)
    (predicate : CheckedSourceTerm) (represented : Ty) (bindings : Subst) (state : Effects.State)
    (captured : TypeDefinitionConstruction.sourceNames.map (fun name => applySubst bindings (.var name)) =
      TypeDefinitionConstruction.sourceArguments input before predicate represented)
    (global : TypeParameterOrdering.globalParameters predicate.canonical.term)
    (typed : predicate.ty = .function represented Ty.bool)
    (context : TheoryContext) (formed : AnnotationsFormed context.signature predicate.canonical.term)
    (absFresh : .constant (Name.global input.abstractionName) ∉ context.names)
    (repFresh : .constant (Name.global input.representationName) ∉ context.names)
    (equalityIdentity : before Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (receiptFresh : ReceiptKeys.presentB input.key input.receipts = false)
    (cacheFresh : input.cache.lookup input.key = none)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    ∃ texts finalNames, texts.map Name.global = sortedParameters predicate.source ∧
      (NativePeTTaBoundCalls.theory program).MultiStep
        (encode { state, control := .evaluate bindings (.expression
          (.symbol "hol-light:extend-type" :: TypeDefinitionConstruction.sourceNames.map Atom.var)) } names)
        (encode (Eval.finished state [TypeDefinitionConstruction.result input before predicate represented texts] [] []) finalNames) ∧
      NamedSpaces.Store.EmptyTail state [] ∧
      (∀ name, name ∉ finalNames → state.cells name = none) := by
  obtain ⟨texts, ordered, returned⟩ := TypeDefinitionConstruction.authored_helper_call_returns input before
    predicate represented bindings state captured global typed context formed absFresh repFresh
    equalityIdentity receiptFresh cacheFresh
  obtain ⟨finalNames, path, retained, support⟩ := NativePeTTaBoundCalls.path_lifts returned names vacant covers
  exact ⟨texts, finalNames, ordered, path, retained, support⟩

/-- The retained equation-building source computes its two laws and enters
both publishers through the native typed configuration graph. This starts
after sequential declarations and remains distinct from proposition evidence. -/
theorem type_definition_equations (operators declarations axioms key dependencies : Atom)
    (typeName abstractionName representationName : String) (premise : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : Effects.State) (constants : Const → Atom)
    (abstraction representation : Const) (represented carrier : Ty) (predicate : DBTerm)
    (predicateChecked : predicate.inferType [] = some (.function represented Ty.bool))
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (worldCaptured : applySubst bindings (.var "extended") =
      ProofLookup.sourceState operators declarations axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var "key") = key)
    (requestCaptured : applySubst bindings (.var "request") =
      TypeDefinitionFormation.command typeName abstractionName representationName premise)
    (dependenciesCaptured : applySubst bindings (.var "dependencies") = dependencies)
    (predicateCaptured : applySubst bindings (.var "predicate") = Representation.termAtom Representation.registeredOperatorAtom constants [] predicate)
    (absCaptured : applySubst bindings (.var "abs") =
      Representation.termAtom Representation.registeredOperatorAtom constants [] (TypeDefinitionEquations.abstractionTerm abstraction represented carrier))
    (repCaptured : applySubst bindings (.var "rep") =
      Representation.termAtom Representation.registeredOperatorAtom constants [] (TypeDefinitionEquations.representationTerm representation represented carrier))
    (aCaptured : applySubst bindings (.var "a") = Representation.termAtom Representation.registeredOperatorAtom constants [] (TypeDefinitionEquations.carrierVariable carrier))
    (rCaptured : applySubst bindings (.var "r") =
      Representation.termAtom Representation.registeredOperatorAtom constants [] (TypeDefinitionEquations.representationVariable represented))
    (fresh : ∀ name ∈ ["first", "retraction", "second", "withFirst"], Subst.lookup bindings name = none)
    (receiptFresh : ReceiptKeys.presentB key receipts = false) (cacheFresh : cache.lookup key = none)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    ∃ finalNames,
      (NativePeTTaBoundCalls.theory program).MultiStep
        (encode { state, control := .evaluate bindings TypeDefinitionEquations.sourceBody } names)
        (encode (Eval.finished state [TypeDefinitionPublication.finalResult operators declarations axioms key
          (Representation.termAtom Representation.registeredOperatorAtom constants []
            (TypeDefinitionEquations.firstLaw abstraction representation represented carrier))
          (Representation.termAtom Representation.registeredOperatorAtom constants []
            (TypeDefinitionEquations.secondLaw abstraction representation represented carrier predicate))
          dependencies typeName abstractionName representationName premise cache receipts] [] []) finalNames) ∧
      NamedSpaces.Store.EmptyTail state [] ∧
      (∀ name, name ∉ finalNames → state.cells name = none) :=
  NativePeTTaBoundCalls.path_lifts
    (TypeDefinitionEquations.authored_equations_publish operators declarations axioms key dependencies
      typeName abstractionName representationName premise cache receipts bindings state constants
      abstraction representation represented carrier predicate predicateChecked equalityIdentity
      worldCaptured keyCaptured requestCaptured dependenciesCaptured predicateCaptured absCaptured repCaptured
      aCaptured rCaptured fresh receiptFresh cacheFresh)
    names vacant covers

/-- Both actual type-definition publisher calls run over the typed native
configuration graph. A second-address conflict returns no extended theory
value. This is the source tail, not the preceding declaration helper. -/
theorem type_definition_publications (operators constants axioms key first second dependencies : Atom)
    (typeName abstractionName representationName : String) (premise : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) (state : Effects.State)
    (receiptFresh : ReceiptKeys.presentB key receipts = false) (cacheFresh : cache.lookup key = none)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    ∃ finalNames,
      (NativePeTTaBoundCalls.theory program).MultiStep
        (encode { state, control := (.evaluate
          (TypeDefinitionPublication.environment operators constants axioms key first second dependencies
            typeName abstractionName representationName premise cache receipts)
          TypeDefinitionPublication.sourceTail) } names)
        (encode (Eval.finished state [TypeDefinitionPublication.finalResult operators constants axioms
          key first second dependencies typeName abstractionName representationName premise cache receipts]
          [] []) finalNames) ∧
      NamedSpaces.Store.EmptyTail state [] ∧
      (∀ name, name ∉ finalNames → state.cells name = none) :=
  NativePeTTaBoundCalls.path_lifts
    (TypeDefinitionPublication.authored_tail_returns operators constants axioms key first second dependencies
      typeName abstractionName representationName premise cache receipts state receiptFresh cacheFresh)
    names vacant covers

/-- Actual parameter collection and sorting execute as typed native
configuration paths. Their returned order is the registered source gate's
order, including the predicate's retained source representation. -/
theorem type_definition_parameters (constants : Const → Atom) (predicate : CheckedSourceTerm)
    (global : TypeParameterOrdering.globalParameters predicate.canonical.term)
    (bindings : Subst) (state : Effects.State) (termKey : String)
    (captured : applySubst bindings (.var termKey) =
      Representation.termAtom Representation.registeredOperatorAtom constants [] predicate.canonical.term)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    ∃ texts finalNames, texts.map Name.global = sortedParameters predicate.source ∧
      (NativePeTTaBoundCalls.theory program).MultiStep
        (encode { state, control := .evaluate bindings (.expression [.symbol "hol-light:type-parameters", .expression [.symbol "hol-light:sorted-names",
            .expression [.symbol "hol-light:term-type-vars", .var termKey]]]) } names)
        (encode (Eval.finished state [Premises.keys (TypeParameterOrdering.Parameters.atoms texts)] [] []) finalNames) ∧
      NamedSpaces.Store.EmptyTail state [] ∧
      (∀ name, name ∉ finalNames → state.cells name = none) := by
  obtain ⟨texts, ordered, actual⟩ := TypeParameterOrdering.authored_admission_parameters
    constants predicate global bindings state termKey captured
  obtain ⟨finalNames, native, retained, support⟩ := NativePeTTaBoundCalls.path_lifts actual.extended names vacant covers
  exact ⟨texts, finalNames, ordered, native, retained, support⟩

/-- The complete source definition event executes on the native typed graph.
The computed closedness and parameter guards remain part of the path, as do
the dispatcher capture and publication receipt checks. -/
theorem constant_definition_step (world : TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (identity : Const → Atom)
    (equalityIdentity : identity Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (axioms key : Atom) (name : String) (body : CheckedSourceTerm)
    (sourceResolved : TermReading.SourceResolved world.signature body.source)
    (schemaResolved : TypeFormation.Resolved world.signature body.ty)
    (formed : AnnotationsFormed world.signature body.canonical.term)
    (schemaFormed : TypeFormed world.signature body.ty)
    (fresh : .constant (Name.global name) ∉ world.names)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : Effects.State) (stateName keyName requestName : String)
    (worldCaptured : applySubst bindings (.var stateName) =
      ProofLookup.sourceState (OperatorTable.tableAtom table.operators origins)
        (DeclarationTable.tableAtom table identity) axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = DefinitionExecution.definitionRequest name body)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    ∃ finalNames,
      (NativePeTTaBoundCalls.theory program).MultiStep
        (encode { state, control := .evaluate bindings (.expression [.symbol "hol-light:step",
          .var stateName, .var keyName, .var requestName]) } names)
        (encode (Eval.finished state [if ReceiptKeys.presentB key receipts then .symbol "None" else
          DefinitionExecution.classifiedResult world table origins identity axioms key name body cache receipts]
          [] []) finalNames) ∧
      NamedSpaces.Store.EmptyTail state [] ∧
      (∀ name, name ∉ finalNames → state.cells name = none) :=
  NativePeTTaBoundCalls.path_lifts
    (DefinitionEvents.authored_definition_step world table origins identity equalityIdentity axioms key name body
      sourceResolved schemaResolved formed schemaFormed fresh cache receipts bindings state
      stateName keyName requestName worldCaptured keyCaptured requestCaptured) names vacant covers

/-- Complete declaration events execute over the same typed native graph,
including the receipt guard, captured helper and registered source checks.
Successful results extend the theory value rather than changing the store. -/
theorem constant_declaration_step (world : TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (identity : Const → Atom)
    (axioms key : Atom) (name : String) (schema : Ty)
    (resolved : TypeFormation.Resolved world.signature schema)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : Effects.State) (stateName keyName requestName : String)
    (worldCaptured : applySubst bindings (.var stateName) =
      ProofLookup.sourceState (OperatorTable.tableAtom table.operators origins)
        (DeclarationTable.tableAtom table identity) axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = DeclarationExecution.constantRequest name schema)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    ∃ finalNames,
      (NativePeTTaBoundCalls.theory program).MultiStep
        (encode { state, control := .evaluate bindings (.expression [.symbol "hol-light:step",
          .var stateName, .var keyName, .var requestName]) } names)
        (encode (Eval.finished state [if ReceiptKeys.presentB key receipts then .symbol "None" else
          DeclarationExecution.constantResult world table origins identity axioms key name schema cache receipts]
          [] []) finalNames) ∧
      NamedSpaces.Store.EmptyTail state [] ∧
      (∀ name, name ∉ finalNames → state.cells name = none) :=
  NativePeTTaBoundCalls.path_lifts
    (DeclarationEvents.authored_constant_step world table origins identity axioms key name schema resolved
      cache receipts bindings state stateName keyName requestName worldCaptured keyCaptured requestCaptured)
    names vacant covers

/-- The actual reader of arbitrary admitted source terms executes over the
native typed configuration graph and retains its positional source context. -/
theorem source_reader (world : TheoryContext)
    (table : DeclarationTable.Table world)
    (origins : TypeOp → Atom)
    (constants : Const → Atom)
    (source : SourceTerm)
    (resolved : TermReading.SourceResolved world.signature source)
    (context : List SourceVar)
    (contextFormed : ∀ binder ∈ context,
      TypeFormed world.signature binder.ty)
    (annotations : AnnotationsFormed world.signature (source.toDB context))
    (type : Ty) (typed : source.inferType = some type)
    (bindings : Subst) (state : Effects.State) (operatorsKey constantsKey contextKey sourceKey : String)
    (operatorsCaptured : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table.operators origins)
    (constantsCaptured : applySubst bindings (.var constantsKey) = DeclarationTable.tableAtom table constants)
    (contextCaptured : applySubst bindings (.var contextKey) = ContextLookup.contextAtom context)
    (sourceCaptured : applySubst bindings (.var sourceKey) = TermReading.sourceAtom source)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    ∃ finalNames,
      (NativePeTTaBoundCalls.theory program).MultiStep
        (encode { state, control := .evaluate bindings (.expression [.symbol "hol-light:read-term", .var operatorsKey,
          .var constantsKey, .var contextKey, .var sourceKey]) } names)
        (encode (Eval.finished state [.expression [.symbol "Some",
          Representation.termAtom Representation.registeredOperatorAtom constants
            (context.map Var.ty) (source.toDB context)]] [] []) finalNames) ∧
      NamedSpaces.Store.EmptyTail state [] ∧
      (∀ name, name ∉ finalNames → state.cells name = none) :=
  NativePeTTaBoundCalls.path_lifts
    (TermReading.authored_read_bound_return world table origins constants source resolved context contextFormed annotations
      type typed bindings state operatorsKey constantsKey contextKey sourceKey
      operatorsCaptured constantsCaptured contextCaptured sourceCaptured) names vacant covers

/-- A formed source annotation cannot bypass a declaration schema. The
refusal runs on the same native graph as successful reading. -/
theorem wrong_constant_instance (world : TheoryContext)
    (table : DeclarationTable.Table world)
    (origins : TypeOp → Atom)
    (constants : Const → Atom)
    (context : List SourceVar)
    (constant : Const)
    (schema occurrence : Ty)
    (registered : world.signature.constants constant = some schema)
    (schemaFormed : TypeFormed world.signature schema)
    (occurrenceFormed : TypeFormed world.signature occurrence)
    (resolved : TypeFormation.Resolved world.signature occurrence)
    (wrong : ¬ ConstantInstance world.signature constant occurrence)
    (bindings : Subst) (state : Effects.State) (operatorsKey constantsKey contextKey sourceKey : String)
    (operatorsCaptured : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table.operators origins)
    (constantsCaptured : applySubst bindings (.var constantsKey) = DeclarationTable.tableAtom table constants)
    (contextCaptured : applySubst bindings (.var contextKey) = ContextLookup.contextAtom context)
    (sourceCaptured : applySubst bindings (.var sourceKey) = TermReading.sourceAtom (.const constant occurrence))
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    ∃ finalNames,
      (NativePeTTaBoundCalls.theory program).MultiStep
        (encode { state, control := .evaluate bindings (.expression [.symbol "hol-light:read-term", .var operatorsKey,
          .var constantsKey, .var contextKey, .var sourceKey]) } names)
        (encode (Eval.finished state [.symbol "None"] [] []) finalNames) ∧
      NamedSpaces.Store.EmptyTail state [] ∧
      (∀ name, name ∉ finalNames → state.cells name = none) :=
  NativePeTTaBoundCalls.path_lifts
    (TermReading.authored_wrong_constant_instance_bound_refused world table origins constants context constant schema occurrence
      registered schemaFormed occurrenceFormed resolved wrong bindings state operatorsKey constantsKey contextKey sourceKey
      operatorsCaptured constantsCaptured contextCaptured sourceCaptured) names vacant covers

/-- Every classified AXIOM event executes over the native typed
configuration graph. The path retains the source store and distinguishes
successful publication from both formula and carrier refusal. -/
theorem classified_axiom_step (world : TheoryContext) (table : DeclarationTable.Table world)
    (origins : TypeOp → Atom) (constants : Const → Atom) (identified : DeclarationTable.Identifies world constants)
    (source expected : CheckedSourceTerm)
    (sourceResolved : TermReading.SourceResolved world.signature source.source)
    (expectedResolved : TermReading.SourceResolved world.signature expected.source)
    (sourceFormed : AnnotationsFormed world.signature source.canonical.term)
    (expectedFormed : AnnotationsFormed world.signature expected.canonical.term)
    (sourceTypeFormed : TypeFormed world.signature source.ty) (booleanFormed : TypeFormed world.signature Ty.bool)
    (key label : Atom) (commitments cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (found : commitments.lookup label = some (TermReading.sourceAtom expected.source))
    (bindings : Subst) (state : Effects.State) (stateName keyName requestName : String)
    (worldCaptured : applySubst bindings (.var stateName) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
      (Lookup.table commitments) (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = AxiomDispatch.request label (TermReading.sourceAtom source.source))
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    ∃ finalNames,
      (NativePeTTaBoundCalls.theory program).MultiStep
        (encode { state, control := .evaluate bindings (.expression [.symbol "hol-light:step", .var stateName, .var keyName, .var requestName]) } names)
        (encode (Eval.finished state [AxiomDispatch.eventResult (OperatorTable.tableAtom table.operators origins)
            (DeclarationTable.tableAtom table constants) key label constants source expected commitments cache receipts] [] []) finalNames) ∧
      NamedSpaces.Store.EmptyTail state [] ∧
      (∀ name, name ∉ finalNames → state.cells name = none) :=
  NativePeTTaBoundCalls.path_lifts
    (AxiomDispatch.authored_axiom_step_classified_return world table origins constants identified source expected
      sourceResolved expectedResolved sourceFormed expectedFormed sourceTypeFormed booleanFormed key label commitments
      cache receipts found bindings state stateName keyName requestName worldCaptured keyCaptured requestCaptured)
    names vacant covers

/-- The actual dispatcher prefix constructs a typed native configuration path
with its publication continuation and source world still present. -/
theorem authored_dispatch_prefix (world key label source : Atom)
    (bindings : Subst) (state : Effects.State) (stateName keyName requestName : String)
    (worldCaptured : applySubst bindings (.var stateName) = world)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = AxiomDispatch.request label source)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    ∃ finalNames,
      (NativePeTTaBoundCalls.theory program).MultiStep
        (encode { state, control := .evaluate bindings (.expression [.symbol "hol-light:dispatch", .var stateName, .var keyName, .var requestName]) } names)
        (encode (AxiomDispatch.helperEntry world key label source state) finalNames) ∧
      NamedSpaces.Store.EmptyTail state [] ∧
      (∀ name, name ∉ finalNames → state.cells name = none) :=
  NativePeTTaBoundCalls.path_lifts
    (AxiomDispatch.authored_dispatch_enters_helper world key label source bindings state stateName keyName requestName
      worldCaptured keyCaptured requestCaptured) names vacant covers

/-- The complete undeclared-AXIOM refusal also executes in the same native
typed configuration representation, without a guest-proof inhabitant claim. -/
theorem missing_axiom_step (operators constants key label source : Atom)
    (commitments cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (missing : commitments.lookup label = none)
    (bindings : Subst) (state : Effects.State) (stateName keyName requestName : String)
    (worldCaptured : applySubst bindings (.var stateName) = ProofLookup.sourceState
      operators constants (Lookup.table commitments) (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = AxiomDispatch.request label source)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    ∃ finalNames,
      (NativePeTTaBoundCalls.theory program).MultiStep
        (encode { state, control := .evaluate bindings (.expression [.symbol "hol-light:step", .var stateName, .var keyName, .var requestName]) } names)
        (encode (Eval.finished state [.symbol "None"] [] []) finalNames) ∧
      NamedSpaces.Store.EmptyTail state [] ∧
      (∀ name, name ∉ finalNames → state.cells name = none) :=
  NativePeTTaBoundCalls.path_lifts
    (AxiomDispatch.authored_missing_axiom_step_refused operators constants key label source commitments cache receipts missing
      bindings state stateName keyName requestName worldCaptured keyCaptured requestCaptured) names vacant covers

/-- The complete EQ_MP event earns the registered cache result and
its native typed operational path. Native proposition inhabitants remain
a separate interpretation obligation. -/
theorem eq_mp_event_earns_cache (policy : AxiomPolicy) (world : TheoryContext)
    (constants : Const → Atom) (identified : DeclarationTable.Identifies world constants)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (functionArity : world.signature.typeOperators TypeOp.function = some 2)
    (cache : CacheAuthorization.Cache) (valid : CacheAuthorization.Valid policy world cache) (equality premise : CacheAuthorization.Record) (first second : Atom)
    (firstSelected : cache.lookup first = some equality) (secondSelected : cache.lookup second = some premise)
    (target : CanonicalTerm)
    (view : CanonicalTerm.EqualityViewSemantics equality.conclusion premise.conclusion target)
    (receipts : List ReceiptKeys.Entry) (operators declarations axioms key : Atom)
    (receiptFresh : ReceiptKeys.presentB key receipts = false)
    (cacheFresh : (CacheAuthorization.entries constants cache).lookup key = none)
    (bindings : Subst) (state : Effects.State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      operators declarations axioms (ReceiptKeys.table receipts) (CacheAuthorization.entries constants cache))
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = .expression [.symbol "EQ_MP", first, second])
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    ∃ next : CacheAuthorization.Record, ∃ finalNames,
      InferenceRequest.Semantics (.eqMp equality.fact premise.fact) next.fact ∧
      TheoryDerives policy world next.fact ∧
      CacheAuthorization.Valid policy world ((key, next) :: cache) ∧
      (NativePeTTaConfigurations.theory program).MultiStep
        (encode { state, control := .evaluate bindings (.expression
          [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName]) } names)
        (encode (Eval.finished state [.expression [.symbol "Some", ProofLookup.sourceState operators declarations axioms
          (ReceiptKeys.table (⟨key, .expression [.symbol "EQ_MP", first, second], [first, second]⟩ :: receipts))
          (CacheAuthorization.entries constants ((key, next) :: cache))]] [] []) finalNames) ∧
      NamedSpaces.Store.EmptyTail state [] ∧
      (∀ name, name ∉ finalNames → state.cells name = none) := by
  obtain ⟨next, _, _, _, _, semantics, derived, authorized, returned⟩ :=
    InferenceHistory.authored_eq_mp_preserves_valid policy world constants identified equalityIdentity functionArity cache valid equality premise first second firstSelected secondSelected target view receipts operators declarations axioms key receiptFresh cacheFresh bindings state stateKey keyName requestName stateCaptured keyCaptured requestCaptured
  obtain ⟨finalNames, path, retained, support⟩ := NativePeTTaConfigurations.path_lifts returned names vacant covers
  exact ⟨next, finalNames, semantics, derived, authorized, path, retained, support⟩

/-- The complete MK_COMB event earns the registered cache result and
its native typed operational path. Native proposition inhabitants remain
a separate interpretation obligation. -/
theorem mk_comb_event_earns_cache (policy : AxiomPolicy) (world : TheoryContext)
    (constants : Const → Atom) (identified : DeclarationTable.Identifies world constants)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (functionArity : world.signature.typeOperators TypeOp.function = some 2)
    (equalityParameter : Name)
    (equalityRegistered : world.signature.constants Const.equality = some (Ty.equality (.var equalityParameter)))
    (cache : CacheAuthorization.Cache) (valid : CacheAuthorization.Valid policy world cache) (functions arguments : CacheAuthorization.Record) (first second : Atom)
    (firstSelected : cache.lookup first = some functions) (secondSelected : cache.lookup second = some arguments)
    (functionLeft functionRight argumentLeft argumentRight : CanonicalTerm) (domain codomain : Ty)
    (functionView : CanonicalTerm.EqualityViewSemantics functions.conclusion functionLeft functionRight)
    (argumentView : CanonicalTerm.EqualityViewSemantics arguments.conclusion argumentLeft argumentRight)
    (functionType : functionLeft.ty = .function domain codomain) (argumentType : argumentLeft.ty = domain)
    (receipts : List ReceiptKeys.Entry) (operators declarations axioms key : Atom)
    (receiptFresh : ReceiptKeys.presentB key receipts = false)
    (cacheFresh : (CacheAuthorization.entries constants cache).lookup key = none)
    (bindings : Subst) (state : Effects.State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      operators declarations axioms (ReceiptKeys.table receipts) (CacheAuthorization.entries constants cache))
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = .expression [.symbol "MK_COMB", first, second])
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    ∃ next : CacheAuthorization.Record, ∃ finalNames,
      InferenceRequest.Semantics (.mkComb functions.fact arguments.fact) next.fact ∧
      TheoryDerives policy world next.fact ∧
      CacheAuthorization.Valid policy world ((key, next) :: cache) ∧
      (NativePeTTaConfigurations.theory program).MultiStep
        (encode { state, control := .evaluate bindings (.expression
          [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName]) } names)
        (encode (Eval.finished state [.expression [.symbol "Some", ProofLookup.sourceState operators declarations axioms
          (ReceiptKeys.table (⟨key, .expression [.symbol "MK_COMB", first, second], [first, second]⟩ :: receipts))
          (CacheAuthorization.entries constants ((key, next) :: cache))]] [] []) finalNames) ∧
      NamedSpaces.Store.EmptyTail state [] ∧
      (∀ name, name ∉ finalNames → state.cells name = none) := by
  obtain ⟨next, _, _, _, _, semantics, derived, authorized, returned⟩ :=
    InferenceHistory.authored_mk_comb_preserves_valid policy world constants identified equalityIdentity functionArity equalityParameter equalityRegistered cache valid functions arguments first second firstSelected secondSelected functionLeft functionRight argumentLeft argumentRight domain codomain functionView argumentView functionType argumentType receipts operators declarations axioms key receiptFresh cacheFresh bindings state stateKey keyName requestName stateCaptured keyCaptured requestCaptured
  obtain ⟨finalNames, path, retained, support⟩ := NativePeTTaConfigurations.path_lifts returned names vacant covers
  exact ⟨next, finalNames, semantics, derived, authorized, path, retained, support⟩

/-- The actual deduction event earns both hypothesis discharge and the
registered native operational path, retaining the two source occurrences. -/
theorem deduct_event_earns_cache (policy : AxiomPolicy) (world : TheoryContext)
    (constants : Const → Atom) (identified : DeclarationTable.Identifies world constants)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (functionArity : world.signature.typeOperators TypeOp.function = some 2)
    (equalityParameter : Name)
    (equalityRegistered : world.signature.constants Const.equality = some (Ty.equality (.var equalityParameter)))
    (cache : CacheAuthorization.Cache) (valid : CacheAuthorization.Valid policy world cache) (left right : CacheAuthorization.Record) (first second : Atom)
    (firstSelected : cache.lookup first = some left) (secondSelected : cache.lookup second = some right)
    (receipts : List ReceiptKeys.Entry) (operators declarations axioms key : Atom)
    (receiptFresh : ReceiptKeys.presentB key receipts = false)
    (cacheFresh : (CacheAuthorization.entries constants cache).lookup key = none)
    (bindings : Subst) (state : Effects.State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      operators declarations axioms (ReceiptKeys.table receipts) (CacheAuthorization.entries constants cache))
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = .expression [.symbol "DEDUCT_ANTISYM_RULE", first, second])
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    ∃ next : CacheAuthorization.Record, ∃ finalNames,
      InferenceRequest.Semantics (.deductAntisym left.fact right.fact) next.fact ∧
      TheoryDerives policy world next.fact ∧
      CacheAuthorization.Valid policy world ((key, next) :: cache) ∧
      (NativePeTTaConfigurations.theory program).MultiStep
        (encode { state, control := .evaluate bindings (.expression
          [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName]) } names)
        (encode (Eval.finished state [.expression [.symbol "Some", ProofLookup.sourceState operators declarations axioms
          (ReceiptKeys.table (⟨key, .expression [.symbol "DEDUCT_ANTISYM_RULE", first, second], [first, second]⟩ :: receipts))
          (CacheAuthorization.entries constants ((key, next) :: cache))]] [] []) finalNames) ∧
      NamedSpaces.Store.EmptyTail state [] ∧
      (∀ name, name ∉ finalNames → state.cells name = none) := by
  obtain ⟨next, _, _, _, _, semantics, derived, authorized, returned⟩ :=
    InferenceHistory.authored_deduct_preserves_valid policy world constants identified equalityIdentity functionArity equalityParameter equalityRegistered cache valid left right first second firstSelected secondSelected receipts operators declarations axioms key receiptFresh cacheFresh bindings state stateKey keyName requestName stateCaptured keyCaptured requestCaptured
  obtain ⟨finalNames, path, retained, support⟩ := NativePeTTaConfigurations.path_lifts returned names vacant covers
  exact ⟨next, finalNames, semantics, derived, authorized, path, retained, support⟩

/-- The exact source BETA event earns its cache entry and a path in the
existing typed configuration graph. The native path does not identify HOL
equality with native dependent identity. -/
theorem beta_event_earns_cache (policy : AxiomPolicy) (world : TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (functionArity : world.signature.typeOperators TypeOp.function = some 2)
    (equalityParameter : Name)
    (equalityRegistered : world.signature.constants Const.equality = some (Ty.equality (.var equalityParameter)))
    (booleanFormed : TypeFormed world.signature Ty.bool) (needle : SourceVar) (body : CheckedSourceTerm)
    (resolved : TermReading.SourceResolved world.signature (Beta.redex needle body.source))
    (annotations : AnnotationsFormed world.signature ((Beta.redex needle body.source).toDB []))
    (cache : CacheAuthorization.Cache) (valid : CacheAuthorization.Valid policy world cache)
    (receipts : List ReceiptKeys.Entry) (key axioms : Atom)
    (receiptFresh : ReceiptKeys.presentB key receipts = false)
    (cacheFresh : (CacheAuthorization.entries constants cache).lookup key = none)
    (bindings : Subst) (state : Effects.State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms
      (ReceiptKeys.table receipts) (CacheAuthorization.entries constants cache))
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) =
      .expression [.symbol "BETA", TermReading.sourceAtom (Beta.redex needle body.source)])
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    ∃ (source : CheckedSourceTerm) (next : CacheAuthorization.Record) (finalNames : List String),
      source.source = Beta.redex needle body.source ∧
      InferenceRequest.Semantics (.beta source) next.fact ∧ TheoryDerives policy world next.fact ∧
      CacheAuthorization.Valid policy world ((key, next) :: cache) ∧
      (NativePeTTaConfigurations.theory program).MultiStep
        (encode { state, control := .evaluate bindings (.expression
          [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName]) } names)
        (encode (Eval.finished state [.expression [.symbol "Some", ProofLookup.sourceState
          (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms
          (ReceiptKeys.table (⟨key, .expression [.symbol "BETA", TermReading.sourceAtom (Beta.redex needle body.source)],
            []⟩ :: receipts)) (CacheAuthorization.entries constants ((key, next) :: cache))]] [] []) finalNames) ∧
      NamedSpaces.Store.EmptyTail state [] ∧ (∀ name, name ∉ finalNames → state.cells name = none) := by
  obtain ⟨source, next, shape, _, _, _, semantics, derived, authorized, returned⟩ :=
    InferenceHistory.authored_beta_preserves_valid policy world table origins constants equalityIdentity functionArity
      equalityParameter equalityRegistered booleanFormed needle body resolved annotations cache valid receipts key axioms
      receiptFresh cacheFresh bindings state stateKey keyName requestName stateCaptured keyCaptured requestCaptured
  obtain ⟨finalNames, path, retained, support⟩ := NativePeTTaConfigurations.path_lifts returned names vacant covers
  exact ⟨source, next, finalNames, shape, semantics, derived, authorized, path, retained, support⟩

/-- An authorized ABS premise earns both closing and its typed operational
path. The original ordered metadata and exact input receipt are retained. -/
theorem abs_event_earns_cache (policy : AxiomPolicy) (world : TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (functionArity : world.signature.typeOperators TypeOp.function = some 2)
    (equalityParameter : Name)
    (equalityRegistered : world.signature.constants Const.equality = some (Ty.equality (.var equalityParameter)))
    (needle : SourceVar) (needleFormed : TypeFormed world.signature needle.ty)
    (resolved : TermReading.SourceResolved world.signature (.var needle.name needle.ty))
    (cache : CacheAuthorization.Cache) (valid : CacheAuthorization.Valid policy world cache)
    (premise : CacheAuthorization.Record) (input : Atom) (selected : cache.lookup input = some premise)
    (left right : CanonicalTerm) (view : CanonicalTerm.EqualityViewSemantics premise.conclusion left right)
    (fresh : ¬ FreeInHypotheses needle premise.fact.sequent.hyp)
    (receipts : List ReceiptKeys.Entry) (key axioms : Atom)
    (receiptFresh : ReceiptKeys.presentB key receipts = false)
    (cacheFresh : (CacheAuthorization.entries constants cache).lookup key = none)
    (bindings : Subst) (state : Effects.State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms
      (ReceiptKeys.table receipts) (CacheAuthorization.entries constants cache))
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) =
      .expression [.symbol "ABS", TermReading.sourceAtom (.var needle.name needle.ty), input])
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    ∃ (next : CacheAuthorization.Record) (finalNames : List String),
      InferenceRequest.Semantics (.abs needle premise.fact) next.fact ∧ TheoryDerives policy world next.fact ∧
      CacheAuthorization.Valid policy world ((key, next) :: cache) ∧
      (NativePeTTaConfigurations.theory program).MultiStep
        (encode { state, control := .evaluate bindings (.expression
          [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName]) } names)
        (encode (Eval.finished state [.expression [.symbol "Some", ProofLookup.sourceState
          (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms
          (ReceiptKeys.table (⟨key, .expression [.symbol "ABS", TermReading.sourceAtom (.var needle.name needle.ty), input],
            [input]⟩ :: receipts)) (CacheAuthorization.entries constants ((key, next) :: cache))]] [] []) finalNames) ∧
      NamedSpaces.Store.EmptyTail state [] ∧ (∀ name, name ∉ finalNames → state.cells name = none) := by
  obtain ⟨next, _, _, _, semantics, derived, authorized, returned⟩ :=
    InferenceHistory.authored_abs_preserves_valid policy world table origins constants equalityIdentity functionArity
      equalityParameter equalityRegistered needle needleFormed resolved cache valid premise input selected left right view
      fresh receipts key axioms receiptFresh cacheFresh bindings state stateKey keyName requestName stateCaptured
      keyCaptured requestCaptured
  obtain ⟨finalNames, path, retained, support⟩ := NativePeTTaConfigurations.path_lifts returned names vacant covers
  exact ⟨next, finalNames, semantics, derived, authorized, path, retained, support⟩

open CacheAuthorization

/-- The actual substitution event earns its registered cache theorem and
executes over the existing native typed configuration graph. The path is
operational evidence, separate from native proposition inhabitants. -/
theorem inst_type_event_earns_cache (policy : AxiomPolicy) (world : TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants) (maplets : List (Ty × Ty))
    (resolved : ∀ entry ∈ maplets, TypeFormation.Resolved world.signature entry.1 ∧
      TypeFormation.Resolved world.signature entry.2)
    (formed : ∀ entry ∈ maplets, TypeFormed world.signature entry.1 ∧ TypeFormed world.signature entry.2)
    (cache : Cache) (valid : Valid policy world cache) (premise : Record) (input : Atom)
    (selected : cache.lookup input = some premise) (receipts : List ReceiptKeys.Entry) (key axioms : Atom)
    (receiptFresh : ReceiptKeys.presentB key receipts = false)
    (cacheFresh : (entries constants cache).lookup key = none)
    (bindings : Subst) (state : Effects.State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms
      (ReceiptKeys.table receipts) (entries constants cache))
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = .expression [.symbol "INST_TYPE",
      TypeSubstitution.maplets Representation.registeredOperatorAtom maplets, input])
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    ∃ next : Record, ∃ finalNames,
      InferenceRequest.Semantics (.instType maplets premise.fact) next.fact ∧
      TheoryDerives policy world next.fact ∧ Valid policy world ((key, next) :: cache) ∧
      (NativePeTTaConfigurations.theory program).MultiStep
        (encode { state, control := .evaluate bindings (.expression
          [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName]) } names)
        (encode (Eval.finished state [.expression [.symbol "Some", ProofLookup.sourceState
          (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms
          (ReceiptKeys.table (⟨key, .expression [.symbol "INST_TYPE", TypeSubstitution.maplets Representation.registeredOperatorAtom maplets, input], [input]⟩ :: receipts))
          (entries constants ((key, next) :: cache))]] [] []) finalNames) ∧
      NamedSpaces.Store.EmptyTail state [] ∧ (∀ name, name ∉ finalNames → state.cells name = none) := by
  obtain ⟨next, _, _, _, _, semantics, derived, authorized, returned⟩ :=
    InferenceHistory.authored_inst_type_preserves_valid policy world table origins constants identified maplets resolved formed cache valid premise input selected receipts key axioms receiptFresh cacheFresh bindings state stateKey keyName requestName stateCaptured keyCaptured requestCaptured
  obtain ⟨finalNames, path, retained, support⟩ := NativePeTTaConfigurations.path_lifts returned names vacant covers
  exact ⟨next, finalNames, semantics, derived, authorized, path, retained, support⟩

/-- The actual substitution event earns its registered cache theorem and
executes over the existing native typed configuration graph. The path is
operational evidence, separate from native proposition inhabitants. -/
theorem inst_event_earns_cache (policy : AxiomPolicy) (world : TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants) (maplets : List TermMapletReading.Entry)
    (admitted : TermMapletReading.admittedB maplets = true)
    (formed : ∀ entry ∈ maplets, TermMapletReading.EntryFormed world.signature entry)
    (cache : Cache) (valid : Valid policy world cache) (premise : Record) (input : Atom)
    (selected : cache.lookup input = some premise) (receipts : List ReceiptKeys.Entry) (key axioms : Atom)
    (receiptFresh : ReceiptKeys.presentB key receipts = false)
    (cacheFresh : (entries constants cache).lookup key = none)
    (bindings : Subst) (state : Effects.State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms
      (ReceiptKeys.table receipts) (entries constants cache))
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) =
      .expression [.symbol "INST", TermMapletReading.sourceAtom maplets, input])
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    ∃ next : Record, ∃ finalNames,
      InferenceRequest.Semantics (.inst (TermMapletReading.sourceEntries maplets) premise.fact) next.fact ∧
      TheoryDerives policy world next.fact ∧ Valid policy world ((key, next) :: cache) ∧
      (NativePeTTaConfigurations.theory program).MultiStep
        (encode { state, control := .evaluate bindings (.expression
          [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName]) } names)
        (encode (Eval.finished state [.expression [.symbol "Some", ProofLookup.sourceState
          (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms
          (ReceiptKeys.table (⟨key, .expression [.symbol "INST", TermMapletReading.sourceAtom maplets, input], [input]⟩ :: receipts))
          (entries constants ((key, next) :: cache))]] [] []) finalNames) ∧
      NamedSpaces.Store.EmptyTail state [] ∧ (∀ name, name ∉ finalNames → state.cells name = none) := by
  obtain ⟨next, _, _, _, _, semantics, derived, authorized, returned⟩ :=
    InferenceHistory.authored_inst_preserves_valid policy world table origins constants identified maplets admitted formed cache valid premise input selected receipts key axioms receiptFresh cacheFresh bindings state stateKey keyName requestName stateCaptured keyCaptured requestCaptured
  obtain ⟨finalNames, path, retained, support⟩ := NativePeTTaConfigurations.path_lifts returned names vacant covers
  exact ⟨next, finalNames, semantics, derived, authorized, path, retained, support⟩

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeHOLBoundDispatch
