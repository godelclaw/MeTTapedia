import Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionEvents
import Mettapedia.Languages.HOLLight.TheoryBooleanity
import Mettapedia.Languages.OpenTheory.FunctionRecognition
import Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionTables

/-!
# Authorized records produced by the actual type-definition event

The existence premise comes from a valid cache lookup. Its Booleanity and
annotation formation are earned from that derivation. The actual command
determines the parameter order used by the registered definition gate.
Both returned records have derived facts, retained dependency occurrences
and separate origins in the extended theory. The returned source world has
the exact registered declaration rows, identified constants, valid cache and
both ordered publication receipts. Arbitrary receive histories remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionCacheHistory

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters
open Effects (State)
open TypeDefinitionConstruction (Input)

def input (context : TheoryContext) (table : DeclarationTable.Table context)
    (origins : TypeOp → Atom) (constants : Const → Atom) (axioms key premise : Atom)
    (typeName abstractionName representationName : String) (record : CacheAuthorization.Record)
    (cache : CacheAuthorization.Cache) (receipts : List ReceiptKeys.Entry) : Input :=
  { operators := OperatorTable.tableAtom table.operators origins
    declarations := DeclarationTable.tableAtom table constants
    axioms := axioms
    key := key
    dependencies := Premises.keys (record.dependencies.map (CacheAuthorization.Dependency.atom constants))
    premise := premise
    typeName := typeName
    abstractionName := abstractionName
    representationName := representationName
    cache := CacheAuthorization.entries constants cache
    receipts := receipts }

def publishedWorld (source : Input) (constants : Const → Atom)
    (predicate : CheckedSourceTerm) (represented : Ty) (texts : List String) : Atom :=
  TypeDefinitionPublication.completedWorld
    (TypeDefinitionConstruction.newOperators source constants predicate texts)
    (TypeDefinitionConstruction.newConstants source constants predicate represented texts) source.axioms source.key
    (Representation.termAtom Representation.registeredOperatorAtom
      (TypeDefinitionConstruction.identities source constants predicate texts) []
      (TypeDefinitionEquations.firstLaw (TypeDefinitionConstruction.abstraction source predicate texts)
        (TypeDefinitionConstruction.representation source predicate texts) represented
        (TypeDefinitionConstruction.carrier source predicate texts)))
    (Representation.termAtom Representation.registeredOperatorAtom
      (TypeDefinitionConstruction.identities source constants predicate texts) []
      (TypeDefinitionEquations.secondLaw (TypeDefinitionConstruction.abstraction source predicate texts)
        (TypeDefinitionConstruction.representation source predicate texts) represented
        (TypeDefinitionConstruction.carrier source predicate texts) predicate.canonical.term))
    source.dependencies source.typeName source.abstractionName source.representationName source.premise
    source.cache source.receipts

private theorem publications_succeed (source : Input) (constants : Const → Atom)
    (predicate : CheckedSourceTerm) (represented : Ty) (texts : List String)
    (receiptFresh : ReceiptKeys.presentB (TypeDefinitionFormation.representationKey source.key) source.receipts = false)
    (cacheFresh : source.cache.lookup (TypeDefinitionFormation.representationKey source.key) = none) :
    TypeDefinitionConstruction.result source constants predicate represented texts =
      .expression [.symbol "Some", publishedWorld source constants predicate represented texts] := by
  have different : (TypeDefinitionFormation.representationKey source.key == source.key) = false :=
    beq_eq_false_iff_ne.mpr (TypeDefinitionPublication.representation_key_ne source.key)
  simp [TypeDefinitionConstruction.result, TypeDefinitionPublication.finalResult, Publication.result,
    Publication.afterState, publishedWorld, TypeDefinitionPublication.completedWorld,
    ReceiptKeys.presentB, different, cacheFresh, List.lookup] at receiptFresh ⊢
  exact receiptFresh

/-- The whole source event earns the same registered definition and two
derived records. Neither a premise derivation nor output formation is an
assumed soundness interface. The resulting source world is identified with
the registered tables and authorized cache, including unchanged old values. -/
theorem authored_event_earns_records (policy : AxiomPolicy) (context : TheoryContext)
    (table : DeclarationTable.Table context) (origins : TypeOp → Atom) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies context constants)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (axioms key premise : Atom) (typeName abstractionName representationName : String)
    (cache : CacheAuthorization.Cache) (valid : CacheAuthorization.Valid policy context cache)
    (record : CacheAuthorization.Record) (selected : cache.lookup premise = some record)
    (predicate : CheckedSourceTerm) (witness : CanonicalTerm)
    (application : CanonicalTerm.ApplicationSemantics predicate.canonical witness record.conclusion)
    (empty : record.hypotheses = []) (closed : predicate.canonical.term.HasNoFreeVariables)
    (global : TypeParameterOrdering.globalParameters predicate.canonical.term)
    (functionArity : context.signature.typeOperators TypeOp.function = some 2)
    (booleanFormed : TypeFormed context.signature Ty.bool) (equalityParameter : Name)
    (equalityRegistered : context.signature.constants Const.equality = some (Ty.equality (.var equalityParameter)))
    (typeFresh : .typeOperator (sourceOperatorName (Name.global typeName)) ∉ context.names)
    (absFresh : .constant (Name.global abstractionName) ∉ context.names)
    (repFresh : .constant (Name.global representationName) ∉ context.names)
    (different : abstractionName ≠ representationName) (receipts : List ReceiptKeys.Entry)
    (receiptFresh : ReceiptKeys.presentB key receipts = false)
    (cacheFresh : (CacheAuthorization.entries constants cache).lookup key = none)
    (representationReceiptFresh : ReceiptKeys.presentB (TypeDefinitionFormation.representationKey key) receipts = false)
    (representationCacheFresh : (CacheAuthorization.entries constants cache).lookup
      (TypeDefinitionFormation.representationKey key) = none)
    (bindings : Subst) (state : State) (stateKey keyName requestName : String)
    (worldCaptured : applySubst bindings (.var stateKey) = TypeDefinitionExecution.world
      (input context table origins constants axioms key premise typeName abstractionName representationName record cache receipts))
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) =
      TypeDefinitionFormation.command typeName abstractionName representationName premise) :
    ∃ texts witnesses result, ∃ declarations : DeclarationTable.Table result.context,
      let source := input context table origins constants axioms key premise typeName abstractionName representationName record cache receipts
      let request := TypeDefinitionAdmission.request typeName abstractionName representationName texts predicate record.fact
      let command := TypeDefinitionFormation.command typeName abstractionName representationName premise
      let first := TypeDefinitionFormation.outputRecord key command result.output.abstractionRepresentationTheorem.sequent.concl record.dependencies
      let second := TypeDefinitionFormation.outputRecord (TypeDefinitionFormation.representationKey key) command
        result.output.representationAbstractionTheorem.sequent.concl record.dependencies
      texts.map Name.global = sortedParameters predicate.source ∧
      BoundCalls.PureReturns program bindings state
        (.expression [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName]) state
        (.expression [.symbol "Some", publishedWorld source constants predicate witness.ty texts]) ∧
      admitSourceTypeInTheory context witnesses request = some result ∧
      TheoryDerives policy context record.fact ∧
      TheoryDerives policy result.context first.fact ∧ TheoryDerives policy result.context second.fact ∧
      CacheAuthorization.Valid policy result.context
        ((TypeDefinitionFormation.representationKey key, second) :: (key, first) :: cache) ∧
      first.conclusion.term = TypeDefinitionEquations.firstLaw
        (TypeDefinitionConstruction.abstraction source predicate texts)
        (TypeDefinitionConstruction.representation source predicate texts) witness.ty
        (TypeDefinitionConstruction.carrier source predicate texts) ∧
      second.conclusion.term = TypeDefinitionEquations.secondLaw
        (TypeDefinitionConstruction.abstraction source predicate texts)
        (TypeDefinitionConstruction.representation source predicate texts) witness.ty
        (TypeDefinitionConstruction.carrier source predicate texts) predicate.canonical.term ∧
      first.dependencies = record.dependencies ∧ second.dependencies = record.dependencies ∧
      first.origin = .expression [.symbol "HOL:Origin", key, command] ∧
      second.origin = .expression [.symbol "HOL:Origin", TypeDefinitionFormation.representationKey key, command] ∧
      DeclarationTable.Identifies result.context (TypeDefinitionConstruction.identities source constants predicate texts) ∧
      CacheAuthorization.entries (TypeDefinitionConstruction.identities source constants predicate texts) cache =
        CacheAuthorization.entries constants cache ∧
      publishedWorld source constants predicate witness.ty texts = ProofLookup.sourceState
        (OperatorTable.tableAtom declarations.operators (TypeDefinitionTables.origins source origins constants predicate texts))
        (DeclarationTable.tableAtom declarations (TypeDefinitionConstruction.identities source constants predicate texts))
        axioms (ReceiptKeys.table
          (⟨TypeDefinitionFormation.representationKey key, command, [premise]⟩ :: ⟨key, command, [premise]⟩ :: receipts))
        (CacheAuthorization.entries (TypeDefinitionConstruction.identities source constants predicate texts)
          ((TypeDefinitionFormation.representationKey key, second) :: (key, first) :: cache)) := by
  let source := input context table origins constants axioms key premise typeName abstractionName representationName record cache receipts
  have retrieved := CacheAuthorization.stored_lookup_derived policy context cache valid premise record selected
  have boolean : record.conclusion.IsBool := retrieved.conclusionBoolean
  have components : AnnotationsFormed context.signature predicate.canonical.term ∧
      AnnotationsFormed context.signature witness.term := by
    obtain ⟨_, _, _, _, shape⟩ := application
    have whole : AnnotationsFormed context.signature (.app predicate.canonical.term witness.term) := by
      rw [← shape]
      exact retrieved.wellFormed.1.1
    cases whole with | app function argument => exact ⟨function, argument⟩
  have representedFormed := AnnotationsFormed.inferredType context.signature functionArity components.2
    (by simp [ContextFormed]) witness.checked
  have typed : predicate.ty = .function witness.ty Ty.bool := by
    have recognized := (Ty.destFunction?_eq_some_iff _ _ _).mp application.functionType
    exact recognized.trans (congrArg (Ty.function witness.ty) boolean)
  have found : source.cache.lookup premise = some (record.atom constants) := by
    change (CacheAuthorization.entries constants cache).lookup premise = _
    rw [CacheAuthorization.lookup_entries, selected]
    rfl
  have earned := CacheAuthorization.lookup_derived policy context constants identified cache valid
    premise record retrieved.wellFormed found
  have sourceFound : source.cache.lookup source.premise =
      some (TypeDefinitionExecution.premiseValue source constants predicate witness record.origin) := by
    obtain ⟨_, _, _, _, shape⟩ := application
    simpa only [CacheAuthorization.Record.atom, Representation.theoremAtom, empty, List.map_nil,
      Premises.keys, TypeDefinitionExecution.premiseValue, shape, Representation.termAtom, source, input] using found
  obtain ⟨texts, ordered, returned⟩ := TypeDefinitionEvents.authored_step_returns source context table origins constants
    rfl rfl predicate witness record.origin sourceFound typeFresh absFresh repFresh different global typed
    components.1 closed equalityIdentity receiptFresh cacheFresh bindings state stateKey keyName requestName
    worldCaptured keyCaptured requestCaptured
  have emptyHypotheses : record.fact.sequent.hyp = ∅ := by simp [CacheAuthorization.Record.fact, empty]
  obtain ⟨witnesses, result, accepted⟩ := TypeDefinitionAdmission.registered_admission_constructed context
    typeName abstractionName representationName texts predicate record.fact witness ordered application emptyHypotheses
    boolean closed components.1 components.2 representedFormed functionArity typeFresh absFresh repFresh different
  let command := TypeDefinitionFormation.command typeName abstractionName representationName premise
  let first := TypeDefinitionFormation.outputRecord key command result.output.abstractionRepresentationTheorem.sequent.concl record.dependencies
  let second := TypeDefinitionFormation.outputRecord (TypeDefinitionFormation.representationKey key) command
    result.output.representationAbstractionTheorem.sequent.concl record.dependencies
  have derived := TypeDefinitionFormation.source_outputs_derived policy context witnesses _ predicate.canonical witness
    application boolean result accepted earned functionArity booleanFormed equalityParameter equalityRegistered
  have retained := admitSourceTypeInTheory_result accepted
  have firstFact := TypeDefinitionFormation.output_record_fact key command record result.output.abstractionRepresentationTheorem
    (retained.2.2.2.2.1.trans emptyHypotheses) retained.2.2.1
  have secondFact := TypeDefinitionFormation.output_record_fact (TypeDefinitionFormation.representationKey key) command record
    result.output.representationAbstractionTheorem (retained.2.2.2.2.2.trans emptyHypotheses) retained.2.2.2.1
  have firstDerived : TheoryDerives policy result.context first.fact := firstFact ▸ derived.1
  have secondDerived : TheoryDerives policy result.context second.fact := secondFact ▸ derived.2
  have formulas := TypeDefinitionConstruction.registered_output_correspondence source predicate texts record.fact witness
    application boolean context witnesses result accepted
  obtain ⟨declarations, identifiedAfter, operatorRows, constantRows⟩ :=
    TypeDefinitionTables.admitted_tables_agree context table source origins constants identified predicate texts record.fact
      witness application boolean witnesses result accepted rfl rfl
  have oldCache := TypeDefinitionTables.old_cache_retained policy context source constants predicate texts cache valid absFresh repFresh
  have dependencies := TypeDefinitionTables.dependencies_retained context source constants predicate texts record retrieved.wellFormed absFresh repFresh
  have actualWorld : publishedWorld source constants predicate witness.ty texts = ProofLookup.sourceState
      (OperatorTable.tableAtom declarations.operators (TypeDefinitionTables.origins source origins constants predicate texts))
      (DeclarationTable.tableAtom declarations (TypeDefinitionConstruction.identities source constants predicate texts))
      axioms (ReceiptKeys.table
        (⟨TypeDefinitionFormation.representationKey key, command, [premise]⟩ :: ⟨key, command, [premise]⟩ :: receipts))
      (CacheAuthorization.entries (TypeDefinitionConstruction.identities source constants predicate texts)
        ((TypeDefinitionFormation.representationKey key, second) :: (key, first) :: cache)) := by
    rw [operatorRows, constantRows]
    simp only [CacheAuthorization.entries, List.map_cons, TypeDefinitionFormation.outputRecord,
      CacheAuthorization.Record.atom, Representation.theoremAtom, List.map_nil,
      Premises.keys, formulas.1, formulas.2, first, second, dependencies]
    change publishedWorld source constants predicate witness.ty texts = ProofLookup.sourceState
      (TypeDefinitionConstruction.newOperators source constants predicate texts)
      (TypeDefinitionConstruction.newConstants source constants predicate witness.ty texts)
      axioms (ReceiptKeys.table
        (⟨TypeDefinitionFormation.representationKey key, command, [premise]⟩ :: ⟨key, command, [premise]⟩ :: receipts))
      ((TypeDefinitionFormation.representationKey key,
          Publication.publishedValue (TypeDefinitionFormation.representationKey key) command (.symbol "HOL:Nil")
            (Representation.termAtom Representation.registeredOperatorAtom
              (TypeDefinitionConstruction.identities source constants predicate texts) []
              (TypeDefinitionEquations.secondLaw (TypeDefinitionConstruction.abstraction source predicate texts)
                (TypeDefinitionConstruction.representation source predicate texts) witness.ty
                (TypeDefinitionConstruction.carrier source predicate texts) predicate.canonical.term)) source.dependencies) ::
        (key, Publication.publishedValue key command (.symbol "HOL:Nil")
          (Representation.termAtom Representation.registeredOperatorAtom
            (TypeDefinitionConstruction.identities source constants predicate texts) []
            (TypeDefinitionEquations.firstLaw (TypeDefinitionConstruction.abstraction source predicate texts)
              (TypeDefinitionConstruction.representation source predicate texts) witness.ty
              (TypeDefinitionConstruction.carrier source predicate texts))) source.dependencies) ::
        CacheAuthorization.entries (TypeDefinitionConstruction.identities source constants predicate texts) cache)
    rw [oldCache]
    rfl
  rw [publications_succeed source constants predicate witness.ty texts representationReceiptFresh representationCacheFresh] at returned
  exact ⟨texts, witnesses, result, declarations, ordered, returned, accepted, earned, firstDerived, secondDerived,
    CacheAuthorization.insert_valid (CacheAuthorization.insert_valid (CacheAuthorization.weaken_valid retained.1 valid)
      key first firstDerived) (TypeDefinitionFormation.representationKey key) second secondDerived,
    formulas.1, formulas.2, rfl, rfl, rfl, rfl, identifiedAfter, oldCache, actualWorld⟩

end Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionCacheHistory
