import Mettapedia.Languages.HOLLight.MeTTa.DefinitionEvents

/-!
# Earned definition evidence in the actual source history

A successful definition event extends the registered declaration table,
retains earlier proof records, and publishes its own derived equation. The
source cache and receipt carry the exact definition command and identity.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.DefinitionHistory

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters
open DefinitionExecution

def publishedRecord (key : Atom) (name : String) (body : CheckedSourceTerm) : CacheAuthorization.Record :=
  ⟨[], (makeConstantDefinition (Name.global name) body.source body.canonical).definitionTheorem.sequent.concl,
    [], .expression [.symbol "HOL:Origin", key, definitionRequest name body]⟩

theorem published_record_fact (key : Atom) (name : String) (body : CheckedSourceTerm) :
    (publishedRecord key name body).fact =
      (makeConstantDefinition (Name.global name) body.source body.canonical).definitionTheorem := by
  rfl

theorem published_record_value (constants : Const → Atom) (key : Atom) (name : String) (body : CheckedSourceTerm) :
    (publishedRecord key name body).atom (definedIdentities constants name body) =
      Publication.publishedValue key (definitionRequest name body) (.symbol "HOL:Nil")
        (Representation.termAtom Representation.registeredOperatorAtom (definedIdentities constants name body) []
          (definingEquation body name)) (.symbol "HOL:Nil") := rfl

/-- The extended source rows are exactly the registered table, including the
new definition identity and every unchanged earlier declaration identity. -/
theorem extended_table_registered (context : TheoryContext) (table : DeclarationTable.Table context)
    (constants : Const → Atom) (name : String) (body : CheckedSourceTerm)
    (formed : TypeFormed context.signature body.ty) (fresh : .constant (Name.global name) ∉ context.names) :
    DeclarationTable.tableAtom (DeclarationTable.addConstant table (definedConstant name body) body.ty formed fresh)
      (definedIdentities constants name body) =
      extendedConstants (DeclarationTable.tableAtom table constants) constants name body := by
  have oldRows : table.constants.map (DeclarationTable.entryAtom (definedIdentities constants name body)) =
      table.constants.map (DeclarationTable.entryAtom constants) := by
    apply List.map_congr_left
    intro entry member
    have retained := DeclarationTable.old_constant_identity_preserved context (definedConstant name body)
      entry.1 entry.2 constants (definitionIdentity constants name body) fresh (table.registered entry member)
    simp only [definedIdentities, DeclarationTable.entryAtom, retained]
  simp only [DeclarationTable.tableAtom, DeclarationTable.entriesAtom, DeclarationTable.addConstant,
    List.map_cons, oldRows]
  simp [DeclarationTable.entryAtom, definedIdentities, DeclarationTable.extendIdentity,
    definedConstant, constantName, Lookup.table, Premises.keys, Const.same_eq_true_iff, extendedConstants]

/-- With fresh event addresses, the computed definition classification
publishes exactly when the shared source definition side conditions hold.
The claim is confined to checked, resolved bodies at fresh definition names. -/
theorem classified_publication_iff (context : TheoryContext) (table : DeclarationTable.Table context)
    (origins : TypeOp → Atom) (constants : Const → Atom) (axioms key : Atom)
    (name : String) (body : CheckedSourceTerm) (fresh : .constant (Name.global name) ∉ context.names)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (receiptFresh : ReceiptKeys.presentB key receipts = false) (cacheFresh : cache.lookup key = none) :
    classifiedResult context table origins constants axioms key name body cache receipts ≠ .symbol "None" ↔
      ConstantAdmissible context.names (Name.global name) body.source := by
  rw [side_conditions_iff]
  simp [classifiedResult, definitionResult, Publication.result, receiptFresh, cacheFresh, fresh,
    FreeVariables.free_atoms_nil_iff]

/-- Publication of an admitted definition earns its new cache record in the
same registered calculus used by imported and authored inference proofs. -/
theorem authored_step_preserves_history (policy : AxiomPolicy) (context : TheoryContext)
    (table : DeclarationTable.Table context) (origins : TypeOp → Atom) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies context constants)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (axioms key : Atom) (name : String) (body : CheckedSourceTerm)
    (sourceResolved : TermReading.SourceResolved context.signature body.source)
    (schemaResolved : TypeFormation.Resolved context.signature body.ty)
    (formed : AnnotationsFormed context.signature body.canonical.term)
    (schemaFormed : TypeFormed context.signature body.ty)
    (fresh : .constant (Name.global name) ∉ context.names)
    (closed : body.canonical.term.HasNoFreeVariables)
    (parameters : body.canonical.term.typeVariables ⊆ body.ty.typeVariables)
    (equalityFormed : TypeFormed context.signature (Ty.equality body.ty))
    (equalityRegistered : ConstantInstance context.signature Const.equality (Ty.equality body.ty))
    (cache : CacheAuthorization.Cache) (valid : CacheAuthorization.Valid policy context cache)
    (receipts : List ReceiptKeys.Entry) (receiptFresh : ReceiptKeys.presentB key receipts = false)
    (cacheFresh : (CacheAuthorization.entries constants cache).lookup key = none)
    (bindings : Subst) (state : Effects.State) (stateName keyName requestName : String)
    (worldCaptured : applySubst bindings (.var stateName) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
      axioms (ReceiptKeys.table receipts) (CacheAuthorization.entries constants cache))
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = definitionRequest name body) :
    let extended := (registeredResult context name body schemaFormed fresh).context
    let identities := definedIdentities constants name body
    let declarations := DeclarationTable.addConstant table (definedConstant name body) body.ty schemaFormed fresh
    let record := publishedRecord key name body
    DeclarationTable.Identifies extended identities ∧
      TheoryDerives policy extended record.fact ∧
      CacheAuthorization.Valid policy extended ((key, record) :: cache) ∧
      CacheAuthorization.entries identities cache = CacheAuthorization.entries constants cache ∧
      BoundCalls.PureReturns program bindings state
        (.expression [.symbol "hol-light:step", .var stateName, .var keyName, .var requestName]) state
        (.expression [.symbol "Some", ProofLookup.sourceState
          (OperatorTable.tableAtom declarations.operators origins)
          (DeclarationTable.tableAtom declarations identities) axioms
          (ReceiptKeys.table (⟨key, definitionRequest name body, []⟩ :: receipts))
          (CacheAuthorization.entries identities ((key, record) :: cache))]) := by
  dsimp only
  have retained := definition_preserves_old_cache policy context constants name body schemaFormed fresh cache valid
  have derived := registered_definition_derives policy context name body formed schemaFormed fresh closed parameters
    equalityFormed equalityRegistered
  have newDerived : TheoryDerives policy (registeredResult context name body schemaFormed fresh).context
      (publishedRecord key name body).fact := by
    rw [published_record_fact]
    exact derived
  refine ⟨DeclarationTable.extended_identity_identifies context constants identified (definedConstant name body)
      body.ty schemaFormed fresh (definitionIdentity constants name body) rfl,
    newDerived, CacheAuthorization.insert_valid retained.1 key _ newDerived, retained.2, ?_⟩
  have actual := DefinitionEvents.authored_definition_step context table origins constants equalityIdentity axioms key name body
    sourceResolved schemaResolved formed schemaFormed fresh (CacheAuthorization.entries constants cache) receipts
    bindings state stateName keyName requestName worldCaptured keyCaptured requestCaptured
  have empty := (FreeVariables.free_atoms_nil_iff Representation.registeredOperatorAtom body.canonical.term).mpr closed
  simp only [receiptFresh, Bool.false_eq_true, ↓reduceIte, classifiedResult, empty, parameters,
    definitionResult, Publication.result, cacheFresh] at actual
  rw [← extended_table_registered context table constants name body schemaFormed fresh, ← retained.2] at actual
  have operatorsSame : OperatorTable.tableAtom
      (DeclarationTable.addConstant table (definedConstant name body) body.ty schemaFormed fresh).operators origins =
      OperatorTable.tableAtom table.operators origins := rfl
  rw [operatorsSame]
  simpa only [Publication.afterState, CacheAuthorization.entries, List.map_cons, published_record_value] using actual

end Mettapedia.Languages.HOLLight.MeTTa.DefinitionHistory
