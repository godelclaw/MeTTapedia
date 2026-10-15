import Mettapedia.Languages.HOLLight.MeTTa.AxiomDispatch

/-!
# Authorized AXIOM events extend the actual retained proof cache

The complete authored event earns its dependency in the selected registered
calculus and inserts the same formula, dependency label and command origin in
the source cache. This law composes with signature weakening and actual cache
retrieval. It does not authorize supplied cache records or an undeclared axiom.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.AxiomCacheHistory

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters
open Effects (State)
open Representation (registeredOperatorAtom termAtom)

def publishedRecord (key label : Atom) (source : CheckedSourceTerm)
    (isBool : source.canonical.IsBool) : CacheAuthorization.Record :=
  ⟨[], source.canonical, [AxiomExecution.dependency label source isBool],
    .expression [.symbol "HOL:Origin", key, AxiomDispatch.request label (TermReading.sourceAtom source.source)]⟩

theorem published_record_value (constants : Const → Atom) (key label : Atom)
    (source : CheckedSourceTerm) (isBool : source.canonical.IsBool) :
    (publishedRecord key label source isBool).atom constants =
      Publication.publishedValue key (AxiomDispatch.request label (TermReading.sourceAtom source.source))
        (.symbol "HOL:Nil") (termAtom registeredOperatorAtom constants [] source.canonical.term)
        (Premises.keys [.expression [.symbol "HOL:AxiomDependency", label,
          termAtom registeredOperatorAtom constants [] source.canonical.term]]) := rfl

/-- Publication retains the exact command origin while logical authorization
remains the derivation already constructed from the explicit commitment. -/
theorem published_record_derived (policy : AxiomPolicy) (world : TheoryContext)
    (key label : Atom) (source : CheckedSourceTerm) (isBool : source.canonical.IsBool)
    (formed : AnnotationsFormed world.signature source.canonical.term)
    (authorized : policy (AxiomExecution.dependency label source isBool).sequent) :
    TheoryDerives policy world (publishedRecord key label source isBool).fact :=
  AxiomExecution.record_derived policy world label source isBool formed authorized

/-- A complete admitted source event extends an already authorized history.
Its returned source state encodes precisely the resulting ordered cache;
dependency labels and event origins are not recovered from logical support. -/
theorem authored_step_preserves_valid (policy : AxiomPolicy) (world : TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants)
    (source expected : CheckedSourceTerm) (same : source.canonical = expected.canonical)
    (isBool : source.canonical.IsBool)
    (sourceResolved : TermReading.SourceResolved world.signature source.source)
    (expectedResolved : TermReading.SourceResolved world.signature expected.source)
    (sourceFormed : AnnotationsFormed world.signature source.canonical.term)
    (expectedFormed : AnnotationsFormed world.signature expected.canonical.term)
    (sourceTypeFormed : TypeFormed world.signature source.ty)
    (booleanFormed : TypeFormed world.signature Ty.bool)
    (key label : Atom) (authorized : policy (AxiomExecution.dependency label source isBool).sequent)
    (commitments : List (Atom × Atom)) (cache : CacheAuthorization.Cache)
    (valid : CacheAuthorization.Valid policy world cache) (receipts : List ReceiptKeys.Entry)
    (found : commitments.lookup label = some (TermReading.sourceAtom expected.source))
    (receiptFresh : ReceiptKeys.presentB key receipts = false)
    (cacheFresh : (CacheAuthorization.entries constants cache).lookup key = none)
    (bindings : Subst) (state : State) (stateName keyName requestName : String)
    (worldCaptured : applySubst bindings (.var stateName) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
      (Lookup.table commitments) (ReceiptKeys.table receipts) (CacheAuthorization.entries constants cache))
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) =
      AxiomDispatch.request label (TermReading.sourceAtom source.source)) :
    let record := publishedRecord key label source isBool
    TheoryDerives policy world record.fact ∧
      CacheAuthorization.Valid policy world ((key, record) :: cache) ∧
      BoundCalls.PureReturns program bindings state
        (.expression [.symbol "hol-light:step", .var stateName, .var keyName, .var requestName]) state
        (.expression [.symbol "Some", ProofLookup.sourceState
          (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
          (Lookup.table commitments)
          (ReceiptKeys.table (⟨key, AxiomDispatch.request label (TermReading.sourceAtom source.source), []⟩ :: receipts))
          (CacheAuthorization.entries constants ((key, record) :: cache))]) := by
  dsimp only
  have derived := published_record_derived policy world key label source isBool sourceFormed authorized
  refine ⟨derived, CacheAuthorization.insert_valid valid key _ derived, ?_⟩
  have actual := AxiomDispatch.authored_axiom_step_derivation world table origins constants identified
    source expected same isBool sourceResolved expectedResolved sourceFormed expectedFormed
    sourceTypeFormed booleanFormed policy key label authorized commitments (CacheAuthorization.entries constants cache)
    receipts found receiptFresh cacheFresh bindings state stateName keyName requestName
    worldCaptured keyCaptured requestCaptured
  simpa only [Publication.afterState, CacheAuthorization.entries, List.map_cons,
    published_record_value] using actual.2

end Mettapedia.Languages.HOLLight.MeTTa.AxiomCacheHistory
