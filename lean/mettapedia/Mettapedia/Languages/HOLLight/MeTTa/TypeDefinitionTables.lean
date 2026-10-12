import Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionConstruction

/-!
# Registered tables for the authored type-definition extension

The table is constructed through the existing carrier and map registrations.
Its constant rows retain the source presentation order. Identity and origin
payloads are changed only at the fresh declarations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionTables

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters
open TypeDefinitionConstruction (Input)

/-- The existing registered extension with the source's map-row order. -/
def extension (context : TheoryContext) (before : DeclarationTable.Table context)
    (request : TypeOperatorDefinitionRequest) (represented : Ty)
    (functionArity : context.signature.typeOperators TypeOp.function = some 2)
    (representedFormed : TypeFormed context.signature represented)
    (fresh : TypeNamesFresh context.names request) :
    DeclarationTable.Table (context.typeDefinitionExtension request represented functionArity representedFormed fresh) := by
  unfold TheoryContext.typeDefinitionExtension
  let operator : TypeOp := .mk request.typeName (.defined request.predicateSource request.typeVariables)
  let carrier : Ty := .op operator (request.typeVariables.map Ty.var)
  let withType := context.addTypeOperator operator request.typeVariables.length fresh.1
  have typeIncluded := context.addTypeOperator_includes operator request.typeVariables.length fresh.1
  have carrierFormed : TypeFormed withType.signature carrier := by
    simp only [carrier, TypeFormed, List.length_map]
    refine ⟨context.addTypeOperator_registered operator request.typeVariables.length fresh.1, ?_⟩
    intro argument member
    obtain ⟨name, _, rfl⟩ := List.mem_map.mp member
    simp only [TypeFormed]
  have representedInType := representedFormed.mono typeIncluded
  have functionInType := typeIncluded.1 TypeOp.function 2 functionArity
  have absFresh : .constant request.abstractionName ∉ withType.names := by
    simpa [withType, TheoryContext.addTypeOperator] using fresh.2.1
  let abstraction : Const := .mk request.abstractionName (.abstraction operator)
  let abstractionType := Ty.function represented carrier
  have abstractionFormed := TypeFormed.function withType.signature functionInType representedInType carrierFormed
  let withAbs := withType.addConstant abstraction abstractionType abstractionFormed absFresh
  have absIncluded := withType.addConstant_includes abstraction abstractionType abstractionFormed absFresh
  have repFresh : .constant request.representationName ∉ withAbs.names := by
    have different : request.representationName ≠ request.abstractionName := Ne.symm fresh.2.2.2
    simpa [withAbs, abstraction, TheoryContext.addConstant, constantName, withType,
      TheoryContext.addTypeOperator, different] using fresh.2.2.1
  let representation : Const := .mk request.representationName (.representation operator)
  let representationType := Ty.function carrier represented
  have representationFormed := TypeFormed.function withAbs.signature
    (absIncluded.1 TypeOp.function 2 functionInType)
    (carrierFormed.mono absIncluded) (representedInType.mono absIncluded)
  let typed := DeclarationTable.addTypeOperator before operator request.typeVariables.length fresh.1
  let abstracted := DeclarationTable.addConstant typed abstraction abstractionType abstractionFormed absFresh
  let registered := DeclarationTable.addConstant abstracted representation representationType representationFormed repFresh
  exact
    { operators := registered.operators
      constants := (abstraction, abstractionType) :: (representation, representationType) :: before.constants
      registered := by
        intro entry member
        apply registered.registered entry
        simpa only [registered, abstracted, typed, DeclarationTable.addConstant,
          DeclarationTable.addTypeOperator, List.mem_cons, or_left_comm] using member
      complete := by
        intro constant schema found
        have member := registered.complete constant schema found
        simpa only [registered, abstracted, typed, DeclarationTable.addConstant,
          DeclarationTable.addTypeOperator, List.mem_cons, or_left_comm] using member }

theorem extension_constants (context : TheoryContext) (before : DeclarationTable.Table context)
    (request : TypeOperatorDefinitionRequest) (represented : Ty)
    (functionArity : context.signature.typeOperators TypeOp.function = some 2)
    (representedFormed : TypeFormed context.signature represented)
    (fresh : TypeNamesFresh context.names request) :
    let operator := TypeOp.mk request.typeName (.defined request.predicateSource request.typeVariables)
    let carrier := Ty.op operator (request.typeVariables.map Ty.var)
    (extension context before request represented functionArity representedFormed fresh).constants =
      (.mk request.abstractionName (.abstraction operator), .function represented carrier) ::
      (.mk request.representationName (.representation operator), .function carrier represented) :: before.constants := rfl

theorem extension_operators (context : TheoryContext) (before : DeclarationTable.Table context)
    (request : TypeOperatorDefinitionRequest) (represented : Ty)
    (functionArity : context.signature.typeOperators TypeOp.function = some 2)
    (representedFormed : TypeFormed context.signature represented)
    (fresh : TypeNamesFresh context.names request) :
    (extension context before request represented functionArity representedFormed fresh).operators.entries =
      (.mk request.typeName (.defined request.predicateSource request.typeVariables), request.typeVariables.length) ::
      before.operators.entries := rfl

def origins (source : Input) (before : TypeOp → Atom) (constants : Const → Atom)
    (predicate : CheckedSourceTerm) (texts : List String) : TypeOp → Atom :=
  fun candidate => if TypeOp.same candidate (TypeDefinitionConstruction.operator source predicate texts) then
    .expression [.symbol "HOL:DefinedType", .grounded (.string source.typeName),
      Representation.termAtom Representation.registeredOperatorAtom constants [] predicate.canonical.term]
    else before candidate

/-- Every constant row, including old identity payloads, is the authored row. -/
theorem constant_rows_agree (context : TheoryContext) (before : DeclarationTable.Table context)
    (source : Input) (constants : Const → Atom) (predicate : CheckedSourceTerm)
    (represented : Ty) (texts : List String) (existence : Theorem)
    (functionArity : context.signature.typeOperators TypeOp.function = some 2)
    (representedFormed : TypeFormed context.signature represented)
    (fresh : TypeNamesFresh context.names (TypeDefinitionAdmission.request source.typeName
      source.abstractionName source.representationName texts predicate existence))
    (rows : source.declarations = DeclarationTable.tableAtom before constants) :
    DeclarationTable.tableAtom (extension context before
      (TypeDefinitionAdmission.request source.typeName source.abstractionName source.representationName texts predicate existence)
      represented functionArity representedFormed fresh)
      (TypeDefinitionConstruction.identities source constants predicate texts) =
      TypeDefinitionConstruction.newConstants source constants predicate represented texts := by
  have oldRows : before.constants.map (DeclarationTable.entryAtom
      (TypeDefinitionConstruction.identities source constants predicate texts)) =
      before.constants.map (DeclarationTable.entryAtom constants) := by
    apply List.map_congr_left
    intro entry member
    have found := before.registered entry member
    have absFresh : .constant (constantName (TypeDefinitionConstruction.abstraction source predicate texts)) ∉ context.names := fresh.2.1
    have repFresh : .constant (constantName (TypeDefinitionConstruction.representation source predicate texts)) ∉ context.names := fresh.2.2.1
    have repRetained := DeclarationTable.old_constant_identity_preserved context
      (TypeDefinitionConstruction.representation source predicate texts) entry.1 entry.2
      (DeclarationTable.extendIdentity constants (TypeDefinitionConstruction.abstraction source predicate texts)
        (TypeDefinitionConstruction.abstractionIdentity source constants predicate))
      (TypeDefinitionConstruction.representationIdentity source constants predicate) repFresh found
    have absRetained := DeclarationTable.old_constant_identity_preserved context
      (TypeDefinitionConstruction.abstraction source predicate texts) entry.1 entry.2 constants
      (TypeDefinitionConstruction.abstractionIdentity source constants predicate) absFresh found
    simp only [DeclarationTable.entryAtom, TypeDefinitionConstruction.identities, repRetained, absRetained]
  have shape := extension_constants context before _ represented functionArity representedFormed fresh
  dsimp only at shape
  unfold DeclarationTable.tableAtom DeclarationTable.entriesAtom
  rw [shape, List.map_cons, List.map_cons]
  change Lookup.table (DeclarationTable.entryAtom (TypeDefinitionConstruction.identities source constants predicate texts)
      (TypeDefinitionConstruction.abstraction source predicate texts,
        .function represented (TypeDefinitionConstruction.carrier source predicate texts)) ::
    DeclarationTable.entryAtom (TypeDefinitionConstruction.identities source constants predicate texts)
      (TypeDefinitionConstruction.representation source predicate texts,
        .function (TypeDefinitionConstruction.carrier source predicate texts) represented) ::
    before.constants.map (DeclarationTable.entryAtom (TypeDefinitionConstruction.identities source constants predicate texts))) = _
  rw [oldRows]
  simp only [DeclarationTable.entryAtom]
  rw [TypeDefinitionConstruction.abstraction_identity, TypeDefinitionConstruction.representation_identity]
  simp [TypeDefinitionConstruction.abstraction, TypeDefinitionConstruction.representation, constantName,
    TypeSubstitution.nameAtom, Name.global, Lookup.table, Premises.keys,
    TypeDefinitionConstruction.newConstants, rows, DeclarationTable.tableAtom, DeclarationTable.entriesAtom]
  rfl

/-- The carrier row also retains its source predicate provenance and arity. -/
theorem operator_rows_agree (context : TheoryContext) (before : DeclarationTable.Table context)
    (source : Input) (oldOrigins : TypeOp → Atom) (constants : Const → Atom)
    (predicate : CheckedSourceTerm) (represented : Ty) (texts : List String) (existence : Theorem)
    (functionArity : context.signature.typeOperators TypeOp.function = some 2)
    (representedFormed : TypeFormed context.signature represented)
    (fresh : TypeNamesFresh context.names (TypeDefinitionAdmission.request source.typeName
      source.abstractionName source.representationName texts predicate existence))
    (rows : source.operators = OperatorTable.tableAtom before.operators oldOrigins) :
    OperatorTable.tableAtom (extension context before
      (TypeDefinitionAdmission.request source.typeName source.abstractionName source.representationName texts predicate existence)
      represented functionArity representedFormed fresh).operators
      (origins source oldOrigins constants predicate texts) =
      TypeDefinitionConstruction.newOperators source constants predicate texts := by
  have oldRows : before.operators.entries.map (OperatorTable.entryAtom
      (origins source oldOrigins constants predicate texts)) =
      before.operators.entries.map (OperatorTable.entryAtom oldOrigins) := by
    apply List.map_congr_left
    intro entry member
    have different : entry.1 ≠ TypeDefinitionConstruction.operator source predicate texts := by
      intro same
      have found := before.operators.registered entry member
      have named := context.typeNames entry.1 entry.2 found
      rw [same] at named
      exact fresh.1 named
    simp [OperatorTable.entryAtom, origins, TypeOp.same_eq_true_iff, different]
  have shape := extension_operators context before _ represented functionArity representedFormed fresh
  unfold OperatorTable.tableAtom OperatorTable.entriesAtom
  rw [shape]
  simp only [TypeDefinitionAdmission.request, List.length_map, List.map_cons]
  change Lookup.table (OperatorTable.entryAtom (origins source oldOrigins constants predicate texts)
      (TypeDefinitionConstruction.operator source predicate texts, texts.length) ::
    before.operators.entries.map (OperatorTable.entryAtom (origins source oldOrigins constants predicate texts))) = _
  rw [oldRows]
  simp [OperatorTable.entryAtom, origins, TypeOp.same_eq_true_iff,
    TypeDefinitionConstruction.operator_spelling, Lookup.table,
    TypeDefinitionConstruction.newOperators, rows, OperatorTable.tableAtom, OperatorTable.entriesAtom]
  rfl

/-- Successful admission returns the constructed registered context. The
extension parameters are extracted from the gate's own checks. -/
theorem admitted_context (context : TheoryContext) (witnesses : InstanceWitnesses)
    (request : TypeOperatorDefinitionRequest) (predicate witness : CanonicalTerm)
    (application : CanonicalTerm.ApplicationSemantics predicate witness request.existence.sequent.concl)
    (boolean : request.existence.sequent.concl.IsBool) (result : SourceTypeDefinitionResult)
    (accepted : admitSourceTypeInTheory context witnesses request = some result) :
    ∃ functionArity : context.signature.typeOperators TypeOp.function = some 2,
      ∃ representedFormed : TypeFormed context.signature witness.ty,
        ∃ fresh : TypeNamesFresh context.names request,
          result.context = context.typeDefinitionExtension request witness.ty functionArity representedFormed fresh := by
  have core := (TypeDefinitionFormation.source_result_components context witnesses request
    predicate witness application boolean result accepted).1
  unfold admitTypeInTheoryFromApplication at core
  split at core
  · split at core
    · rename_i representedChecked
      split at core
      · rename_i functionArity
        split at core
        · rename_i fresh
          split at core
          · cases core
          · have same := congrArg ContextTypeDefinitionResult.context (Option.some.inj core)
            exact ⟨functionArity, (typeFormedB_eq_true_iff _ _).mp representedChecked, fresh, same.symm⟩
        · cases core
      · cases core
    · cases core
  · cases core

/-- The new maps satisfy the same identity projection as all old constants. -/
theorem identities_identify (context : TheoryContext) (source : Input) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies context constants) (predicate : CheckedSourceTerm)
    (represented : Ty) (texts : List String) (existence : Theorem)
    (functionArity : context.signature.typeOperators TypeOp.function = some 2)
    (representedFormed : TypeFormed context.signature represented)
    (fresh : TypeNamesFresh context.names (TypeDefinitionAdmission.request source.typeName
      source.abstractionName source.representationName texts predicate existence)) :
    DeclarationTable.Identifies (context.typeDefinitionExtension
      (TypeDefinitionAdmission.request source.typeName source.abstractionName source.representationName texts predicate existence)
      represented functionArity representedFormed fresh)
      (TypeDefinitionConstruction.identities source constants predicate texts) := by
  intro candidate schema registered
  by_cases isRep : candidate = TypeDefinitionConstruction.representation source predicate texts
  · subst candidate
    rw [TypeDefinitionConstruction.representation_identity]
    rfl
  · by_cases isAbs : candidate = TypeDefinitionConstruction.abstraction source predicate texts
    · subst candidate
      rw [TypeDefinitionConstruction.abstraction_identity]
      rfl
    · have old : context.signature.constants candidate = some schema := by
        have repComparison : Const.same candidate (TypeDefinitionConstruction.representation source predicate texts) = false :=
          Bool.eq_false_iff.mpr (fun same => isRep ((Const.same_eq_true_iff _ _).mp same))
        have absComparison : Const.same candidate (TypeDefinitionConstruction.abstraction source predicate texts) = false :=
          Bool.eq_false_iff.mpr (fun same => isAbs ((Const.same_eq_true_iff _ _).mp same))
        change (if Const.same candidate (TypeDefinitionConstruction.representation source predicate texts) then
            some (.function (TypeDefinitionConstruction.carrier source predicate texts) represented)
          else if Const.same candidate (TypeDefinitionConstruction.abstraction source predicate texts) then
            some (.function represented (TypeDefinitionConstruction.carrier source predicate texts))
          else context.signature.constants candidate) = some schema at registered
        simpa only [repComparison, absComparison, Bool.false_eq_true, ↓reduceIte] using registered
      have absFresh : .constant (constantName (TypeDefinitionConstruction.abstraction source predicate texts)) ∉ context.names := fresh.2.1
      have repFresh : .constant (constantName (TypeDefinitionConstruction.representation source predicate texts)) ∉ context.names := fresh.2.2.1
      rw [TypeDefinitionConstruction.identities,
        DeclarationTable.old_constant_identity_preserved context
          (TypeDefinitionConstruction.representation source predicate texts) candidate schema _ _ repFresh old,
        DeclarationTable.old_constant_identity_preserved context
          (TypeDefinitionConstruction.abstraction source predicate texts) candidate schema _ _ absFresh old]
      exact identified candidate schema old

/-- Old proof values retain all encoded hypotheses, dependencies and origins. -/
theorem old_cache_retained (policy : AxiomPolicy) (context : TheoryContext)
    (source : Input) (constants : Const → Atom) (predicate : CheckedSourceTerm)
    (texts : List String) (cache : CacheAuthorization.Cache)
    (valid : CacheAuthorization.Valid policy context cache)
    (absFresh : .constant (Name.global source.abstractionName) ∉ context.names)
    (repFresh : .constant (Name.global source.representationName) ∉ context.names) :
    CacheAuthorization.entries (TypeDefinitionConstruction.identities source constants predicate texts) cache =
      CacheAuthorization.entries constants cache := by
  have absUnregistered := context.constant_unregistered (TypeDefinitionConstruction.abstraction source predicate texts) absFresh
  have repUnregistered := context.constant_unregistered (TypeDefinitionConstruction.representation source predicate texts) repFresh
  unfold TypeDefinitionConstruction.identities
  rw [CacheAuthorization.entries_fresh_identity policy context _ repUnregistered _ _ _ valid,
    CacheAuthorization.entries_fresh_identity policy context _ absUnregistered _ _ _ valid]

theorem dependencies_retained (context : TheoryContext) (source : Input)
    (constants : Const → Atom) (predicate : CheckedSourceTerm) (texts : List String)
    (record : CacheAuthorization.Record) (formed : TheoremFormed context.signature record.fact)
    (absFresh : .constant (Name.global source.abstractionName) ∉ context.names)
    (repFresh : .constant (Name.global source.representationName) ∉ context.names) :
    record.dependencies.map (CacheAuthorization.Dependency.atom
        (TypeDefinitionConstruction.identities source constants predicate texts)) =
      record.dependencies.map (CacheAuthorization.Dependency.atom constants) := by
  have absUnregistered := context.constant_unregistered (TypeDefinitionConstruction.abstraction source predicate texts) absFresh
  have repUnregistered := context.constant_unregistered (TypeDefinitionConstruction.representation source predicate texts) repFresh
  unfold TypeDefinitionConstruction.identities
  rw [CacheAuthorization.dependencies_fresh_identity context _ repUnregistered _ _ record formed,
    CacheAuthorization.dependencies_fresh_identity context _ absUnregistered _ _ record formed]

/-- Admission and the authored rows produce one identified registered table,
including the newly defined operator's predicate provenance. -/
theorem admitted_tables_agree (context : TheoryContext) (before : DeclarationTable.Table context)
    (source : Input) (oldOrigins : TypeOp → Atom) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies context constants) (predicate : CheckedSourceTerm)
    (texts : List String) (existence : Theorem) (witness : CanonicalTerm)
    (application : CanonicalTerm.ApplicationSemantics predicate.canonical witness existence.sequent.concl)
    (boolean : existence.sequent.concl.IsBool) (witnesses : InstanceWitnesses)
    (result : SourceTypeDefinitionResult)
    (accepted : admitSourceTypeInTheory context witnesses
      (TypeDefinitionAdmission.request source.typeName source.abstractionName source.representationName texts predicate existence) = some result)
    (operatorRows : source.operators = OperatorTable.tableAtom before.operators oldOrigins)
    (constantRows : source.declarations = DeclarationTable.tableAtom before constants) :
    ∃ after : DeclarationTable.Table result.context,
      DeclarationTable.Identifies result.context (TypeDefinitionConstruction.identities source constants predicate texts) ∧
      OperatorTable.tableAtom after.operators (origins source oldOrigins constants predicate texts) =
        TypeDefinitionConstruction.newOperators source constants predicate texts ∧
      DeclarationTable.tableAtom after (TypeDefinitionConstruction.identities source constants predicate texts) =
        TypeDefinitionConstruction.newConstants source constants predicate witness.ty texts := by
  obtain ⟨functionArity, representedFormed, fresh, same⟩ := admitted_context context witnesses _
    predicate.canonical witness application boolean result accepted
  rw [same]
  exact ⟨extension context before _ witness.ty functionArity representedFormed fresh,
    identities_identify context source constants identified predicate witness.ty texts existence functionArity representedFormed fresh,
    operator_rows_agree context before source oldOrigins constants predicate witness.ty texts existence functionArity representedFormed fresh operatorRows,
    constant_rows_agree context before source constants predicate witness.ty texts existence functionArity representedFormed fresh constantRows⟩

/-- Swapping the two map identities fails the registration's name projection,
even when an observer ignores their predicate and carrier payloads. -/
theorem swapped_representation_identity_refused (source : Input) (constants : Const → Atom)
    (predicate : CheckedSourceTerm) (texts : List String)
    (different : source.abstractionName ≠ source.representationName) :
    DeclarationTable.identityName? (TypeDefinitionConstruction.representationIdentity source constants predicate) ≠
      some (TypeSubstitution.nameAtom (constantName (TypeDefinitionConstruction.abstraction source predicate texts))) := by
  intro same
  have names : Name.global source.representationName = Name.global source.abstractionName :=
    TypeSubstitution.nameAtom_injective (Option.some.inj same)
  exact different (congrArg Name.component names).symm

end Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionTables
