import Mettapedia.Languages.HOLLight.ConstantHistoryExpandedTypes

/-!
# Type instances of installed uniform source type definitions

The original abstraction and representation Symbols follow the original
source type substitution through one assignment-independent witnessed
operator family. Declaration licences are recovered from the actual source
admission and remain distinct from malformed raw symbol annotations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.UniformTypeDefinitionInstances

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics ModelInterpretation SignatureFormation ModelInstanceCoherence
open DefinitionAdapters UniformTypeDefinitionFamily UniformTypeDefinitionModels

universe w

variable {initial context : TheoryContext}
  (history : DefinitionHistoryModels.ConstantHistory initial context)
  {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
  (accepted : admitSourceTypeInTheory context instances request = some result)
  (proof : HOL.ClosedTheorySet.Provable (definitionTheory history) (TypeAdmission.admittedImage accepted).formula)
  (other : OperatorFamilies.{w})

include accepted in
/-- The exact source gate's successor registry, with its original symbol
identities and retained representation type. -/
theorem source_signature : result.context.signature =
    ((context.signature.addTypeOperator (SourceTypeDefinitionTransport.operator request) request.typeVariables.length).addConstant result.output.abstractionConstant
        (abstractionAnnotation (request := request) (result := result) TypeSubst.empty)).addConstant result.output.representationConstant
        (representationAnnotation (request := request) (result := result) TypeSubst.empty) := by
  cases view : request.existence.sequent.concl.applicationView? with
  | none => simp [admitSourceTypeInTheory, view] at accepted
  | some application =>
      simp only [admitSourceTypeInTheory, view] at accepted
      cases admitted : admitTypeInTheoryFromApplication context instances request
          application.function application.argument application.semantics with
      | none => simp [admitted] at accepted
      | some core =>
          simp only [admitted] at accepted
          split at accepted
          · have equal := Option.some.inj accepted
            subst result
            unfold admitTypeInTheoryFromApplication at admitted
            split at admitted
            · split at admitted
              · split at admitted
                · split at admitted
                  · split at admitted
                    · cases admitted
                    · have equal := Option.some.inj admitted
                      subst core
                      simp only [abstractionAnnotation, representationAnnotation, TypeSubst.apply_empty,
                        SourceTypeDefinitionTransport.sourceCarrierType]
                      rfl
                  · cases admitted
                · cases admitted
              · cases admitted
            · cases admitted
          · contradiction

theorem sourceCarrierType_composition (first second : TypeSubst) :
    second.apply (SourceTypeDefinitionTransport.sourceCarrierType request first) =
      SourceTypeDefinitionTransport.sourceCarrierType request (first.compose second) := by
  simp only [SourceTypeDefinitionTransport.sourceCarrierType, TypeSubst.apply_op, List.map_map]
  congr 1
  apply List.map_congr_left
  intro parameter member
  exact (TypeSubst.apply_compose first second (.var parameter)).symm

theorem abstractionAnnotation_composition (first second : TypeSubst) :
    second.apply (abstractionAnnotation (request := request) (result := result) first) =
      abstractionAnnotation (request := request) (result := result) (first.compose second) := by
  rw [abstractionAnnotation, TypeSubst.apply_function, sourceCarrierType_composition, ← TypeSubst.apply_compose]
  rfl

theorem representationAnnotation_composition (first second : TypeSubst) :
    second.apply (representationAnnotation (request := request) (result := result) first) =
      representationAnnotation (request := request) (result := result) (first.compose second) := by
  rw [representationAnnotation, TypeSubst.apply_function, sourceCarrierType_composition, ← TypeSubst.apply_compose]
  rfl

theorem instanceArguments_composition (assignment : Assignment.{w}) (first second : TypeSubst) :
    instanceArguments history accepted proof other
      (reindex (primitiveFamilies (operators history accepted proof other)) second assignment) first =
    instanceArguments history accepted proof other assignment (first.compose second) := by
  unfold instanceArguments
  rw [reindex_composition]

theorem abstractionInstance_composition (assignment : Assignment.{w}) (first second : TypeSubst) :
    HEq (abstractionInstance history accepted proof other
      (reindex (primitiveFamilies (operators history accepted proof other)) second assignment) first)
      (abstractionInstance history accepted proof other assignment (first.compose second)) := by
  have maps : HEq
      (abstraction history accepted proof other (instanceAssignment history accepted proof other
        (reindex (primitiveFamilies (operators history accepted proof other)) second assignment) first))
      (abstraction history accepted proof other (instanceAssignment history accepted proof other assignment (first.compose second))) := by
    unfold instanceAssignment
    rw [instanceArguments_composition]
  exact (abstractionInstance_heq history accepted proof other _ first).trans
    (maps.trans (abstractionInstance_heq history accepted proof other assignment (first.compose second)).symm)

theorem representationInstance_composition (assignment : Assignment.{w}) (first second : TypeSubst) :
    HEq (representationInstance history accepted proof other
      (reindex (primitiveFamilies (operators history accepted proof other)) second assignment) first)
      (representationInstance history accepted proof other assignment (first.compose second)) := by
  have maps : HEq
      (representation history accepted proof other (instanceAssignment history accepted proof other
        (reindex (primitiveFamilies (operators history accepted proof other)) second assignment) first))
      (representation history accepted proof other (instanceAssignment history accepted proof other assignment (first.compose second))) := by
    unfold instanceAssignment
    rw [instanceArguments_composition]
  exact (representationInstance_heq history accepted proof other _ first).trans
    (maps.trans (representationInstance_heq history accepted proof other assignment (first.compose second)).symm)

theorem abstraction_meaning_of_annotation (assignment : Assignment.{w}) (substitution : TypeSubst)
    {annotation : Ty} (same : annotation = abstractionAnnotation (request := request) (result := result) substitution)
    {type : HOL.Ty AtomicTy} (typed : annotation.toHOL = type) :
    HEq ((model history accepted proof other assignment).constDen
      (.constant result.output.abstractionConstant annotation typed))
      (abstraction history accepted proof other (instanceAssignment history accepted proof other assignment substitution)) := by
  subst annotation
  exact meanings_abstraction_heq history accepted proof other assignment substitution typed

theorem representation_meaning_of_annotation (assignment : Assignment.{w}) (substitution : TypeSubst)
    {annotation : Ty} (same : annotation = representationAnnotation (request := request) (result := result) substitution)
    {type : HOL.Ty AtomicTy} (typed : annotation.toHOL = type) :
    HEq ((model history accepted proof other assignment).constDen
      (.constant result.output.representationConstant annotation typed))
      (representation history accepted proof other (instanceAssignment history accepted proof other assignment substitution)) := by
  subst annotation
  exact meanings_representation_heq history accepted proof other assignment substitution typed

/-- Original symbol substitution retains the abstraction identity and gives
exactly the map at the composed original parameter instance. -/
theorem abstraction_symbol_composition (assignment : Assignment.{w}) (first second : TypeSubst)
    {type : HOL.Ty AtomicTy}
    (typed : (abstractionAnnotation (request := request) (result := result) first).toHOL = type) :
    HEq ((model history accepted proof other
      (reindex (primitiveFamilies (operators history accepted proof other)) second assignment)).constDen
      (.constant result.output.abstractionConstant (abstractionAnnotation (request := request) (result := result) first) typed))
      ((model history accepted proof other assignment).constDen
        (second.symbolInstance (.constant result.output.abstractionConstant
          (abstractionAnnotation (request := request) (result := result) first) typed))) := by
  have maps : HEq
      (abstraction history accepted proof other (instanceAssignment history accepted proof other
        (reindex (primitiveFamilies (operators history accepted proof other)) second assignment) first))
      (abstraction history accepted proof other (instanceAssignment history accepted proof other assignment (first.compose second))) := by
    unfold instanceAssignment
    rw [instanceArguments_composition]
  exact (meanings_abstraction_heq history accepted proof other _ first typed).trans
    (maps.trans (abstraction_meaning_of_annotation history accepted proof other assignment (first.compose second)
      (abstractionAnnotation_composition first second) _).symm)

theorem representation_symbol_composition (assignment : Assignment.{w}) (first second : TypeSubst)
    {type : HOL.Ty AtomicTy}
    (typed : (representationAnnotation (request := request) (result := result) first).toHOL = type) :
    HEq ((model history accepted proof other
      (reindex (primitiveFamilies (operators history accepted proof other)) second assignment)).constDen
      (.constant result.output.representationConstant (representationAnnotation (request := request) (result := result) first) typed))
      ((model history accepted proof other assignment).constDen
        (second.symbolInstance (.constant result.output.representationConstant
          (representationAnnotation (request := request) (result := result) first) typed))) := by
  have maps : HEq
      (representation history accepted proof other (instanceAssignment history accepted proof other
        (reindex (primitiveFamilies (operators history accepted proof other)) second assignment) first))
      (representation history accepted proof other (instanceAssignment history accepted proof other assignment (first.compose second))) := by
    unfold instanceAssignment
    rw [instanceArguments_composition]
  exact (meanings_representation_heq history accepted proof other _ first typed).trans
    (maps.trans (representation_meaning_of_annotation history accepted proof other assignment (first.compose second)
      (representationAnnotation_composition first second) _).symm)

include accepted in
theorem new_constants_registered :
    result.context.signature.constants result.output.abstractionConstant =
      some (abstractionAnnotation (request := request) (result := result) TypeSubst.empty) ∧
    result.context.signature.constants result.output.representationConstant =
      some (representationAnnotation (request := request) (result := result) TypeSubst.empty) := by
  rw [source_signature accepted]
  simp [Signature.addConstant, Ne.symm (SourceTypeDefinitionTransport.admitted_constants_distinct accepted)]

include accepted in
theorem licensed_abstraction_instance {annotation : Ty}
    (declared : ConstantInstance result.context.signature result.output.abstractionConstant annotation) :
    ∃ substitution, annotation = abstractionAnnotation (request := request) (result := result) substitution := by
  obtain ⟨schema, substitution, found, equal⟩ := declared
  have schemaEq := Option.some.inj (found.symm.trans (new_constants_registered accepted).1)
  subst schema
  exact ⟨substitution, equal.symm.trans (abstractionAnnotation_composition TypeSubst.empty substitution)⟩

include accepted in
theorem licensed_representation_instance {annotation : Ty}
    (declared : ConstantInstance result.context.signature result.output.representationConstant annotation) :
    ∃ substitution, annotation = representationAnnotation (request := request) (result := result) substitution := by
  obtain ⟨schema, substitution, found, equal⟩ := declared
  have schemaEq := Option.some.inj (found.symm.trans (new_constants_registered accepted).2)
  subst schema
  exact ⟨substitution, equal.symm.trans (representationAnnotation_composition TypeSubst.empty substitution)⟩

include accepted in
/-- A licensed different successor constant retains its original declaration
row, including provenance and the submitted type-instance evidence. -/
theorem old_constant_instance {constant : Const} {annotation : Ty}
    (notAbstraction : constant ≠ result.output.abstractionConstant)
    (notRepresentation : constant ≠ result.output.representationConstant)
    (declared : ConstantInstance result.context.signature constant annotation) :
    ConstantInstance context.signature constant annotation := by
  obtain ⟨schema, substitution, found, equal⟩ := declared
  refine ⟨schema, substitution, ?_, equal⟩
  rw [source_signature accepted] at found
  simpa [Signature.addConstant, Signature.addTypeOperator, notAbstraction, notRepresentation] using found

/-- Actual predecessor meanings follow the original substitution at all
instances formed in a later type table, with the original constant rows. -/
theorem carrierModel_instance_agreement_withTypes (later : Signature)
    (types : ∀ operator arity, result.context.signature.typeOperators operator = some arity →
      later.typeOperators operator = some arity)
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (equalityParameter : Name)
    (equalityRegistered : initial.signature.constants Const.equality = some (Ty.equality (.var equalityParameter)))
    (selectionParameter : Name)
    (selectionDeclaration : initial.signature.constants selectionConstant = none ∨
      initial.signature.constants selectionConstant = some (selectionType (.var selectionParameter)))
    (assignment : Assignment.{w}) (substitution : TypeSubst) :
    SourceAgreement (ConstantHistoryExpandedTypes.withTypes context.signature later)
      (carrierModel history accepted proof other
        (reindex (primitiveFamilies (operators history accepted proof other)) substitution assignment))
      (reindexedModel substitution (carrierModel history accepted proof other assignment)) :=
  ConstantHistoryExpandedTypes.history_instance_agreement history later
    (fun operator arity found => types operator arity ((admitSourceTypeInTheory_result accepted).1.1 operator arity
      (history.includes.1 operator arity found))) functionArity equalityParameter equalityRegistered
    selectionParameter selectionDeclaration (operators history accepted proof other) assignment substitution

/-- Actual predecessor meanings at all subsequently formed types follow the
original source substitution. The larger-table law is earned from every
prior original admission. -/
theorem carrierModel_instance_agreement (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (equalityParameter : Name)
    (equalityRegistered : initial.signature.constants Const.equality = some (Ty.equality (.var equalityParameter)))
    (selectionParameter : Name)
    (selectionDeclaration : initial.signature.constants selectionConstant = none ∨
      initial.signature.constants selectionConstant = some (selectionType (.var selectionParameter)))
    (assignment : Assignment.{w}) (substitution : TypeSubst) :
    SourceAgreement (comparisonSignature (context := context) (result := result))
      (carrierModel history accepted proof other
        (reindex (primitiveFamilies (operators history accepted proof other)) substitution assignment))
      (reindexedModel substitution (carrierModel history accepted proof other assignment)) :=
  carrierModel_instance_agreement_withTypes history accepted proof other result.context.signature
    (fun _ _ found => found) functionArity equalityParameter equalityRegistered
    selectionParameter selectionDeclaration assignment substitution

/-- Carriers of the actual installed model are precisely the carrier reduct
under original source type substitution. -/
theorem model_reindex_carrier (assignment : Assignment.{w}) (substitution : TypeSubst) :
    (model history accepted proof other
      (reindex (primitiveFamilies (operators history accepted proof other)) substitution assignment)).Carrier =
    (reindexedModel substitution (model history accepted proof other assignment)).Carrier := by
  change (model history accepted proof other
    (reindex (primitiveFamilies (operators history accepted proof other)) substitution assignment)).Carrier =
      fun atomic => HOL.Ty.denote (model history accepted proof other assignment).Carrier (substitution.baseInstance atomic)
  rw [UniformTypeDefinitionSupport.model_carrier_eq_atomic, UniformTypeDefinitionSupport.model_carrier_eq_atomic]
  exact atomicCarrier_reindex (operators history accepted proof other) substitution assignment

set_option backward.isDefEq.respectTransparency false in
/-- The complete installed source model is coherent at every original
licensed type instance, including old declarations at the new carrier types.
No coherence of the constructed family is assumed. -/
theorem model_instance_agreement_withTypes (later : Signature)
    (types : ∀ operator arity, result.context.signature.typeOperators operator = some arity →
      later.typeOperators operator = some arity)
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (equalityParameter : Name)
    (equalityRegistered : initial.signature.constants Const.equality = some (Ty.equality (.var equalityParameter)))
    (selectionParameter : Name)
    (selectionDeclaration : initial.signature.constants selectionConstant = none ∨
      initial.signature.constants selectionConstant = some (selectionType (.var selectionParameter)))
    (assignment : Assignment.{w}) (substitution : TypeSubst) :
    SourceAgreement (ConstantHistoryExpandedTypes.withTypes result.context.signature later)
      (model history accepted proof other
        (reindex (primitiveFamilies (operators history accepted proof other)) substitution assignment))
      (reindexedModel substitution (model history accepted proof other assignment)) := by
  have predecessor := carrierModel_instance_agreement_withTypes history accepted proof other later types
    functionArity equalityParameter equalityRegistered selectionParameter selectionDeclaration assignment substitution
  refine ⟨?_, ?_, ?_⟩
  · intro type formed
    exact congrArg (fun carrier => HOL.Ty.denote carrier type)
      (model_reindex_carrier history accepted proof other assignment substitution)
  · intro constant annotation type typed formed declared
    by_cases abstractionName : constant = result.output.abstractionConstant
    · subst constant
      obtain ⟨first, rfl⟩ := licensed_abstraction_instance accepted declared
      change HEq _ ((HOL.Ty.denoteSubstituteEquiv substitution.baseInstance
        (model history accepted proof other assignment).Carrier type).symm
        ((model history accepted proof other assignment).constDen
          (substitution.symbolInstance (.constant result.output.abstractionConstant _ typed))))
      exact (abstraction_symbol_composition history accepted proof other assignment first substitution typed).trans
        (HOL.Ty.denoteSubstituteEquiv_symm_apply_heq _ _ _ _).symm
    · by_cases representationName : constant = result.output.representationConstant
      · subst constant
        obtain ⟨first, rfl⟩ := licensed_representation_instance accepted declared
        change HEq _ ((HOL.Ty.denoteSubstituteEquiv substitution.baseInstance
          (model history accepted proof other assignment).Carrier type).symm
          ((model history accepted proof other assignment).constDen
            (substitution.symbolInstance (.constant result.output.representationConstant _ typed))))
        exact (representation_symbol_composition history accepted proof other assignment first substitution typed).trans
          (HOL.Ty.denoteSubstituteEquiv_symm_apply_heq _ _ _ _).symm
      · have priorDeclared := old_constant_instance accepted abstractionName representationName declared
        have priorFormed := (typeFormed_eq_of_operators (ConstantHistoryExpandedTypes.withTypes result.context.signature later)
          (ConstantHistoryExpandedTypes.withTypes context.signature later) rfl annotation).mp formed
        have compared := predecessor.constants constant annotation typed priorFormed priorDeclared
        change HEq _ ((HOL.Ty.denoteSubstituteEquiv substitution.baseInstance
          (model history accepted proof other assignment).Carrier type).symm
          ((model history accepted proof other assignment).constDen
            (substitution.symbolInstance (.constant constant annotation typed))))
        simp only [TypeSubst.symbolInstance]
        rw [meanings_other history accepted proof other _ typed abstractionName representationName,
          meanings_other history accepted proof other assignment _ abstractionName representationName]
        exact compared
  · intro sourceVar type typed formed
    have priorFormed := (typeFormed_eq_of_operators (ConstantHistoryExpandedTypes.withTypes result.context.signature later)
      (ConstantHistoryExpandedTypes.withTypes context.signature later) rfl sourceVar.ty).mp formed
    have compared := predecessor.variableValues sourceVar typed priorFormed
    change HEq _ ((HOL.Ty.denoteSubstituteEquiv substitution.baseInstance
      (model history accepted proof other assignment).Carrier type).symm
      ((model history accepted proof other assignment).constDen
        (substitution.symbolInstance (.variable sourceVar typed))))
    simp only [TypeSubst.symbolInstance]
    rw [meanings_variable history accepted proof other _ sourceVar typed,
      meanings_variable history accepted proof other assignment _ _]
    exact compared

/-- Every actual licensed successor instance satisfies the earned source
comparison. This specializes the later-type-table law to the current registry. -/
theorem model_instance_agreement (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (equalityParameter : Name)
    (equalityRegistered : initial.signature.constants Const.equality = some (Ty.equality (.var equalityParameter)))
    (selectionParameter : Name)
    (selectionDeclaration : initial.signature.constants selectionConstant = none ∨
      initial.signature.constants selectionConstant = some (selectionType (.var selectionParameter)))
    (assignment : Assignment.{w}) (substitution : TypeSubst) :
    SourceAgreement result.context.signature
      (model history accepted proof other
        (reindex (primitiveFamilies (operators history accepted proof other)) substitution assignment))
      (reindexedModel substitution (model history accepted proof other assignment)) :=
  model_instance_agreement_withTypes history accepted proof other result.context.signature
    (fun _ _ found => found) functionArity equalityParameter equalityRegistered
    selectionParameter selectionDeclaration assignment substitution

/-- Original formed source sentences have exactly the truth of their actual
source type instances in the constructed uniform model. -/
theorem model_models_instance (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (equalityParameter : Name)
    (equalityRegistered : initial.signature.constants Const.equality = some (Ty.equality (.var equalityParameter)))
    (selectionParameter : Name)
    (selectionDeclaration : initial.signature.constants selectionConstant = none ∨
      initial.signature.constants selectionConstant = some (selectionType (.var selectionParameter)))
    (assignment : Assignment.{w}) (substitution : TypeSubst)
    {term : DBTerm} {formula : HOL.ClosedFormula Symbol}
    (translation : TranslatesCompositionally [] term .prop formula)
    (formed : AnnotationsFormed result.context.signature term) :
    (model history accepted proof other
      (reindex (primitiveFamilies (operators history accepted proof other)) substitution assignment)).models formula ↔
      (model history accepted proof other assignment).models
        (HOL.mapTypes substitution.baseInstance substitution.symbolInstance formula) :=
  ((model_instance_agreement history accepted proof other functionArity equalityParameter equalityRegistered
    selectionParameter selectionDeclaration assignment substitution).models
      ((admitSourceTypeInTheory_result accepted).1.1 TypeOp.function 2
        (history.includes.1 TypeOp.function 2 functionArity))
      (model_fullDomains history accepted proof other _) (reindexedModel_fullDomains _ _)
      translation formed).trans (reindexedModel_models substitution _ (model_fullDomains history accepted proof other _) formula)

include accepted in
theorem abstraction_registered_instance (substitution : TypeSubst) :
    ConstantInstance result.context.signature result.output.abstractionConstant
      (abstractionAnnotation (request := request) (result := result) substitution) :=
  ⟨abstractionAnnotation (request := request) (result := result) TypeSubst.empty,
    substitution, (new_constants_registered accepted).1,
    abstractionAnnotation_composition TypeSubst.empty substitution⟩

include accepted in
theorem representation_registered_instance (substitution : TypeSubst) :
    ConstantInstance result.context.signature result.output.representationConstant
      (representationAnnotation (request := request) (result := result) substitution) :=
  ⟨representationAnnotation (request := request) (result := result) TypeSubst.empty,
    substitution, (new_constants_registered accepted).2,
    representationAnnotation_composition TypeSubst.empty substitution⟩

include accepted in
/-- A raw variable annotation cannot be an original public abstraction
instance; formation of some later transformed annotation cannot supply the
missing original declaration licence. -/
theorem abstraction_variable_annotation_unlicensed (parameter : Name) :
    ¬ ConstantInstance result.context.signature result.output.abstractionConstant (.var parameter) := by
  intro declared
  obtain ⟨substitution, same⟩ := licensed_abstraction_instance accepted declared
  cases same

/-- The earned instance law persists through an arbitrary following original
constant history. Both the source comparison and reduct commutation use the
actual chronological admission receipts. -/
theorem constant_suffix_instance_agreement {final : TheoryContext}
    (suffix : DefinitionHistoryModels.ConstantHistory result.context final)
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (equalityParameter : Name)
    (equalityRegistered : initial.signature.constants Const.equality = some (Ty.equality (.var equalityParameter)))
    (selectionParameter : Name)
    (selectionDeclaration : initial.signature.constants selectionConstant = none ∨
      initial.signature.constants selectionConstant = some (selectionType (.var selectionParameter)))
    (assignment : Assignment.{w}) (substitution : TypeSubst) :
    SourceAgreement final.signature
      (suffix.extendModel (model history accepted proof other
        (reindex (primitiveFamilies (operators history accepted proof other)) substitution assignment)))
      (reindexedModel substitution (suffix.extendModel (model history accepted proof other assignment))) := by
  have sourceIncluded := history.includes.trans (admitSourceTypeInTheory_result accepted).1
  have functionRegistered := sourceIncluded.1 TypeOp.function 2 functionArity
  have modelCompared := model_instance_agreement history accepted proof other functionArity
    equalityParameter equalityRegistered selectionParameter selectionDeclaration assignment substitution
  exact ConstantHistoryInstanceCoherence.sourceAgreement_trans
    (modelCompared.constantHistory suffix functionRegistered (model_fullDomains history accepted proof other _)
      (reindexedModel_fullDomains _ _))
    (ConstantHistoryInstanceCoherence.constantHistory_reindex_agreement suffix functionRegistered
      equalityParameter (sourceIncluded.2 Const.equality _ equalityRegistered)
      (model history accepted proof other assignment) (model_fullDomains history accepted proof other _) substitution)

/-- Every following original constant history also obeys the instance law
on its declarations at types introduced still later. -/
theorem constant_suffix_instance_agreement_withTypes {final : TheoryContext}
    (suffix : DefinitionHistoryModels.ConstantHistory result.context final)
    (later : Signature)
    (types : ∀ operator arity, result.context.signature.typeOperators operator = some arity →
      later.typeOperators operator = some arity)
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (equalityParameter : Name)
    (equalityRegistered : initial.signature.constants Const.equality = some (Ty.equality (.var equalityParameter)))
    (selectionParameter : Name)
    (selectionDeclaration : initial.signature.constants selectionConstant = none ∨
      initial.signature.constants selectionConstant = some (selectionType (.var selectionParameter)))
    (assignment : Assignment.{w}) (substitution : TypeSubst) :
    SourceAgreement (ConstantHistoryExpandedTypes.withTypes final.signature later)
      (suffix.extendModel (model history accepted proof other
        (reindex (primitiveFamilies (operators history accepted proof other)) substitution assignment)))
      (reindexedModel substitution (suffix.extendModel (model history accepted proof other assignment))) := by
  have sourceIncluded := history.includes.trans (admitSourceTypeInTheory_result accepted).1
  have functionRegistered := sourceIncluded.1 TypeOp.function 2 functionArity
  have modelCompared := model_instance_agreement_withTypes history accepted proof other later types functionArity
    equalityParameter equalityRegistered selectionParameter selectionDeclaration assignment substitution
  exact ConstantHistoryInstanceCoherence.sourceAgreement_trans
    (ConstantHistoryExpandedTypes.history_agreement suffix later types functionRegistered modelCompared
      (model_fullDomains history accepted proof other _) (reindexedModel_fullDomains _ _))
    (ConstantHistoryExpandedTypes.history_reindex_agreement suffix later types functionRegistered
      equalityParameter (sourceIncluded.2 Const.equality _ equalityRegistered)
      (model history accepted proof other assignment) (model_fullDomains history accepted proof other _) substitution)

namespace Controls

open UniformTypeDefinitionFamily.Controls DefinitionAdapters.ContextControls

theorem original_abstraction_schema_formed : TypeFormed polymorphicResult.context.signature
    (abstractionAnnotation (request := polymorphicRequest) (result := polymorphicResult) TypeSubst.empty) := by
  apply (typeFormedB_eq_true_iff _ _).mp
  decide +kernel

theorem original_representation_schema_formed : TypeFormed polymorphicResult.context.signature
    (representationAnnotation (request := polymorphicRequest) (result := polymorphicResult) TypeSubst.empty) := by
  apply (typeFormedB_eq_true_iff _ _).mp
  decide +kernel

/-- Both original parameter-bearing Symbols in one actual model follow
source substitution to Boolean, function and newly introduced carrier types. -/
theorem original_symbols_substitution (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (substitution : TypeSubst) :
    let originalHistory := DefinitionHistoryModels.Controls.polymorphicDefinitions
    let originalOperators := operators originalHistory polymorphic_result_admitted polymorphic_existence_proven other
    let current := model originalHistory polymorphic_result_admitted polymorphic_existence_proven other
    HEq ((current (reindex (primitiveFamilies originalOperators) substitution assignment)).constDen
      (.constant polymorphicResult.output.abstractionConstant
        (abstractionAnnotation (request := polymorphicRequest) (result := polymorphicResult) TypeSubst.empty) rfl))
      ((reindexedModel substitution (current assignment)).constDen
        (.constant polymorphicResult.output.abstractionConstant
          (abstractionAnnotation (request := polymorphicRequest) (result := polymorphicResult) TypeSubst.empty) rfl)) ∧
    HEq ((current (reindex (primitiveFamilies originalOperators) substitution assignment)).constDen
      (.constant polymorphicResult.output.representationConstant
        (representationAnnotation (request := polymorphicRequest) (result := polymorphicResult) TypeSubst.empty) rfl))
      ((reindexedModel substitution (current assignment)).constDen
        (.constant polymorphicResult.output.representationConstant
          (representationAnnotation (request := polymorphicRequest) (result := polymorphicResult) TypeSubst.empty) rfl)) := by
  intro originalHistory originalOperators current
  have compared := model_instance_agreement originalHistory polymorphic_result_admitted polymorphic_existence_proven
    other (core_includes.1 TypeOp.function 2 function_registered) equalityParameter
    ConstantHistoryInstanceCoherence.Controls.core_equality_registered equalityParameter
    (Or.inl ConstantHistoryInstanceCoherence.Controls.core_selection_unregistered) assignment substitution
  exact ⟨compared.constants _ _ rfl original_abstraction_schema_formed
      (abstraction_registered_instance polymorphic_result_admitted TypeSubst.empty),
    compared.constants _ _ rfl original_representation_schema_formed
      (representation_registered_instance polymorphic_result_admitted TypeSubst.empty)⟩

def rawAnnotationSubstitution : TypeSubst :=
  ⟨[(TypeFamilySemantics.Controls.alpha,
    abstractionAnnotation (request := polymorphicRequest) (result := polymorphicResult) TypeSubst.empty)]⟩

/-- A malformed original annotation may acquire the licensed map shape after
substitution. This is why the uniform law retains original source licences. -/
theorem recognition_requires_original_licence :
    ¬ ConstantInstance polymorphicResult.context.signature polymorphicResult.output.abstractionConstant
      (.var TypeFamilySemantics.Controls.alpha) ∧
    rawAnnotationSubstitution.apply (.var TypeFamilySemantics.Controls.alpha) =
      abstractionAnnotation (request := polymorphicRequest) (result := polymorphicResult) TypeSubst.empty ∧
    ConstantInstance polymorphicResult.context.signature polymorphicResult.output.abstractionConstant
      (rawAnnotationSubstitution.apply (.var TypeFamilySemantics.Controls.alpha)) := by
  have same : rawAnnotationSubstitution.apply (.var TypeFamilySemantics.Controls.alpha) =
      abstractionAnnotation (request := polymorphicRequest) (result := polymorphicResult) TypeSubst.empty := by
    apply (Ty.same_eq_true_iff _ _).mp
    decide +kernel
  refine ⟨abstraction_variable_annotation_unlicensed polymorphic_result_admitted _, same, ?_⟩
  rw [same]
  exact abstraction_registered_instance polymorphic_result_admitted TypeSubst.empty

/-- The successor still rejects wrong public arities, despite the total
semantic interpretation of raw annotations. -/
theorem malformed_public_instance_refused :
    typeFormedB polymorphicResult.context.signature
      (abstractionAnnotation (request := polymorphicRequest) (result := polymorphicResult)
        UniformTypeDefinitionModels.Controls.malformedInstance) = false := by
  decide +kernel

end Controls

end Mettapedia.Languages.HOLLight.UniformTypeDefinitionInstances
