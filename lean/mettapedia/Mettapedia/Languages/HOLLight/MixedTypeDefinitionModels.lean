import Mettapedia.Languages.HOLLight.MixedDefinitionModelFamily
import Mettapedia.Languages.HOLLight.TypeDefinitionModels

/-!
# Installed original source symbols over a constructed mixed predecessor

The next witnessed family and original abstraction/representation Symbols
are interpreted over the actual preceding model construction. Source
annotations are the original admitted declarations; no new syntax or
acceptance authority is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MixedTypeDefinitionModels

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics ModelInterpretation SignatureFormation ModelInstanceCoherence
open DefinitionAdapters MixedDefinitionHistory MixedDefinitionModelFamily
open MixedDefinitionModelFamily.Witnessed
open UniformTypeDefinitionFamily (tupleAssignment tupleAssignment_mapped represented_support)
open UniformTypeDefinitionModels (abstractionAnnotation representationAnnotation licensed_old_constant comparisonSignature comparisonSignature_includes instance_predicate_formed)
open UniformTypeDefinitionInstances (abstractionAnnotation_composition representationAnnotation_composition licensed_abstraction_instance licensed_representation_instance old_constant_instance)
open ConstantHistoryExpandedTypes (withTypes)

universe w

variable {initial context : TheoryContext} {records : List Theorem}
  {history : History initial context records}
  (prior : Construction.{w} history)
  {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
  (accepted : admitSourceTypeInTheory context instances request = some result)
  (proof : HOL.ClosedTheorySet.Provable (equationTheory records) (TypeAdmission.admittedImage accepted).formula)
  (other : OperatorFamilies.{w}) (assignment : Assignment.{w})

noncomputable def instanceArguments (substitution : TypeSubst) : List Domain.{w} :=
  TypeDefinitionModels.instanceArguments
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (substitution := substitution)

noncomputable def instanceAssignment (substitution : TypeSubst) : Assignment.{w} :=
  TypeDefinitionModels.instanceAssignment
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (substitution := substitution)

theorem instanceAssignment_agrees (substitution : TypeSubst) :
    ∀ parameter ∈ request.typeVariables,
      instanceAssignment prior accepted proof other assignment substitution parameter =
        reindex (primitiveFamilies (operators prior accepted proof other)) substitution assignment parameter := by
  exact TypeDefinitionModels.instanceAssignment_agrees
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (substitution := substitution)

theorem represented_carrier (substitution : TypeSubst) :
    HOL.Ty.denote.{0, w + 1} (carrierModel prior accepted proof other assignment).Carrier
      (substitution.apply result.core.witness.ty).toHOL =
    HOL.Ty.denote.{0, w + 1}
      (prior.model other (instanceAssignment prior accepted proof other assignment substitution)).Carrier
      result.core.witness.ty.toHOL := by
  exact TypeDefinitionModels.represented_carrier
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (substitution := substitution)

theorem new_carrier (substitution : TypeSubst) :
    HOL.Ty.denote.{0, w + 1} (carrierModel prior accepted proof other assignment).Carrier
      (SourceTypeDefinitionTransport.sourceCarrierType request substitution).toHOL =
      (predicateDomain prior accepted proof other
        (instanceAssignment prior accepted proof other assignment substitution)).Carrier := by
  exact TypeDefinitionModels.new_carrier
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (substitution := substitution)

noncomputable def abstractionInstance (substitution : TypeSubst) :
    HOL.Ty.denote.{0, w + 1} (carrierModel prior accepted proof other assignment).Carrier
      (Ty.function (substitution.apply result.core.witness.ty)
        (SourceTypeDefinitionTransport.sourceCarrierType request substitution)).toHOL :=
  TypeDefinitionModels.abstractionInstance
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (substitution := substitution)

noncomputable def representationInstance (substitution : TypeSubst) :
    HOL.Ty.denote.{0, w + 1} (carrierModel prior accepted proof other assignment).Carrier
      (Ty.function (SourceTypeDefinitionTransport.sourceCarrierType request substitution)
        (substitution.apply result.core.witness.ty)).toHOL :=
  TypeDefinitionModels.representationInstance
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (substitution := substitution)

theorem abstractionInstance_heq (substitution : TypeSubst) :
    HEq (abstractionInstance prior accepted proof other assignment substitution)
      (abstraction prior accepted proof other
        (instanceAssignment prior accepted proof other assignment substitution)) := by
  exact TypeDefinitionModels.abstractionInstance_heq
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (substitution := substitution)

theorem representationInstance_heq (substitution : TypeSubst) :
    HEq (representationInstance prior accepted proof other assignment substitution)
      (representation prior accepted proof other
        (instanceAssignment prior accepted proof other assignment substitution)) := by
  exact TypeDefinitionModels.representationInstance_heq
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (substitution := substitution)

theorem instanceArguments_eq {first second : TypeSubst}
    (same : SourceTypeDefinitionTransport.sourceCarrierType request first =
      SourceTypeDefinitionTransport.sourceCarrierType request second) :
    instanceArguments prior accepted proof other assignment first =
      instanceArguments prior accepted proof other assignment second := by
  exact TypeDefinitionModels.instanceArguments_eq
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (first := first)
    (second := second)
    (same := same)

theorem abstractionInstance_choice_independent {first second : TypeSubst}
    (same : abstractionAnnotation (request := request) (result := result) first =
      abstractionAnnotation (request := request) (result := result) second) :
    HEq (abstractionInstance prior accepted proof other assignment first)
      (abstractionInstance prior accepted proof other assignment second) := by
  exact TypeDefinitionModels.abstractionInstance_choice_independent
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (first := first)
    (second := second)
    (same := same)

theorem representationInstance_choice_independent {first second : TypeSubst}
    (same : representationAnnotation (request := request) (result := result) first =
      representationAnnotation (request := request) (result := result) second) :
    HEq (representationInstance prior accepted proof other assignment first)
      (representationInstance prior accepted proof other assignment second) := by
  exact TypeDefinitionModels.representationInstance_choice_independent
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (first := first)
    (second := second)
    (same := same)

noncomputable def meanings : ∀ {type}, Symbol type →
    HOL.Ty.denote.{0, w + 1} (carrierModel prior accepted proof other assignment).Carrier type:=
  TypeDefinitionModels.meanings
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)

noncomputable def model : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol :=
  TypeDefinitionModels.model
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)

theorem model_carrier : (model prior accepted proof other assignment).Carrier =
    (carrierModel prior accepted proof other assignment).Carrier := by
  exact TypeDefinitionModels.model_carrier
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)

theorem model_fullDomains : (model prior accepted proof other assignment).FullDomains := by
  exact TypeDefinitionModels.model_fullDomains
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)

theorem meanings_abstraction (substitution : TypeSubst) :
    (model prior accepted proof other assignment).constDen
      (.constant result.output.abstractionConstant
        (abstractionAnnotation (request := request) (result := result) substitution) rfl) =
      abstractionInstance prior accepted proof other assignment substitution := by
  exact TypeDefinitionModels.meanings_abstraction
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (substitution := substitution)

theorem meanings_representation (substitution : TypeSubst) :
    (model prior accepted proof other assignment).constDen
      (.constant result.output.representationConstant
        (representationAnnotation (request := request) (result := result) substitution) rfl) =
      representationInstance prior accepted proof other assignment substitution := by
  exact TypeDefinitionModels.meanings_representation
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (substitution := substitution)

theorem meanings_other {constant : Const} {annotation : Ty} {type : HOL.Ty AtomicTy}
    (typed : annotation.toHOL = type)
    (notAbstraction : constant ≠ result.output.abstractionConstant)
    (notRepresentation : constant ≠ result.output.representationConstant) :
    (model prior accepted proof other assignment).constDen (.constant constant annotation typed) =
      (carrierModel prior accepted proof other assignment).constDen (.constant constant annotation typed) := by
  exact TypeDefinitionModels.meanings_other
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (constant := constant)
    (annotation := annotation)
    (type := type)
    (typed := typed)
    (notAbstraction := notAbstraction)
    (notRepresentation := notRepresentation)

theorem meanings_variable (sourceVar : SourceVar) {type : HOL.Ty AtomicTy}
    (typed : sourceVar.ty.toHOL = type) :
    (model prior accepted proof other assignment).constDen (.variable sourceVar typed) =
      (carrierModel prior accepted proof other assignment).constDen (.variable sourceVar typed) := by
  exact TypeDefinitionModels.meanings_variable
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (sourceVar := sourceVar)
    (type := type)
    (typed := typed)

theorem model_carrierModel_agreement :
    SourceAgreement context.signature (model prior accepted proof other assignment)
      (carrierModel prior accepted proof other assignment):= by
  exact TypeDefinitionModels.model_carrierModel_agreement
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)

theorem model_old_agreement :
    SourceAgreement context.signature (model prior accepted proof other assignment)
      (prior.model other assignment) := by
  exact TypeDefinitionModels.model_old_agreement
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)

theorem model_models_old
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    {term : DBTerm} {formula : HOL.ClosedFormula Symbol}
    (translated : TranslatesCompositionally [] term .prop formula)
    (formed : AnnotationsFormed context.signature term) :
    (model prior accepted proof other assignment).models formula ↔
      (prior.model other assignment).models formula := by
  exact TypeDefinitionModels.model_models_old
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (functionArity := functionArity)
    (term := term)
    (formula := formula)
    (translated := translated)
    (formed := formed)

theorem meanings_abstraction_heq (substitution : TypeSubst) {type : HOL.Ty AtomicTy}
    (typed : (abstractionAnnotation (request := request) (result := result) substitution).toHOL = type) :
    HEq ((model prior accepted proof other assignment).constDen
      (.constant result.output.abstractionConstant
        (abstractionAnnotation (request := request) (result := result) substitution) typed))
      (abstraction prior accepted proof other
        (instanceAssignment prior accepted proof other assignment substitution)) := by
  exact TypeDefinitionModels.meanings_abstraction_heq
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (substitution := substitution)
    (type := type)
    (typed := typed)

theorem meanings_representation_heq (substitution : TypeSubst) {type : HOL.Ty AtomicTy}
    (typed : (representationAnnotation (request := request) (result := result) substitution).toHOL = type) :
    HEq ((model prior accepted proof other assignment).constDen
      (.constant result.output.representationConstant
        (representationAnnotation (request := request) (result := result) substitution) typed))
      (representation prior accepted proof other
        (instanceAssignment prior accepted proof other assignment substitution)) := by
  exact TypeDefinitionModels.meanings_representation_heq
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (substitution := substitution)
    (type := type)
    (typed := typed)

theorem model_abstraction_representation (substitution : TypeSubst)
    (value : HOL.Ty.denote.{0, w + 1} (model prior accepted proof other assignment).Carrier
      (SourceTypeDefinitionTransport.sourceCarrierType request substitution).toHOL) :
    (model prior accepted proof other assignment).constDen
        (.constant result.output.abstractionConstant
          (abstractionAnnotation (request := request) (result := result) substitution) (Ty.toHOL_function _ _))
      ((model prior accepted proof other assignment).constDen
        (.constant result.output.representationConstant
          (representationAnnotation (request := request) (result := result) substitution) (Ty.toHOL_function _ _)) value) = value := by
  exact TypeDefinitionModels.model_abstraction_representation
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (substitution := substitution)
    (value := value)

theorem instanceArguments_assignment_agreement (first second : Assignment.{w}) (substitution : TypeSubst)
    (agree : ∀ parameter ∈ (SourceTypeDefinitionTransport.sourceCarrierType request substitution).typeVariables,
      first parameter = second parameter) :
    instanceArguments prior accepted proof other first substitution =
      instanceArguments prior accepted proof other second substitution := by
  exact TypeDefinitionModels.instanceArguments_assignment_agreement
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (first := first)
    (second := second)
    (substitution := substitution)
    (agree := agree)

theorem abstraction_assignment_agreement (first second : Assignment.{w}) (substitution : TypeSubst)
    (agree : ∀ parameter ∈ (abstractionAnnotation (request := request) (result := result) substitution).typeVariables,
      first parameter = second parameter) :
    HEq (abstractionInstance prior accepted proof other first substitution)
      (abstractionInstance prior accepted proof other second substitution) := by
  exact TypeDefinitionModels.abstraction_assignment_agreement
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (first := first)
    (second := second)
    (substitution := substitution)
    (agree := agree)

theorem representation_assignment_agreement (first second : Assignment.{w}) (substitution : TypeSubst)
    (agree : ∀ parameter ∈ (representationAnnotation (request := request) (result := result) substitution).typeVariables,
      first parameter = second parameter) :
    HEq (representationInstance prior accepted proof other first substitution)
      (representationInstance prior accepted proof other second substitution) := by
  exact TypeDefinitionModels.representation_assignment_agreement
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (first := first)
    (second := second)
    (substitution := substitution)
    (agree := agree)

theorem model_carrier_eq_atomic (assignment : Assignment.{w}) :
    (model prior accepted proof other assignment).Carrier =
      atomicCarrier (operators prior accepted proof other) assignment := by
  exact TypeDefinitionModels.model_carrier_eq_atomic
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)

theorem model_symbol_local : ModelAssignmentSupport.SymbolLocal (model prior accepted proof other) := by
  exact TypeDefinitionModels.model_symbol_local
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)

theorem instanceArguments_composition (assignment : Assignment.{w}) (first second : TypeSubst) :
    instanceArguments prior accepted proof other
      (reindex (primitiveFamilies (operators prior accepted proof other)) second assignment) first =
    instanceArguments prior accepted proof other assignment (first.compose second) := by
  exact TypeDefinitionModels.instanceArguments_composition
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (first := first)
    (second := second)

theorem abstractionInstance_composition (assignment : Assignment.{w}) (first second : TypeSubst) :
    HEq (abstractionInstance prior accepted proof other
      (reindex (primitiveFamilies (operators prior accepted proof other)) second assignment) first)
      (abstractionInstance prior accepted proof other assignment (first.compose second)) := by
  exact TypeDefinitionModels.abstractionInstance_composition
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (first := first)
    (second := second)

theorem representationInstance_composition (assignment : Assignment.{w}) (first second : TypeSubst) :
    HEq (representationInstance prior accepted proof other
      (reindex (primitiveFamilies (operators prior accepted proof other)) second assignment) first)
      (representationInstance prior accepted proof other assignment (first.compose second)) := by
  exact TypeDefinitionModels.representationInstance_composition
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (first := first)
    (second := second)

theorem abstraction_meaning_of_annotation (assignment : Assignment.{w}) (substitution : TypeSubst)
    {annotation : Ty} (same : annotation = abstractionAnnotation (request := request) (result := result) substitution)
    {type : HOL.Ty AtomicTy} (typed : annotation.toHOL = type) :
    HEq ((model prior accepted proof other assignment).constDen
      (.constant result.output.abstractionConstant annotation typed))
      (abstraction prior accepted proof other (instanceAssignment prior accepted proof other assignment substitution)) := by
  exact TypeDefinitionModels.abstraction_meaning_of_annotation
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (substitution := substitution)
    (annotation := annotation)
    (same := same)
    (type := type)
    (typed := typed)

theorem representation_meaning_of_annotation (assignment : Assignment.{w}) (substitution : TypeSubst)
    {annotation : Ty} (same : annotation = representationAnnotation (request := request) (result := result) substitution)
    {type : HOL.Ty AtomicTy} (typed : annotation.toHOL = type) :
    HEq ((model prior accepted proof other assignment).constDen
      (.constant result.output.representationConstant annotation typed))
      (representation prior accepted proof other (instanceAssignment prior accepted proof other assignment substitution)) := by
  exact TypeDefinitionModels.representation_meaning_of_annotation
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (substitution := substitution)
    (annotation := annotation)
    (same := same)
    (type := type)
    (typed := typed)

theorem abstraction_symbol_composition (assignment : Assignment.{w}) (first second : TypeSubst)
    {type : HOL.Ty AtomicTy}
    (typed : (abstractionAnnotation (request := request) (result := result) first).toHOL = type) :
    HEq ((model prior accepted proof other
      (reindex (primitiveFamilies (operators prior accepted proof other)) second assignment)).constDen
      (.constant result.output.abstractionConstant (abstractionAnnotation (request := request) (result := result) first) typed))
      ((model prior accepted proof other assignment).constDen
        (second.symbolInstance (.constant result.output.abstractionConstant
          (abstractionAnnotation (request := request) (result := result) first) typed))) := by
  exact TypeDefinitionModels.abstraction_symbol_composition
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (first := first)
    (second := second)
    (type := type)
    (typed := typed)

theorem representation_symbol_composition (assignment : Assignment.{w}) (first second : TypeSubst)
    {type : HOL.Ty AtomicTy}
    (typed : (representationAnnotation (request := request) (result := result) first).toHOL = type) :
    HEq ((model prior accepted proof other
      (reindex (primitiveFamilies (operators prior accepted proof other)) second assignment)).constDen
      (.constant result.output.representationConstant (representationAnnotation (request := request) (result := result) first) typed))
      ((model prior accepted proof other assignment).constDen
        (second.symbolInstance (.constant result.output.representationConstant
          (representationAnnotation (request := request) (result := result) first) typed))) := by
  exact TypeDefinitionModels.representation_symbol_composition
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (first := first)
    (second := second)
    (type := type)
    (typed := typed)

theorem carrierModel_instance_agreement_withTypes (later : Signature)
    (types : ∀ operator arity, result.context.signature.typeOperators operator = some arity →
      later.typeOperators operator = some arity) (substitution : TypeSubst) :
    SourceAgreement (withTypes context.signature later)
      (carrierModel prior accepted proof other
        (reindex (primitiveFamilies (operators prior accepted proof other)) substitution assignment))
      (reindexedModel substitution (carrierModel prior accepted proof other assignment)) := by
  exact TypeDefinitionModels.carrierModel_instance_agreement_withTypes
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (later := later)
    (types := types)
    (substitution := substitution)

theorem model_reindex_carrier (substitution : TypeSubst) :
    (model prior accepted proof other
      (reindex (primitiveFamilies (operators prior accepted proof other)) substitution assignment)).Carrier =
    (reindexedModel substitution (model prior accepted proof other assignment)).Carrier := by
  exact TypeDefinitionModels.model_reindex_carrier
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (substitution := substitution)

theorem model_instance_agreement_withTypes (later : Signature)
    (types : ∀ operator arity, result.context.signature.typeOperators operator = some arity →
      later.typeOperators operator = some arity)
    (substitution : TypeSubst) :
    SourceAgreement (ConstantHistoryExpandedTypes.withTypes result.context.signature later)
      (model prior accepted proof other
        (reindex (primitiveFamilies (operators prior accepted proof other)) substitution assignment))
      (reindexedModel substitution (model prior accepted proof other assignment)) := by
  exact TypeDefinitionModels.model_instance_agreement_withTypes
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (later := later)
    (types := types)
    (substitution := substitution)

theorem model_instance_agreement (substitution : TypeSubst) :
    SourceAgreement result.context.signature
      (model prior accepted proof other
        (reindex (primitiveFamilies (operators prior accepted proof other)) substitution assignment))
      (reindexedModel substitution (model prior accepted proof other assignment)) := by
  exact TypeDefinitionModels.model_instance_agreement
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (substitution := substitution)

theorem model_models_instance (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (substitution : TypeSubst) {term : DBTerm} {formula : HOL.ClosedFormula Symbol}
    (translation : TranslatesCompositionally [] term .prop formula)
    (formed : AnnotationsFormed result.context.signature term) :
    (model prior accepted proof other
      (reindex (primitiveFamilies (operators prior accepted proof other)) substitution assignment)).models formula ↔
      (model prior accepted proof other assignment).models
        (HOL.mapTypes substitution.baseInstance substitution.symbolInstance formula) := by
  exact TypeDefinitionModels.model_models_instance
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (functionArity := functionArity)
    (substitution := substitution)
    (term := term)
    (formula := formula)
    (translation := translation)
    (formed := formed)

theorem models_source_instance (primitives : Primitives initial)
    {term : DBTerm} {original instantiated : HOL.ClosedFormula Symbol}
    (translation : TranslatesCompositionally [] term .prop original)
    (formed : AnnotationsFormed result.context.signature term)
    (holds : ∀ changedAssignment, (model prior accepted proof other changedAssignment).models original)
    (substitution : TypeSubst)
    (instantiatedTranslation : TranslatesCompositionally [] ((TermSubst.mk substitution []).applyDB term) .prop instantiated) :
    (model prior accepted proof other assignment).models instantiated := by
  exact TypeDefinitionModels.models_source_instance
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (primitives := primitives)
    (term := term)
    (original := original)
    (instantiated := instantiated)
    (translation := translation)
    (formed := formed)
    (holds := holds)
    (substitution := substitution)
    (instantiatedTranslation := instantiatedTranslation)

theorem models_preceding_equations (primitives : Primitives initial) :
    ∀ formula ∈ equationTheory records, (model prior accepted proof other assignment).models formula := by
  rintro formula ⟨recorded, member, substitution, translated⟩
  obtain ⟨original, originalTranslation⟩ := history.record_translation member TypeSubst.empty
  have originalTranslated := originalTranslation.of_term_eq (TermSubst.typeInstance_identity _)
  have formed := history.record_formed primitives.functionArity primitives.equalityParameter
    primitives.equalityRegistered member
  apply models_source_instance prior accepted proof other assignment primitives originalTranslated
    (formed.mono (admitSourceTypeInTheory_result accepted).1) _ substitution translated
  intro changedAssignment
  apply (model_models_old prior accepted proof other changedAssignment primitives.functionArity
    originalTranslated formed).mpr
  exact prior.equations other changedAssignment original ⟨recorded, member, TypeSubst.empty, originalTranslation⟩

theorem model_original_predicate_heq (primitives : Primitives initial) :
    HEq ((model prior accepted proof other assignment).denote
      (TypeAdmission.admittedImage accepted).predicateTerm (fun index => nomatch index))
      ((prior.model other (instanceAssignment prior accepted proof other assignment TypeSubst.empty)).denote
        (TypeAdmission.admittedImage accepted).predicateTerm (fun index => nomatch index)) := by
  exact TypeDefinitionModels.model_original_predicate_heq
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (primitives := primitives)

theorem model_original_predicate_law (primitives : Primitives initial)
    (value : HOL.Ty.denote.{0, w + 1} (model prior accepted proof other assignment).Carrier result.core.witness.ty.toHOL) :
    (((model prior accepted proof other assignment).denote
      (TypeAdmission.admittedImage accepted).predicateTerm (fun index => nomatch index)) value).down ↔
      (model prior accepted proof other assignment).constDen
          (.constant result.output.representationConstant
            (representationAnnotation (request := request) (result := result) TypeSubst.empty)
            (show (representationAnnotation (request := request) (result := result) TypeSubst.empty).toHOL =
              HOL.Ty.arr (SourceTypeDefinitionTransport.sourceCarrierType request TypeSubst.empty).toHOL result.core.witness.ty.toHOL from by
                simpa only [representationAnnotation, TypeSubst.apply_empty] using
                  Ty.toHOL_function (SourceTypeDefinitionTransport.sourceCarrierType request TypeSubst.empty) result.core.witness.ty))
        ((model prior accepted proof other assignment).constDen
          (.constant result.output.abstractionConstant
            (abstractionAnnotation (request := request) (result := result) TypeSubst.empty)
            (show (abstractionAnnotation (request := request) (result := result) TypeSubst.empty).toHOL =
              HOL.Ty.arr result.core.witness.ty.toHOL (SourceTypeDefinitionTransport.sourceCarrierType request TypeSubst.empty).toHOL from by
                simpa only [abstractionAnnotation, TypeSubst.apply_empty] using
                  Ty.toHOL_function result.core.witness.ty (SourceTypeDefinitionTransport.sourceCarrierType request TypeSubst.empty))) value) = value := by
  exact TypeDefinitionModels.model_original_predicate_law
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (primitives := primitives)
    (value := value)

theorem model_comparison_agreement :
    SourceAgreement (comparisonSignature (context := context) (result := result))
      (model prior accepted proof other assignment) (carrierModel prior accepted proof other assignment):= by
  exact TypeDefinitionModels.model_comparison_agreement
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)

theorem model_instance_predicate_same (substitution : TypeSubst)
    (formedCarrier : TypeFormed result.context.signature
      (SourceTypeDefinitionTransport.sourceCarrierType request substitution)) :
    (model prior accepted proof other assignment).denote
      (SourceTypeDefinitionTransport.instanceImage accepted substitution).predicateTerm (fun v => nomatch v) =
    (carrierModel prior accepted proof other assignment).denote
      (SourceTypeDefinitionTransport.instanceImage accepted substitution).predicateTerm (fun v => nomatch v) := by
  exact TypeDefinitionModels.model_instance_predicate_same
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (substitution := substitution)
    (formedCarrier := formedCarrier)

theorem carrierModel_instance_predicate_heq
    (primitives : Primitives initial)
    (substitution : TypeSubst) :
    HEq ((carrierModel prior accepted proof other assignment).denote
      (SourceTypeDefinitionTransport.instanceImage accepted substitution).predicateTerm (fun v => nomatch v))
      ((prior.model other (instanceAssignment prior accepted proof other assignment substitution)).denote
        (TypeAdmission.admittedImage accepted).predicateTerm (fun v => nomatch v)) := by
  exact TypeDefinitionModels.carrierModel_instance_predicate_heq
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (primitives := primitives)
    (substitution := substitution)

theorem model_instance_predicate (primitives : Primitives initial) (substitution : TypeSubst)
    (formedCarrier : TypeFormed result.context.signature
      (SourceTypeDefinitionTransport.sourceCarrierType request substitution))
    (value : HOL.Ty.denote.{0, w + 1} (model prior accepted proof other assignment).Carrier
      (substitution.apply result.core.witness.ty).toHOL) :
    (((model prior accepted proof other assignment).denote
      (SourceTypeDefinitionTransport.instanceImage accepted substitution).predicateTerm (fun v => nomatch v)) value).down =
    TypeAdmission.representedPredicate (TypeAdmission.admittedImage accepted)
      (prior.model other (instanceAssignment prior accepted proof other assignment substitution))
      (cast (represented_carrier prior accepted proof other assignment substitution) value) := by
  exact TypeDefinitionModels.model_instance_predicate
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (primitives := primitives)
    (substitution := substitution)
    (formedCarrier := formedCarrier)
    (value := value)

theorem model_predicate_iff_representation_abstraction (primitives : Primitives initial) (substitution : TypeSubst)
    (formedCarrier : TypeFormed result.context.signature
      (SourceTypeDefinitionTransport.sourceCarrierType request substitution))
    (value : HOL.Ty.denote.{0, w + 1} (model prior accepted proof other assignment).Carrier
      (substitution.apply result.core.witness.ty).toHOL) :
    (((model prior accepted proof other assignment).denote
      (SourceTypeDefinitionTransport.instanceImage accepted substitution).predicateTerm (fun v => nomatch v)) value).down ↔
      (model prior accepted proof other assignment).constDen
          (.constant result.output.representationConstant
            (representationAnnotation (request := request) (result := result) substitution) (Ty.toHOL_function _ _))
        ((model prior accepted proof other assignment).constDen
          (.constant result.output.abstractionConstant
            (abstractionAnnotation (request := request) (result := result) substitution) (Ty.toHOL_function _ _)) value) = value := by
  exact TypeDefinitionModels.model_predicate_iff_representation_abstraction
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (primitives := primitives)
    (substitution := substitution)
    (formedCarrier := formedCarrier)
    (value := value)

theorem model_models_abstractionRepresentation (substitution : TypeSubst) :
    (model prior accepted proof other assignment).models
      (SourceTypeDefinitionTransport.abstractionRepresentationFormula (request := request) (result := result) substitution) := by
  exact TypeDefinitionModels.model_models_abstractionRepresentation
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (substitution := substitution)

theorem model_models_representationAbstraction (primitives : Primitives initial) (substitution : TypeSubst)
    (formedCarrier : TypeFormed result.context.signature
      (SourceTypeDefinitionTransport.sourceCarrierType request substitution)) :
    (model prior accepted proof other assignment).models
      (SourceTypeDefinitionTransport.representationAbstractionFormula accepted substitution) := by
  exact TypeDefinitionModels.model_models_representationAbstraction
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (primitives := primitives)
    (substitution := substitution)
    (formedCarrier := formedCarrier)

theorem type_equation_instances (primitives : Primitives initial) (substitution : TypeSubst)
    {first second : HOL.ClosedFormula Symbol}
    (firstTranslation : TranslatesCompositionally []
      ((TermSubst.mk substitution []).applyDB result.output.abstractionRepresentationTheorem.sequent.concl.term) .prop first)
    (secondTranslation : TranslatesCompositionally []
      ((TermSubst.mk substitution []).applyDB result.output.representationAbstractionTheorem.sequent.concl.term) .prop second) :
    (model prior accepted proof other assignment).models first ∧
      (model prior accepted proof other assignment).models second := by
  exact TypeDefinitionModels.type_equation_instances
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (proof := proof)
    (other := other)
    (assignment := assignment)
    (primitives := primitives)
    (substitution := substitution)
    (first := first)
    (second := second)
    (firstTranslation := firstTranslation)
    (secondTranslation := secondTranslation)

theorem models_equationTheory (primitives : Primitives initial) :
    ∀ formula ∈ equationTheory (records ++
      [result.output.abstractionRepresentationTheorem, result.output.representationAbstractionTheorem]),
      (model prior accepted proof other assignment).models formula := by
  rintro formula ⟨recorded, member, substitution, translated⟩
  rcases List.mem_append.mp member with earlier | added
  · exact models_preceding_equations prior accepted proof other assignment primitives formula
      ⟨recorded, earlier, substitution, translated⟩
  · have holds := type_equation_instances prior accepted proof other assignment primitives substitution
      (SourceTypeDefinitionTransport.abstractionRepresentation_translated accepted substitution)
      (SourceTypeDefinitionTransport.representationAbstraction_translated accepted substitution)
    rcases List.mem_cons.mp added with same | added
    · subst recorded
      rw [← (SourceTypeDefinitionTransport.abstractionRepresentation_translated accepted substitution).unique_eq translated]
      exact holds.1
    · have same := List.mem_singleton.mp added
      subst recorded
      rw [← (SourceTypeDefinitionTransport.representationAbstraction_translated accepted substitution).unique_eq translated]
      exact holds.2

namespace Controls

open MixedDefinitionHistory.Controls MixedDefinitionModelFamily.Controls

/-- The genuinely second source type installs its exact original symbols
in one model after a first type and dependent constant. -/
noncomputable def secondModel (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol :=
  model afterFirstConstruction second_result_admitted
    (History.existence_proof_of_kernel_derives second_result_admitted _ second_existence_derived) other assignment

theorem second_all_retained_equations (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ∀ formula ∈ equationTheory
      (((DefinitionHistoryModels.Controls.polymorphicDefinitions.records.map
        (fun result => result.output.definitionTheorem) ++
        [UniformTypeDefinitionFamily.Controls.polymorphicResult.output.abstractionRepresentationTheorem,
         UniformTypeDefinitionFamily.Controls.polymorphicResult.output.representationAbstractionTheorem]) ++
        [afterTypeResult.output.definitionTheorem]) ++
        [secondResult.output.abstractionRepresentationTheorem, secondResult.output.representationAbstractionTheorem]),
      (secondModel other assignment).models formula :=
  models_equationTheory afterFirstConstruction second_result_admitted
    (History.existence_proof_of_kernel_derives second_result_admitted _ second_existence_derived) other assignment primitives

theorem second_instance_coherence (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (substitution : TypeSubst) :
    SourceAgreement secondResult.context.signature
      (secondModel other
        (reindex (primitiveFamilies (operators afterFirstConstruction second_result_admitted
          (History.existence_proof_of_kernel_derives second_result_admitted _ second_existence_derived) other)) substitution assignment))
      (reindexedModel substitution (secondModel other assignment)) :=
  model_instance_agreement afterFirstConstruction second_result_admitted
    (History.existence_proof_of_kernel_derives second_result_admitted _ second_existence_derived) other assignment substitution

/-- A malformed raw annotation is not admitted merely because its identity
matches the new abstraction symbol. -/
theorem second_malformed_abstraction_refused :
    ¬ ConstantInstance secondResult.context.signature secondResult.output.abstractionConstant
      (.var (Name.global "MalformedAnnotation")) := by
  intro declared
  obtain ⟨substitution, same⟩ := licensed_abstraction_instance second_result_admitted declared
  have impossible := congrArg Ty.destFunction? same
  simp only [abstractionAnnotation, Ty.destFunction?_function] at impossible
  cases impossible

end Controls

end Mettapedia.Languages.HOLLight.MixedTypeDefinitionModels
