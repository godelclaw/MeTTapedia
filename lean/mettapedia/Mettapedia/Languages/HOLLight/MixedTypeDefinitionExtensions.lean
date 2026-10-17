import Mettapedia.Languages.HOLLight.MixedTypeDefinitionModels
import Mettapedia.Languages.HOLLight.TypeDefinitionExtensions

/-!
# Fresh ambient operators after actual mixed witnessed definitions

The installed source interpretation retains every original licensed carrier
and symbol after a later fresh ambient family. These laws close the semantic
construction state needed by the original chronological mixed recurrence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MixedTypeDefinitionExtensions

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics ModelInterpretation SignatureFormation ModelInstanceCoherence
open DefinitionAdapters MixedDefinitionHistory MixedDefinitionModelFamily
open MixedDefinitionModelFamily.Witnessed MixedTypeDefinitionModels
open UniformTypeDefinitionModels (abstractionAnnotation representationAnnotation comparisonSignature)
open UniformTypeDefinitionFamily (inhabitedSubtype inhabitedSubtype_congr)
open UniformTypeDefinitionExtensions (predecessor_fresh operators_distinct)

universe w

variable {initial context : TheoryContext} {records : List Theorem}
  {history : History initial context records} (prior : Construction.{w} history)
  {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
  (accepted : admitSourceTypeInTheory context instances request = some result)
  (proof : HOL.ClosedTheorySet.Provable (equationTheory records) (TypeAdmission.admittedImage accepted).formula)
  (other : OperatorFamilies.{w}) (operator : TypeOp) (replacement : List Domain.{w} → Domain.{w})
  (notBool : operator ≠ TypeOp.bool) (notFunction : operator ≠ TypeOp.function)
  (fresh : result.context.signature.typeOperators operator = none)

include accepted notBool notFunction fresh in
theorem representedCarrier_extend (assignment : Assignment.{w}) :
    HOL.Ty.denote.{0, w + 1}
      (prior.model (extend other operator replacement) assignment).Carrier result.core.witness.ty.toHOL =
      HOL.Ty.denote.{0, w + 1} (prior.model other assignment).Carrier result.core.witness.ty.toHOL := by
  exact TypeDefinitionExtensions.representedCarrier_extend
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (other := other)
    (operator := operator)
    (replacement := replacement)
    (notBool := notBool)
    (notFunction := notFunction)
    (fresh := fresh)
    (assignment := assignment)

include accepted notBool notFunction fresh in
theorem representedPredicate_extend
    (primitives : Primitives initial)
    (assignment : Assignment.{w}) :
    HEq (TypeAdmission.representedPredicate (TypeAdmission.admittedImage accepted)
      (prior.model (extend other operator replacement) assignment))
      (TypeAdmission.representedPredicate (TypeAdmission.admittedImage accepted)
        (prior.model other assignment)) := by
  exact TypeDefinitionExtensions.representedPredicate_extend
    (initial := initial)
    (context := context)
    (theory := equationTheory records)
    (prior := prior.toFamily)
    (instances := instances)
    (request := request)
    (result := result)
    (accepted := accepted)
    (other := other)
    (operator := operator)
    (replacement := replacement)
    (notBool := notBool)
    (notFunction := notFunction)
    (fresh := fresh)
    (primitives := primitives)
    (assignment := assignment)

include accepted notBool notFunction fresh in
theorem predicateDomain_extend
    (primitives : Primitives initial)
    (assignment : Assignment.{w}) :
    predicateDomain prior accepted proof (extend other operator replacement) assignment =
      predicateDomain prior accepted proof other assignment := by
  exact TypeDefinitionExtensions.predicateDomain_extend
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
    (operator := operator)
    (replacement := replacement)
    (notBool := notBool)
    (notFunction := notFunction)
    (fresh := fresh)
    (primitives := primitives)
    (assignment := assignment)

include accepted notBool notFunction fresh in
theorem abstraction_extend
    (primitives : Primitives initial)
    (assignment : Assignment.{w}) :
    HEq (abstraction prior accepted proof (extend other operator replacement) assignment)
      (abstraction prior accepted proof other assignment) := by
  exact TypeDefinitionExtensions.abstraction_extend
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
    (operator := operator)
    (replacement := replacement)
    (notBool := notBool)
    (notFunction := notFunction)
    (fresh := fresh)
    (primitives := primitives)
    (assignment := assignment)

include accepted notBool notFunction fresh in
theorem representation_extend
    (primitives : Primitives initial)
    (assignment : Assignment.{w}) :
    HEq (representation prior accepted proof (extend other operator replacement) assignment)
      (representation prior accepted proof other assignment) := by
  exact TypeDefinitionExtensions.representation_extend
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
    (operator := operator)
    (replacement := replacement)
    (notBool := notBool)
    (notFunction := notFunction)
    (fresh := fresh)
    (primitives := primitives)
    (assignment := assignment)

include accepted notBool notFunction fresh in
theorem operators_extend (primitives : Primitives initial) :
    operators prior accepted proof (extend other operator replacement) =
      extend (operators prior accepted proof other) operator replacement := by
  exact TypeDefinitionExtensions.operators_extend
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
    (operator := operator)
    (replacement := replacement)
    (notBool := notBool)
    (notFunction := notFunction)
    (fresh := fresh)
    (primitives := primitives)

include accepted notBool notFunction fresh in
theorem instanceArguments_extend
    (primitives : Primitives initial)
    (assignment : Assignment.{w}) (substitution : TypeSubst)
    (formedCarrier : TypeFormed result.context.signature
      (SourceTypeDefinitionTransport.sourceCarrierType request substitution)) :
    instanceArguments prior accepted proof (extend other operator replacement) assignment substitution =
      instanceArguments prior accepted proof other assignment substitution := by
  exact TypeDefinitionExtensions.instanceArguments_extend
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
    (operator := operator)
    (replacement := replacement)
    (notBool := notBool)
    (notFunction := notFunction)
    (fresh := fresh)
    (primitives := primitives)
    (assignment := assignment)
    (substitution := substitution)
    (formedCarrier := formedCarrier)

include accepted notBool notFunction fresh in
theorem abstractionInstance_extend
    (primitives : Primitives initial)
    (assignment : Assignment.{w}) (substitution : TypeSubst)
    (publicFormed : TypeFormed result.context.signature
      (abstractionAnnotation (request := request) (result := result) substitution)) :
    HEq (abstractionInstance prior accepted proof (extend other operator replacement) assignment substitution)
      (abstractionInstance prior accepted proof other assignment substitution) := by
  exact TypeDefinitionExtensions.abstractionInstance_extend
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
    (operator := operator)
    (replacement := replacement)
    (notBool := notBool)
    (notFunction := notFunction)
    (fresh := fresh)
    (primitives := primitives)
    (assignment := assignment)
    (substitution := substitution)
    (publicFormed := publicFormed)

include accepted notBool notFunction fresh in
theorem representationInstance_extend
    (primitives : Primitives initial)
    (assignment : Assignment.{w}) (substitution : TypeSubst)
    (publicFormed : TypeFormed result.context.signature
      (representationAnnotation (request := request) (result := result) substitution)) :
    HEq (representationInstance prior accepted proof (extend other operator replacement) assignment substitution)
      (representationInstance prior accepted proof other assignment substitution) := by
  exact TypeDefinitionExtensions.representationInstance_extend
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
    (operator := operator)
    (replacement := replacement)
    (notBool := notBool)
    (notFunction := notFunction)
    (fresh := fresh)
    (primitives := primitives)
    (assignment := assignment)
    (substitution := substitution)
    (publicFormed := publicFormed)

include accepted notBool notFunction fresh in
theorem carrierModel_extend_agreement (primitives : Primitives initial) (assignment : Assignment.{w}) :
    SourceAgreement (comparisonSignature (context := context) (result := result))
      (carrierModel prior accepted proof (extend other operator replacement) assignment)
      (carrierModel prior accepted proof other assignment) := by
  exact TypeDefinitionExtensions.carrierModel_extend_agreement
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
    (operator := operator)
    (replacement := replacement)
    (notBool := notBool)
    (notFunction := notFunction)
    (fresh := fresh)
    (primitives := primitives)
    (assignment := assignment)

include accepted notBool notFunction fresh in
theorem model_extend_agreement
    (primitives : Primitives initial)
    (assignment : Assignment.{w}) :
    SourceAgreement result.context.signature
      (model prior accepted proof (extend other operator replacement) assignment)
      (model prior accepted proof other assignment) := by
  exact TypeDefinitionExtensions.model_extend_agreement
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
    (operator := operator)
    (replacement := replacement)
    (notBool := notBool)
    (notFunction := notFunction)
    (fresh := fresh)
    (primitives := primitives)
    (assignment := assignment)

namespace Controls

open MixedDefinitionHistory.Controls MixedDefinitionModelFamily.Controls

/-- The second installed type, including older symbols at its new carrier,
retains all source meanings after an actual fresh later operator family. -/
theorem second_fresh_meanings (other : OperatorFamilies.{w})
    (replacement : List Domain.{w} → Domain.{w}) (assignment : Assignment.{w}) :
    SourceAgreement secondResult.context.signature
      (MixedTypeDefinitionModels.Controls.secondModel (extend other laterOperator replacement) assignment)
      (MixedTypeDefinitionModels.Controls.secondModel other assignment) :=
  model_extend_agreement afterFirstConstruction second_result_admitted
    (History.existence_proof_of_kernel_derives second_result_admitted _ second_existence_derived)
    other laterOperator replacement later_nonprimitive.1 later_nonprimitive.2 later_fresh primitives assignment

theorem second_fresh_operator_table (other : OperatorFamilies.{w})
    (replacement : List Domain.{w} → Domain.{w}) :
    Witnessed.operators afterFirstConstruction second_result_admitted
      (History.existence_proof_of_kernel_derives second_result_admitted _ second_existence_derived)
      (extend other laterOperator replacement) =
    extend (Witnessed.operators afterFirstConstruction second_result_admitted
      (History.existence_proof_of_kernel_derives second_result_admitted _ second_existence_derived) other)
      laterOperator replacement :=
  operators_extend afterFirstConstruction second_result_admitted
    (History.existence_proof_of_kernel_derives second_result_admitted _ second_existence_derived)
    other laterOperator replacement later_nonprimitive.1 later_nonprimitive.2 later_fresh primitives

/-- A registered second source operator cannot be claimed fresh by dropping
its original declaration row. -/
theorem second_declared_operator_not_fresh :
    secondResult.context.signature.typeOperators (SourceTypeDefinitionTransport.operator secondRequest) ≠ none := by
  have registered : secondResult.context.signature.typeOperators (SourceTypeDefinitionTransport.operator secondRequest) =
      some secondRequest.typeVariables.length := by
    rw [UniformTypeDefinitionInstances.source_signature second_result_admitted]
    simp [Signature.addConstant, Signature.addTypeOperator]
  rw [registered]
  intro impossible
  cases impossible

end Controls

end Mettapedia.Languages.HOLLight.MixedTypeDefinitionExtensions
