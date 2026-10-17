import Mettapedia.Languages.HOLLight.DefinitionSchemaClosure
import Mettapedia.Logic.HOL.PublishedFacts

/-!
# Source-licensed universal schema instance semantics

Agreement of the original source carriers and symbol values transports an
open body's universal closure, including semantic values without closed
source names. This extends instance coherence to the definition schemas.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.DefinitionSchemaInstances

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics ModelInterpretation SignatureFormation ModelInstanceCoherence
open DefinitionAdapters MixedDefinitionHistory MixedDefinitionModelFamily
open SourceTypeDefinitionTransport UniformTypeDefinitionModels DefinitionSchemaClosure

universe w

private theorem variable_member {context : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy}
    (index : HOL.Var context type) : type ∈ context := by
  induction index with
  | vz => exact List.mem_cons_self
  | vs _ ih => exact List.mem_cons_of_mem _ ih

/-- Original licensed source agreement preserves the meaning of universal
closure. The comparison constructs the other valuation from actual carrier
equalities; it does not assume semantic truth preservation. -/
theorem SourceAgreement.models_closeAll {signature : Signature}
    {first second : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol}
    (agreement : SourceAgreement signature first second)
    (functionArity : signature.typeOperators TypeOp.function = some 2)
    (firstFull : first.FullDomains) (secondFull : second.FullDomains)
    {context : HOL.Ctx AtomicTy} {term : DBTerm} {formula : HOL.Formula Symbol context}
    (translation : TranslatesCompositionally context term .prop formula)
    (formed : AnnotationsFormed signature term)
    (contextFormed : ContextFormed signature (context.map Ty.fromHOL)) :
    first.models (HOL.closeAll context formula) ↔ second.models (HOL.closeAll context formula) := by
  rw [HOL.models_closeAll_iff_of_fullDomains first firstFull,
    HOL.models_closeAll_iff_of_fullDomains second secondFull]
  have carrier {type : HOL.Ty AtomicTy} (index : HOL.Var context type) :=
    agreement.carriers type (contextFormed _ (List.mem_map.mpr ⟨type, variable_member index, rfl⟩))
  constructor
  · intro holds valuation
    let other : first.Valuation context := fun {_} index => cast (carrier index).symm (valuation index)
    have equal := agreement.denote functionArity firstFull secondFull translation formed contextFormed
      other valuation (fun _ index => cast_heq (carrier index).symm (valuation index))
    exact (congrArg (fun value : ULift.{w + 1, 0} Prop => value.down) (eq_of_heq equal)) ▸ holds other
  · intro holds valuation
    let other : second.Valuation context := fun {_} index => cast (carrier index) (valuation index)
    have equal := agreement.denote functionArity firstFull secondFull translation formed contextFormed
      valuation other (fun _ index => (cast_heq (carrier index) (valuation index)).symm)
    exact (congrArg (fun value : ULift.{w + 1, 0} Prop => value.down) (eq_of_heq equal)).symm ▸ holds other

/-- The constructed model of an arbitrary original mixed history transports
universal source schemas through each actual type substitution. Only the
original open body and its binder types need source formation. -/
theorem family_models_closeAll_instance {initial final : TheoryContext}
    {theory : HOL.ClosedTheorySet Symbol} (construction : DefinitionModelFamily.Family.{w} initial final theory)
    (primitives : Primitives initial) (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (substitution : TypeSubst) {context : HOL.Ctx AtomicTy} {term : DBTerm}
    {formula : HOL.Formula Symbol context}
    (translation : TranslatesCompositionally context term .prop formula)
    (formed : AnnotationsFormed final.signature term)
    (contextFormed : ContextFormed final.signature (context.map Ty.fromHOL)) :
    (construction.model other (reindex (primitiveFamilies (construction.operators other)) substitution assignment)).models
      (HOL.closeAll context formula) ↔
    (construction.model other assignment).models
      (HOL.mapTypes substitution.baseInstance substitution.symbolInstance (HOL.closeAll context formula)) := by
  have agreement := construction.instances other final.signature (fun _ _ found => found) assignment substitution
  have equal : ConstantHistoryExpandedTypes.withTypes final.signature final.signature = final.signature := by
    cases final.signature
    rfl
  rw [equal] at agreement
  exact (SourceAgreement.models_closeAll agreement
    (construction.includes.1 _ _ primitives.functionArity)
    (construction.fullDomains other _) (reindexedModel_fullDomains _ _)
    translation formed contextFormed).trans
      (reindexedModel_models substitution _ (construction.fullDomains other assignment) _)

/-- The constructed model of an arbitrary original mixed history transports
universal source schemas through each actual type substitution. Only the
original open body and its binder types need source formation. -/
theorem models_closeAll_instance {initial final : TheoryContext} {records : List Theorem}
    {history : History initial final records} (construction : Construction.{w} history)
    (primitives : Primitives initial) (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (substitution : TypeSubst) {context : HOL.Ctx AtomicTy} {term : DBTerm}
    {formula : HOL.Formula Symbol context}
    (translation : TranslatesCompositionally context term .prop formula)
    (formed : AnnotationsFormed final.signature term)
    (contextFormed : ContextFormed final.signature (context.map Ty.fromHOL)) :
    (construction.model other (reindex (primitiveFamilies (construction.operators other)) substitution assignment)).models
      (HOL.closeAll context formula) ↔
    (construction.model other assignment).models
      (HOL.mapTypes substitution.baseInstance substitution.symbolInstance (HOL.closeAll context formula)) := by
  exact family_models_closeAll_instance construction.toFamily primitives other assignment substitution
    translation formed contextFormed

/-- Binding an original source variable preserves every annotation licence. -/
theorem AnnotationsFormed.closeFreeAt {signature : Signature} {term : DBTerm}
    (formed : AnnotationsFormed signature term) (sourceVar : SourceVar) (depth : Nat) :
    AnnotationsFormed signature (DBTerm.closeFreeAt sourceVar depth term) := by
  induction formed generalizing depth with
  | constant annotationFormed declared => simpa only [DBTerm.closeFreeAt] using (AnnotationsFormed.constant annotationFormed declared)
  | free annotationFormed =>
      simp only [DBTerm.closeFreeAt]
      split
      · exact .bound depth
      · exact .free annotationFormed
  | bound index => simpa only [DBTerm.closeFreeAt] using (AnnotationsFormed.bound (signature := signature) index)
  | app _ _ functionIH argumentIH => simpa only [DBTerm.closeFreeAt] using (AnnotationsFormed.app (functionIH depth) (argumentIH depth))
  | abs domainFormed _ bodyIH => simpa only [DBTerm.closeFreeAt] using (AnnotationsFormed.abs domainFormed (bodyIH (depth + 1)))

section TypeSchema

variable {initial context : TheoryContext} {records : List Theorem}
  {history : History initial context records} (prior : Construction.{w} history)
  {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest}
  {result : SourceTypeDefinitionResult}
  (accepted : admitSourceTypeInTheory context instances request = some result)
  (proof : HOL.ClosedTheorySet.Provable (equationTheory records)
    (TypeAdmission.admittedImage accepted).formula)
  (other : OperatorFamilies.{w}) (assignment : Assignment.{w})

private theorem abstractionRepresentation_abstracted (substitution : TypeSubst) :
    HOL.abstractConstAt (Γ := [])
      (Symbol.ofVar ⟨Name.global "a", sourceCarrierType request substitution⟩) []
      (abstractionRepresentationFormula (request := request) (result := result) substitution) =
    abstractionRepresentationBody (request := request) (result := result) substitution := by
  simp only [abstractionRepresentationFormula, HOL.ExtDerivation.abstractConstAt_app,
    abstractConstAt_equalityLambda, abstractConstAt_const_self]
  rw [HOL.abstractConstAt_noOccurrence [] (abstractionTerm (request := request) (result := result) substitution)
    (Symbol.noConstOccurrence_const _ _ (Symbol.sigma_constant_ne_ofVar _ _ _ _)),
    HOL.abstractConstAt_noOccurrence [] (representationTerm (request := request) (result := result) substitution)
    (Symbol.noConstOccurrence_const _ _ (Symbol.sigma_constant_ne_ofVar _ _ _ _))]
  rfl

include accepted in
/-- The universal body's source is exactly the original retained equation
with its original free value bound, rather than a replacement equation. -/
theorem abstractionRepresentation_body_translated (substitution : TypeSubst) :
    TranslatesCompositionally [(sourceCarrierType request substitution).toHOL]
      (DBTerm.closeFreeAt ⟨Name.global "a", sourceCarrierType request substitution⟩ 0
        ((TermSubst.mk substitution []).applyDB result.output.abstractionRepresentationTheorem.sequent.concl.term))
      .prop (abstractionRepresentationBody (request := request) (result := result) substitution) := by
  have translated := (abstractionRepresentation_translated accepted substitution).closeFreeAt
    ⟨Name.global "a", sourceCarrierType request substitution⟩ (Ξ := [])
  rw [abstractionRepresentation_abstracted] at translated
  exact translated

private theorem representationAbstraction_abstracted (substitution : TypeSubst) :
    HOL.abstractConstAt (Γ := [])
      (Symbol.ofVar ⟨Name.global "r", (instanceTerm substitution result.core.witness).ty⟩) []
      (representationAbstractionFormula accepted substitution) =
    representationAbstractionBody accepted substitution := by
  simp only [representationAbstractionFormula, HOL.ExtDerivation.abstractConstAt_app,
    abstractConstAt_equalityLambda, abstractConstAt_const_self]
  rw [HOL.abstractConstAt_noOccurrence [] (instanceImage accepted substitution).predicateTerm
    (predicate_variableFree accepted substitution _),
    HOL.abstractConstAt_noOccurrence [] (abstractionTerm (request := request) (result := result) substitution)
    (Symbol.noConstOccurrence_const _ _ (Symbol.sigma_constant_ne_ofVar _ _ _ _)),
    HOL.abstractConstAt_noOccurrence [] (representationTerm (request := request) (result := result) substitution)
    (Symbol.noConstOccurrence_const _ _ (Symbol.sigma_constant_ne_ofVar _ _ _ _))]
  rfl

/-- Binding the original second-row value yields exactly the displayed
universal body, including the admitted original predicate. -/
theorem representationAbstraction_body_translated (substitution : TypeSubst) :
    TranslatesCompositionally [(instanceTerm substitution result.core.witness).ty.toHOL]
      (DBTerm.closeFreeAt ⟨Name.global "r", (instanceTerm substitution result.core.witness).ty⟩ 0
        ((TermSubst.mk substitution []).applyDB result.output.representationAbstractionTheorem.sequent.concl.term))
      .prop (representationAbstractionBody accepted substitution) := by
  have translated := (representationAbstraction_translated accepted substitution).closeFreeAt
    ⟨Name.global "r", (instanceTerm substitution result.core.witness).ty⟩ (Ξ := [])
  rw [representationAbstraction_abstracted] at translated
  exact translated

include accepted in
private theorem carrier_original_formed : TypeFormed result.context.signature
    (sourceCarrierType request TypeSubst.empty) := by
  have registeredAnnotation := result.context.constantTypes _ _ (UniformTypeDefinitionInstances.new_constants_registered accepted).1
  simpa only [abstractionAnnotation, TypeSubst.apply_empty] using (registeredAnnotation.function_components _).2

/-- The first universally bound equation has truthful whole type images in
one installed model, for every original type substitution. -/
theorem models_typeMapped_abstractionSchema (primitives : Primitives initial)
    (substitution : TypeSubst) :
    (MixedTypeDefinitionModels.model prior accepted proof other assignment).models
      (HOL.mapTypes substitution.baseInstance substitution.symbolInstance
        (abstractionRepresentationSchema (request := request) (result := result) TypeSubst.empty)) := by
  let construction := Construction.typeDefinition primitives prior instances request result accepted proof
  have equations := type_equations_formed accepted
    (history.includes.1 _ _ primitives.functionArity) primitives.equalityParameter
    (history.includes.2 _ _ primitives.equalityRegistered)
  have annotations := AnnotationsFormed.closeFreeAt equations.1
    ⟨Name.global "a", sourceCarrierType request TypeSubst.empty⟩ 0
  have formed : AnnotationsFormed result.context.signature
      (DBTerm.closeFreeAt ⟨Name.global "a", sourceCarrierType request TypeSubst.empty⟩ 0
        ((TermSubst.mk TypeSubst.empty []).applyDB result.output.abstractionRepresentationTheorem.sequent.concl.term)) := by
    simpa only [TermSubst.typeInstance_identity] using annotations
  have contextFormed : ContextFormed result.context.signature
      ([(sourceCarrierType request TypeSubst.empty).toHOL].map Ty.fromHOL) := by
    simp only [List.map_cons, List.map_nil, Ty.fromHOL_toHOL]
    exact ContextFormed.cons _ (carrier_original_formed accepted) (ContextFormed.nil _)
  have compared := models_closeAll_instance construction primitives other assignment substitution
    (abstractionRepresentation_body_translated accepted TypeSubst.empty) formed contextFormed
  apply compared.mp
  exact models_abstractionRepresentation prior accepted proof other _ TypeSubst.empty

/-- Even when a replacement type is not registered, the actual type image
of the whole universal schema is true. Formation is required only at the
original source declaration, and is earned from its actual admission. -/
theorem models_typeMapped_representationSchema (primitives : Primitives initial)
    (substitution : TypeSubst) :
    (MixedTypeDefinitionModels.model prior accepted proof other assignment).models
      (HOL.mapTypes substitution.baseInstance substitution.symbolInstance
        (representationAbstractionSchema accepted TypeSubst.empty)) := by
  let construction := Construction.typeDefinition primitives prior instances request result accepted proof
  have equations := type_equations_formed accepted
    (history.includes.1 _ _ primitives.functionArity) primitives.equalityParameter
    (history.includes.2 _ _ primitives.equalityRegistered)
  have annotations := AnnotationsFormed.closeFreeAt equations.2
    ⟨Name.global "r", (instanceTerm TypeSubst.empty result.core.witness).ty⟩ 0
  have formed : AnnotationsFormed result.context.signature
      (DBTerm.closeFreeAt ⟨Name.global "r", (instanceTerm TypeSubst.empty result.core.witness).ty⟩ 0
        ((TermSubst.mk TypeSubst.empty []).applyDB result.output.representationAbstractionTheorem.sequent.concl.term)) := by
    simpa only [TermSubst.typeInstance_identity] using annotations
  have contextFormed : ContextFormed result.context.signature
      ([(instanceTerm TypeSubst.empty result.core.witness).ty.toHOL].map Ty.fromHOL) := by
    simp only [List.map_cons, List.map_nil, Ty.fromHOL_toHOL]
    apply ContextFormed.cons
    · simpa only [instanceTerm, TypeCorrectTermSubstitution.apply, TermSubst.applyChecked,
        TypeSubst.apply_empty] using
        (admitted_represented_formed accepted).mono (admitSourceTypeInTheory_result accepted).1
    · exact ContextFormed.nil _
  have compared := models_closeAll_instance construction primitives other assignment substitution
    (representationAbstraction_body_translated accepted TypeSubst.empty) formed contextFormed
  apply compared.mp
  exact models_representationAbstraction prior accepted proof other _ primitives TypeSubst.empty
    (carrier_original_formed accepted)

end TypeSchema

namespace Controls

open MixedDefinitionHistory.Controls MixedDefinitionModelFamily.Controls

/-- Both bound schemas remain true at arbitrary type images after the
original constant/type interleaving. -/
theorem second_type_images (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) (substitution : TypeSubst) :
    (MixedTypeDefinitionModels.Controls.secondModel other assignment).models
      (HOL.mapTypes substitution.baseInstance substitution.symbolInstance
        (abstractionRepresentationSchema (request := secondRequest) (result := secondResult) TypeSubst.empty)) ∧
    (MixedTypeDefinitionModels.Controls.secondModel other assignment).models
      (HOL.mapTypes substitution.baseInstance substitution.symbolInstance
        (representationAbstractionSchema second_result_admitted TypeSubst.empty)) :=
  ⟨models_typeMapped_abstractionSchema afterFirstConstruction second_result_admitted
    (History.existence_proof_of_kernel_derives second_result_admitted _ second_existence_derived)
    other assignment MixedDefinitionModelFamily.Controls.primitives substitution,
   models_typeMapped_representationSchema afterFirstConstruction second_result_admitted
    (History.existence_proof_of_kernel_derives second_result_admitted _ second_existence_derived)
    other assignment MixedDefinitionModelFamily.Controls.primitives substitution⟩

/-- Semantic type-image truth does not make a malformed source replacement
admissible to the original source signature. -/
theorem malformed_second_carrier_refused : typeFormedB secondResult.context.signature
    (sourceCarrierType secondRequest UniformTypeDefinitionModels.Controls.malformedInstance) = false := by
  decide +kernel

end Controls

end Mettapedia.Languages.HOLLight.DefinitionSchemaInstances
