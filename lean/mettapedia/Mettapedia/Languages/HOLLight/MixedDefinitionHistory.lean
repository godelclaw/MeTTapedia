import Mettapedia.Languages.HOLLight.UniformTypeDefinitionExtensions
import Mettapedia.Languages.HOLLight.DefinitionModelFamily
import Mettapedia.Languages.OpenTheory.PrimitiveEqualityFormation

/-!
# Original mixed definition chronology and preceding equation proofs

The state retains the original ordered theorem outputs. Every constant or
type step uses the original source admission gate. A type step additionally
carries a syntactic proof of its retained existence application over exactly
the previously introduced equations, before its own equations are appended.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MixedDefinitionHistory

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics ModelInterpretation SignatureFormation ModelInstanceCoherence
open DefinitionAdapters

universe w

/-- The original source equation instances, with their original translation.
The ordered record list is retained by History even though theory membership
is extensional. This does not replace any source proof checker. -/
def equationTheory (records : List Theorem) : HOL.ClosedTheorySet Symbol :=
  {formula | ∃ recorded ∈ records, ∃ substitution : TypeSubst,
    TranslatesCompositionally []
      ((TermSubst.mk substitution []).applyDB recorded.sequent.concl.term) .prop formula}

/-- The original chronological declaration receipts. A witnessed type
admission uses only the preceding syntactic theory; no model-truth field
or final-history conclusion is supplied. -/
inductive History (initial : TheoryContext) :
    (context : TheoryContext) → (records : List Theorem) → Type where
  | nil : History initial initial []
  | constant {prior : TheoryContext} {records : List Theorem}
      (history : History initial prior records)
      (instances : InstanceWitnesses) (name : Name) (source : SourceTerm)
      (result : ContextConstantDefinitionResult)
      (accepted : admitConstantInTheory prior instances name source = some result) :
      History initial result.context (records ++ [result.output.definitionTheorem])
  | typeDefinition {prior : TheoryContext} {records : List Theorem}
      (history : History initial prior records)
      (instances : InstanceWitnesses) (request : TypeOperatorDefinitionRequest)
      (result : SourceTypeDefinitionResult)
      (accepted : admitSourceTypeInTheory prior instances request = some result)
      (existence : HOL.ClosedTheorySet.Provable (equationTheory records)
        (TypeAdmission.admittedImage accepted).formula) :
      History initial result.context (records ++
        [result.output.abstractionRepresentationTheorem, result.output.representationAbstractionTheorem])

theorem equationTheory_nil : equationTheory [] = (∅ : HOL.ClosedTheorySet Symbol) := by
  ext formula
  simp [equationTheory]

theorem equationTheory_append (first second : List Theorem) :
    equationTheory (first ++ second) = equationTheory first ∪ equationTheory second := by
  ext formula
  constructor
  · rintro ⟨recorded, member, substitution, translated⟩
    rcases List.mem_append.mp member with firstMember | secondMember
    · exact Or.inl ⟨recorded, firstMember, substitution, translated⟩
    · exact Or.inr ⟨recorded, secondMember, substitution, translated⟩
  · rintro (⟨recorded, member, substitution, translated⟩ | ⟨recorded, member, substitution, translated⟩)
    · exact ⟨recorded, List.mem_append_left _ member, substitution, translated⟩
    · exact ⟨recorded, List.mem_append_right _ member, substitution, translated⟩

theorem equationTheory_prefix (first second : List Theorem) :
    equationTheory first ⊆ equationTheory (first ++ second) := by
  rw [equationTheory_append]
  exact Set.subset_union_left

/-- The actual retained primitive equality declaration earns the Boolean
carrier licence; it is not an extra axiom of the model construction. -/
theorem boolean_formed (context : TheoryContext) (parameter : Name)
    (registered : context.signature.constants Const.equality = some (Ty.equality (.var parameter))) :
    TypeFormed context.signature Ty.bool :=
  DefinitionModelFamily.boolean_formed context parameter registered

/-- The registered constant equation is a formed original source sentence. -/
theorem constant_equation_formed {context : TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context instances name source = some result)
    (functionArity : context.signature.typeOperators TypeOp.function = some 2)
    (parameter : Name)
    (equalityRegistered : context.signature.constants Const.equality = some (Ty.equality (.var parameter))) :
    AnnotationsFormed result.context.signature result.output.definitionTheorem.sequent.concl.term := by
  have included := (admitConstantInTheory_result accepted).2.2.1
  have registered := (admitConstantInTheory_result accepted).2.2.2.2.2.1
  have operandFormed := ((admitConstantInTheory_result accepted).2.1).mono included
  have constantFormed : AnnotationsFormed result.context.signature
      (.const result.output.constant result.definition.ty) :=
    .constant operandFormed ⟨result.definition.ty, TypeSubst.empty, registered, TypeSubst.apply_empty _⟩
  have bodyFormed := ((checkSource_sound _ _ (admitConstantInTheory_result accepted).1).2).mono included
  rw [(ConstantAdmission.source_equation accepted).2.2]
  exact PrimitiveEqualityFormation.equation_annotations _ parameter _
    (included.1 _ _ functionArity) ((boolean_formed context parameter equalityRegistered).mono included)
    operandFormed (included.2 _ _ equalityRegistered) _ _ constantFormed bodyFormed

/-- Both pointwise source equations retain the actual licensed symbols,
function/Boolean carriers and all annotations of the admitted predicate. -/
theorem type_equations_formed {context : TheoryContext} {instances : InstanceWitnesses}
    {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (functionArity : context.signature.typeOperators TypeOp.function = some 2)
    (parameter : Name)
    (equalityRegistered : context.signature.constants Const.equality = some (Ty.equality (.var parameter))) :
    AnnotationsFormed result.context.signature result.output.abstractionRepresentationTheorem.sequent.concl.term ∧
      AnnotationsFormed result.context.signature result.output.representationAbstractionTheorem.sequent.concl.term :=
  DefinitionModelFamily.type_equations_formed accepted functionArity parameter equalityRegistered

namespace History

variable {initial final : TheoryContext} {records : List Theorem}

theorem includes (history : History initial final records) :
    initial.signature.Includes final.signature := by
  induction history with
  | nil => exact Signature.Includes.refl _
  | constant prior instances name source result accepted ih =>
      exact ih.trans (admitConstantInTheory_result accepted).2.2.1
  | typeDefinition prior instances request result accepted existence ih =>
      exact ih.trans (admitSourceTypeInTheory_result accepted).1

/-- Every retained original row is formed in the actual current registry,
including rows introduced before later carrier-changing definitions. -/
theorem record_formed (history : History initial final records)
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (parameter : Name)
    (equalityRegistered : initial.signature.constants Const.equality = some (Ty.equality (.var parameter)))
    {recorded : Theorem} (member : recorded ∈ records) :
    AnnotationsFormed final.signature recorded.sequent.concl.term := by
  induction history with
  | nil => simp at member
  | constant prior instances name source result accepted ih =>
      rcases List.mem_append.mp member with earlier | added
      · exact (ih earlier).mono (admitConstantInTheory_result accepted).2.2.1
      · have same := List.mem_singleton.mp added
        subst recorded
        exact constant_equation_formed accepted (prior.includes.1 _ _ functionArity)
          parameter (prior.includes.2 _ _ equalityRegistered)
  | typeDefinition prior instances request result accepted existence ih =>
      rcases List.mem_append.mp member with earlier | added
      · exact (ih earlier).mono (admitSourceTypeInTheory_result accepted).1
      · have formed := type_equations_formed accepted (prior.includes.1 _ _ functionArity)
          parameter (prior.includes.2 _ _ equalityRegistered)
        rcases List.mem_cons.mp added with same | added
        · subst recorded; exact formed.1
        · have same := List.mem_singleton.mp added
          subst recorded; exact formed.2

/-- Every stored source equation has a genuine compositional translation
at every type instance. Theory membership is consequently nonvacuous. -/
theorem record_translation (history : History initial final records)
    {recorded : Theorem} (member : recorded ∈ records) (substitution : TypeSubst) :
    ∃ formula : HOL.ClosedFormula Symbol, TranslatesCompositionally []
      ((TermSubst.mk substitution []).applyDB recorded.sequent.concl.term) .prop formula := by
  induction history with
  | nil => simp at member
  | constant prior instances name source result accepted ih =>
      rcases List.mem_append.mp member with earlier | added
      · exact ih earlier
      · have same := List.mem_singleton.mp added
        subst recorded
        have boolean : ((TypeCorrectTermSubstitution.ofTypes substitution).apply
            result.output.definitionTheorem.sequent.concl).IsBool := by
          change substitution.apply result.output.definitionTheorem.sequent.concl.ty = Ty.bool
          rw [show result.output.definitionTheorem.sequent.concl.ty = Ty.bool from
            (ConstantAdmission.source_equation accepted).2.resultIsBool, TypeSubst.apply_bool]
        exact CanonicalTerm.exists_formula boolean
  | typeDefinition prior instances request result accepted existence ih =>
      rcases List.mem_append.mp member with earlier | added
      · exact ih earlier
      · rcases List.mem_cons.mp added with same | added
        · subst recorded
          exact ⟨_, SourceTypeDefinitionTransport.abstractionRepresentation_translated accepted substitution⟩
        · have same := List.mem_singleton.mp added
          subst recorded
          exact ⟨_, SourceTypeDefinitionTransport.representationAbstraction_translated accepted substitution⟩

/-- Earlier mixed-history equations survive a later original constant
extension at arbitrary type instances. This uses source identity omission,
so a later replacement annotation need not be registered in the old table. -/
theorem models_constant_extension (history : History initial final records)
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (parameter : Name)
    (equalityRegistered : initial.signature.constants Const.equality = some (Ty.equality (.var parameter)))
    {instances : InstanceWitnesses} {name : Name} {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory final instances name source = some result)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (sound : ∀ formula ∈ equationTheory records, M.models formula) :
    ∀ formula ∈ equationTheory (records ++ [result.output.definitionTheorem]),
      (ConstantAdmission.sourceExtension result M).models formula := by
  rintro formula ⟨recorded, member, substitution, translated⟩
  rcases List.mem_append.mp member with earlier | added
  · have omitted := ((history.record_formed functionArity parameter equalityRegistered earlier).omits_unregistered
      (ConstantAdmission.admitted_identity_fresh accepted)).typeInstance substitution
    have preserved : (ConstantAdmission.sourceExtension result M).models formula ↔ M.models formula := by
      rw [ConstantAdmission.sourceExtension_eq_reduct, ← M.models_substConst,
        ConstantAdmission.sourceExpansion_preserves_translation result translated omitted]
    exact preserved.mpr (sound formula ⟨recorded, earlier, substitution, translated⟩)
  · have same := List.mem_singleton.mp added
    subst recorded
    exact ConstantAdmission.sourceExtension_models_source_equation accepted M substitution translated

/-- Every original constant history embeds without changing its receipt,
body, record order or actual source equation. -/
noncomputable def ofConstants {final : TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final) :
    History initial final (history.records.map (fun result => result.output.definitionTheorem)) := by
  induction history with
  | nil => exact .nil
  | snoc prior instances name source result accepted ih =>
      simpa only [DefinitionHistoryModels.ConstantHistory.records, List.map_append, List.map_cons, List.map_nil]
        using History.constant ih instances name source result accepted

/-- The first type step uses exactly the equation theory already used by
the uniform constant-prefix construction. -/
theorem equationTheory_of_constants
    (history : DefinitionHistoryModels.ConstantHistory initial final) :
    equationTheory (history.records.map (fun result => result.output.definitionTheorem)) =
      UniformTypeDefinitionFamily.definitionTheory history := by
  ext formula
  constructor
  · rintro ⟨recorded, member, substitution, translated⟩
    obtain ⟨result, rowMember, recordEqual⟩ := List.mem_map.mp member
    exact ⟨result, rowMember, substitution, by simpa only [← recordEqual] using translated⟩
  · rintro ⟨result, member, substitution, translated⟩
    exact ⟨result.output.definitionTheorem, List.mem_map.mpr ⟨result, member, rfl⟩, substitution, translated⟩

/-- A genuine accepted original kernel graph supplies a first type step's
preceding-theory proof. Its actual existence theorem remains unchanged. -/
noncomputable def firstTypeOfChecked
    (history : DefinitionHistoryModels.ConstantHistory initial final)
    {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory final instances request = some result)
    {certificate : ProofSystem.Certificate}
    (checked : (ProofSystem.checker emptyAxiomPolicy).check request.existence certificate = true) :
    History initial result.context
      (history.records.map (fun result => result.output.definitionTheorem) ++
        [result.output.abstractionRepresentationTheorem, result.output.representationAbstractionTheorem]) :=
  .typeDefinition (ofConstants history) instances request result accepted
    (by rw [equationTheory_of_constants]
        exact UniformTypeDefinitionFamily.existence_proof_of_kernel_checked history accepted checked)

/-- Original kernel acceptance of a hypothesis-free existence request
supplies a syntactic proof over any preceding equation list. The existing
kernel-to-HOL bridge remains the proof authority. -/
theorem existence_proof_of_kernel_derives {context : TheoryContext}
    {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (records : List Theorem)
    (derived : Mettapedia.Logic.Derives (HOLLight.Rule emptyAxiomPolicy) request.existence) :
    HOL.ClosedTheorySet.Provable (equationTheory records) (TypeAdmission.admittedImage accepted).formula := by
  have proof := UniformTypeDefinitionFamily.existence_proof_of_kernel_derives
    (DefinitionHistoryModels.ConstantHistory.nil : DefinitionHistoryModels.ConstantHistory context context)
    accepted derived
  apply HOL.ClosedTheorySet.provable_mono _ proof
  rintro formula ⟨result, member, _, _⟩
  simp [DefinitionHistoryModels.ConstantHistory.records] at member

end History

namespace FirstType

open UniformTypeDefinitionFamily UniformTypeDefinitionModels

variable {initial context : TheoryContext}
  (history : DefinitionHistoryModels.ConstantHistory initial context)
  {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
  (accepted : admitSourceTypeInTheory context instances request = some result)
  (proof : HOL.ClosedTheorySet.Provable (definitionTheory history) (TypeAdmission.admittedImage accepted).formula)
  (other : OperatorFamilies.{w})
  (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
  (equalityParameter : Name)
  (equalityRegistered : initial.signature.constants Const.equality = some (Ty.equality (.var equalityParameter)))
  (selectionParameter : Name)
  (selectionDeclaration : initial.signature.constants selectionConstant = none ∨
    initial.signature.constants selectionConstant = some (selectionType (.var selectionParameter)))

include functionArity equalityParameter equalityRegistered selectionParameter selectionDeclaration in
/-- The original representation equation earns every actual type instance
by naturality of the constructed model. No formation assumption on the
substitution's new annotations is substituted for the original licence. -/
theorem representation_instances (assignment : Assignment.{w}) (substitution : TypeSubst)
    {formula : HOL.ClosedFormula Symbol}
    (translated : TranslatesCompositionally []
      ((TermSubst.mk substitution []).applyDB result.output.representationAbstractionTheorem.sequent.concl.term)
      .prop formula) :
    (model history accepted proof other assignment).models formula := by
  have originalTranslation := (SourceTypeDefinitionTransport.representationAbstraction_translated accepted TypeSubst.empty).of_term_eq
    (TermSubst.typeInstance_identity _)
  have formed := (type_equations_formed accepted (history.includes.1 _ _ functionArity)
    equalityParameter (history.includes.2 _ _ equalityRegistered)).2
  have natural := UniformTypeDefinitionInstances.model_models_instance history accepted proof other
    functionArity equalityParameter equalityRegistered selectionParameter selectionDeclaration
    assignment substitution originalTranslation formed
  have originalCarrier : TypeFormed result.context.signature
      (SourceTypeDefinitionTransport.sourceCarrierType request TypeSubst.empty) :=
    (result.context.constantTypes _ _ (UniformTypeDefinitionInstances.new_constants_registered accepted).1).function_components _ |>.2
  have holds := model_models_representationAbstraction history accepted proof other
    (reindex (primitiveFamilies (operators history accepted proof other)) substitution assignment)
    functionArity equalityParameter equalityRegistered selectionParameter selectionDeclaration
    TypeSubst.empty originalCarrier
  have typedInstance := ConstantHistoryInstanceCoherence.translation_type_instance result.context.signature equalityParameter
    ((admitSourceTypeInTheory_result accepted).1.2 _ _ (history.includes.2 _ _ equalityRegistered))
    substitution originalTranslation formed
  have same := typedInstance.unique_eq translated
  rw [← same]
  exact natural.mp holds

include functionArity equalityParameter equalityRegistered selectionParameter selectionDeclaration in
/-- All source instances of the actual two retained type equations are
true in the constructed model, including future/unregistered replacement
annotations. The original declaration licences, not their later recognition,
justify the instantiation. -/
theorem type_equation_instances (assignment : Assignment.{w}) (substitution : TypeSubst)
    {recorded : Theorem}
    (member : recorded ∈ [result.output.abstractionRepresentationTheorem, result.output.representationAbstractionTheorem])
    {formula : HOL.ClosedFormula Symbol}
    (translated : TranslatesCompositionally []
      ((TermSubst.mk substitution []).applyDB recorded.sequent.concl.term) .prop formula) :
    (model history accepted proof other assignment).models formula := by
  rcases List.mem_cons.mp member with same | member
  · subst recorded
    rw [← (SourceTypeDefinitionTransport.abstractionRepresentation_translated accepted substitution).unique_eq translated]
    exact model_models_abstractionRepresentation history accepted proof other assignment substitution
  · have same := List.mem_singleton.mp member
    subst recorded
    exact representation_instances history accepted proof other functionArity equalityParameter
      equalityRegistered selectionParameter selectionDeclaration assignment substitution translated

include functionArity equalityParameter equalityRegistered selectionParameter selectionDeclaration in
/-- Every preceding constant equation and both original type equations are
true at all source type instances in the actual installed uniform model. -/
theorem models_equationTheory (assignment : Assignment.{w}) :
    ∀ formula ∈ equationTheory
      (history.records.map (fun row => row.output.definitionTheorem) ++
        [result.output.abstractionRepresentationTheorem, result.output.representationAbstractionTheorem]),
      (model history accepted proof other assignment).models formula := by
  rintro formula ⟨recorded, member, substitution, translated⟩
  rcases List.mem_append.mp member with earlier | added
  · obtain ⟨row, rowMember, same⟩ := List.mem_map.mp earlier
    subst recorded
    let changed := reindex (primitiveFamilies (operators history accepted proof other)) substitution assignment
    obtain ⟨originalFormula, originalTranslation, originalHolds⟩ :=
      history.record_equation_meaning (initialModel other changed) rowMember TypeSubst.empty
    have originalTranslated := originalTranslation.of_term_eq (TermSubst.typeInstance_identity _)
    have originalFormed := (History.ofConstants history).record_formed functionArity equalityParameter
      equalityRegistered (List.mem_map.mpr ⟨row, rowMember, rfl⟩)
    have originalTruth := (model_models_old history accepted proof other changed functionArity
      originalTranslated originalFormed).mpr originalHolds
    have formed := originalFormed.mono (admitSourceTypeInTheory_result accepted).1
    have natural := UniformTypeDefinitionInstances.model_models_instance history accepted proof other
      functionArity equalityParameter equalityRegistered selectionParameter selectionDeclaration
      assignment substitution originalTranslated formed
    have typedInstance := ConstantHistoryInstanceCoherence.translation_type_instance result.context.signature equalityParameter
      ((admitSourceTypeInTheory_result accepted).1.2 _ _ (history.includes.2 _ _ equalityRegistered))
      substitution originalTranslated formed
    rw [← typedInstance.unique_eq translated]
    exact natural.mp originalTruth
  · exact type_equation_instances history accepted proof other functionArity equalityParameter
      equalityRegistered selectionParameter selectionDeclaration assignment substitution added translated

end FirstType

namespace Controls

open UniformTypeDefinitionFamily.Controls

/-- The original admitted dependency-bearing declarations and witnessed
polymorphic type step are retained in their original order. -/
noncomputable def originalFirstType : History DefinitionAdapters.ContextControls.coreContext polymorphicResult.context
    (DefinitionHistoryModels.Controls.polymorphicDefinitions.records.map
      (fun result => result.output.definitionTheorem) ++
      [polymorphicResult.output.abstractionRepresentationTheorem,
        polymorphicResult.output.representationAbstractionTheorem]) :=
  .typeDefinition (History.ofConstants DefinitionHistoryModels.Controls.polymorphicDefinitions)
    polymorphicCertificates polymorphicRequest polymorphicResult polymorphic_result_admitted
    (by rw [History.equationTheory_of_constants]
        exact polymorphic_existence_proven)

theorem original_record_count :
    (DefinitionHistoryModels.Controls.polymorphicDefinitions.records.map
      (fun result => result.output.definitionTheorem) ++
      [polymorphicResult.output.abstractionRepresentationTheorem,
        polymorphicResult.output.representationAbstractionTheorem]).length = 4 := by
  rfl

/-- A proof over later rows is not the first type step's required input:
the required proof type refers to the preceding rows only. -/
theorem first_type_preceding_theory :
    equationTheory (DefinitionHistoryModels.Controls.polymorphicDefinitions.records.map
      (fun result => result.output.definitionTheorem)) =
      UniformTypeDefinitionFamily.definitionTheory DefinitionHistoryModels.Controls.polymorphicDefinitions :=
  History.equationTheory_of_constants _

/-- A genuine declaration after the first type retains that type's exact
representation symbol and its original public schema. -/
def afterTypeSource : SourceTerm :=
  .const polymorphicResult.output.representationConstant
    (UniformTypeDefinitionModels.representationAnnotation
      (request := polymorphicRequest) (result := polymorphicResult) TypeSubst.empty)

def afterTypeName : Name := Name.global "mixedRepresentationAlias"

def emptyInstances : InstanceWitnesses := fun _ _ => TypeSubst.empty

theorem after_type_constant_admitted :
    (admitConstantInTheory polymorphicResult.context emptyInstances afterTypeName afterTypeSource).isSome = true := by
  decide +kernel

def afterTypeResult : ContextConstantDefinitionResult :=
  (admitConstantInTheory polymorphicResult.context emptyInstances afterTypeName afterTypeSource).get after_type_constant_admitted

theorem after_type_result_admitted :
    admitConstantInTheory polymorphicResult.context emptyInstances afterTypeName afterTypeSource = some afterTypeResult :=
  (Option.some_get after_type_constant_admitted).symm

noncomputable def afterTypeHistory :=
  History.constant originalFirstType emptyInstances afterTypeName afterTypeSource afterTypeResult after_type_result_admitted

def secondWitnessSource : SourceTerm :=
  .abs (Name.global "x") (SourceTypeDefinitionTransport.sourceCarrierType polymorphicRequest TypeSubst.empty)
    (.var (Name.global "x") (SourceTypeDefinitionTransport.sourceCarrierType polymorphicRequest TypeSubst.empty))

def secondWitness : CanonicalTerm :=
  ⟨.abs (SourceTypeDefinitionTransport.sourceCarrierType polymorphicRequest TypeSubst.empty) (.bound 0),
    Ty.function (SourceTypeDefinitionTransport.sourceCarrierType polymorphicRequest TypeSubst.empty)
      (SourceTypeDefinitionTransport.sourceCarrierType polymorphicRequest TypeSubst.empty),
    by simp [DBTerm.inferType]⟩

def secondPredicateSource : SourceTerm :=
  .app (.const Const.equality (Ty.equality secondWitness.ty)) secondWitnessSource

def secondExistence : Theorem := Theorem.emptyResult ∅
  (CanonicalTerm.equalityOfSameType secondWitness secondWitness rfl)

def secondRequest : TypeOperatorDefinitionRequest :=
  { typeName := Name.global "mixedSecondIdentity"
    abstractionName := Name.global "absMixedSecondIdentity"
    representationName := Name.global "repMixedSecondIdentity"
    typeVariables := sortedParameters secondPredicateSource
    predicateSource := secondPredicateSource
    existence := secondExistence }

def secondInstances : InstanceWitnesses := fun constant _ =>
  if constant.same Const.equality then ⟨[(DefinitionAdapters.ContextControls.equalityParameter, secondWitness.ty)]⟩
  else TypeSubst.empty

theorem second_type_admitted :
    (admitSourceTypeInTheory afterTypeResult.context secondInstances secondRequest).isSome = true := by
  decide +kernel

def secondResult : SourceTypeDefinitionResult :=
  (admitSourceTypeInTheory afterTypeResult.context secondInstances secondRequest).get second_type_admitted

theorem second_result_admitted :
    admitSourceTypeInTheory afterTypeResult.context secondInstances secondRequest = some secondResult :=
  (Option.some_get second_type_admitted).symm

theorem second_existence_derived :
    Mettapedia.Logic.Derives (HOLLight.Rule emptyAxiomPolicy) secondRequest.existence := by
  refine Mettapedia.Logic.Derives.node [] secondExistence ?_ ?_
  · refine Or.inl ⟨.refl secondWitness, rfl, ?_⟩
    exact ⟨_, CanonicalTerm.equalityOfSameType_semantics _ _ rfl, rfl, rfl, rfl⟩
  · intro premise member
    cases member

/-- The chronology genuinely alternates carrier-changing and constant
extensions; the second carrier's predicate contains the first carrier. -/
noncomputable def twoTypesHistory :=
  History.typeDefinition afterTypeHistory secondInstances secondRequest secondResult second_result_admitted
    (History.existence_proof_of_kernel_derives second_result_admitted _ second_existence_derived)

theorem mixed_record_count :
    ((DefinitionHistoryModels.Controls.polymorphicDefinitions.records.map
      (fun result => result.output.definitionTheorem) ++
      [polymorphicResult.output.abstractionRepresentationTheorem,
        polymorphicResult.output.representationAbstractionTheorem]) ++
      [afterTypeResult.output.definitionTheorem] ++
      [secondResult.output.abstractionRepresentationTheorem,
        secondResult.output.representationAbstractionTheorem]).length = 7 := by
  rfl

/-- Original source admission rejects the dependency before its type and
symbols have actually been registered. -/
theorem premature_alias_refused :
    admitConstantInTheory DefinitionHistoryModels.Controls.polymorphicAliasResult.context
      emptyInstances afterTypeName afterTypeSource = none := by
  decide +kernel

/-- A repeated original type request is refused after its first admission. -/
theorem repeated_type_refused :
    admitSourceTypeInTheory polymorphicResult.context polymorphicCertificates polymorphicRequest = none := by
  decide +kernel

end Controls

end Mettapedia.Languages.HOLLight.MixedDefinitionHistory
