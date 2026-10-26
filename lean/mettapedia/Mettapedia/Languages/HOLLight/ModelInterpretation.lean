import Mettapedia.Languages.OpenTheory.TypeFamilySemantics
import Mettapedia.Languages.HOLLight.DefinitionAdapters
import Mettapedia.Logic.HOL.HOLLightBooleanDefinitions

/-!
# HOL Light source meanings and witnessed model extensions

The source constant is recognized by its complete identity and exact schema
instance. Its meaning is the selection operation constructed over the actual
type-operator families. Other symbols retain their supplied meanings.

The admitted definition bodies and type-definition premises have constructed
images in the shared STT model. Constant extensions use the translated body;
type extensions use the interpreted predicate and the retained witness. Both
preserve old-language truth along their explicit signature maps. Uniform
interpretation of complete polymorphic declaration histories is separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ModelInterpretation

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics

universe w

/-- The source declares this constant in `class.ml`; provenance participates
in its identity just as it does for the equality constant. -/
def selectionConstant : Const := .mk (Name.global "@") .undefined

def selectionType (operand : Ty) : Ty := .function (.function operand Ty.bool) operand

def selectionOperand? (constant : Const) (annotation : Ty) : Option Ty :=
  if Const.same constant selectionConstant then
    match annotation.destFunction? with
    | none => none
    | some (predicate, result) =>
        match predicate.destFunction? with
        | none => none
        | some (operand, proposition) =>
            if Ty.same operand result && proposition.isBool then some operand else none
  else none

theorem selectionOperand?_eq_some_iff (constant : Const) (annotation operand : Ty) :
    selectionOperand? constant annotation = some operand ↔
      constant = selectionConstant ∧ annotation = selectionType operand := by
  constructor
  · intro recognized
    unfold selectionOperand? at recognized
    split at recognized
    · rename_i sameConstant
      refine ⟨(Const.same_eq_true_iff _ _).mp sameConstant, ?_⟩
      split at recognized
      · contradiction
      · rename_i predicate result outer
        split at recognized
        · contradiction
        · rename_i argument proposition inner
          split at recognized
          · rename_i checked
            simp only [Bool.and_eq_true, Ty.same_eq_true_iff, Ty.isBool_eq_true_iff] at checked
            obtain ⟨rfl, rfl⟩ := checked
            cases recognized
            rw [Ty.eq_function_of_destFunction? outer,
              Ty.eq_function_of_destFunction? inner]
            rfl
          · contradiction
    · contradiction
  · rintro ⟨rfl, rfl⟩
    simp [selectionOperand?, selectionType, Ty.isBool_eq_true_iff]

@[simp] theorem selectionOperand?_selection (operand : Ty) :
    selectionOperand? selectionConstant (selectionType operand) = some operand :=
  (selectionOperand?_eq_some_iff _ _ _).mpr ⟨rfl, rfl⟩

@[simp] theorem selectionType_toHOL (operand : Ty) :
    (selectionType operand).toHOL = .arr (.arr operand.toHOL .prop) operand.toHOL := by
  simp [selectionType]

abbrev Meanings (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :=
  ∀ {type}, Symbol type → HOL.Ty.denote.{0, w + 1} (atomicCarrier other assignment) type

/-- Transport the carrier's own selector into the shared STT value type.
This makes the source meaning follow the evaluated family under substitution. -/
noncomputable def sourceSelection (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (operand : Ty) :
    HOL.Ty.denote.{0, w + 1} (atomicCarrier other assignment)
      (.arr (.arr operand.toHOL .prop) operand.toHOL) :=
  fun predicate => holValue other assignment operand
    ((evaluate (primitiveFamilies other) assignment operand).select
      (fun value => predicate (holValue other assignment operand value)))

theorem sourceSelection_specified (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (operand : Ty)
    (predicate : HOL.Ty.denote.{0, w + 1} (atomicCarrier other assignment)
      (.arr operand.toHOL .prop))
    (existsValue : ∃ value, (predicate value).down) :
    (predicate (sourceSelection other assignment operand predicate)).down := by
  obtain ⟨value, holds⟩ := existsValue
  exact Domain.select_specified (evaluate (primitiveFamilies other) assignment operand)
    (fun value => predicate (holValue other assignment operand value))
    ⟨(holValue other assignment operand).symm value, by simpa using holds⟩

/-- Install the constructed selector only at faithful source occurrences.
The fallback is data for ordinary symbols, not an assumed validity theorem. -/
noncomputable def interpretation (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (ordinary : Meanings other assignment) : Meanings other assignment
  | _, .variable sourceVar typed => ordinary (.variable sourceVar typed)
  | type, .constant constant annotation typed =>
      match recognized : selectionOperand? constant annotation with
      | none => ordinary (.constant constant annotation typed)
      | some operand =>
          have annotationEq := (selectionOperand?_eq_some_iff _ _ _).mp recognized
          have typeEq : HOL.Ty.arr (HOL.Ty.arr operand.toHOL .prop) operand.toHOL = type := by
            rw [← typed, annotationEq.2, selectionType_toHOL]
          typeEq ▸ sourceSelection other assignment operand

noncomputable def model (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (ordinary : Meanings other assignment) : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol :=
  TypeFamilySemantics.model other assignment (interpretation other assignment ordinary)

theorem model_fullDomains (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (ordinary : Meanings other assignment) : (model other assignment ordinary).FullDomains :=
  TypeFamilySemantics.model_fullDomains _ _ _

theorem model_models_eta (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (ordinary : Meanings other assignment) (domain codomain : Ty) :
    (model other assignment ordinary).models
      (HOL.HOLLightStandardTheory.etaFormula domain.toHOL codomain.toHOL) :=
  HOL.HOLLightStandardTheory.models_eta_in _ _ _

/-- An explicit initial interpretation for otherwise unconstrained symbols.
It is a choice of model data, not a source execution rule. -/
noncomputable def pointedMeanings (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    Meanings other assignment :=
  fun {type} _ => (standardModel other assignment).defaultValue
    (fun atomic => (evaluate (primitiveFamilies other) assignment atomic.val).inhabitant) type

theorem model_selection (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (ordinary : Meanings other assignment) (operand : Ty) :
    (model other assignment ordinary).constDen
        (.constant selectionConstant (selectionType operand) (selectionType_toHOL operand)) =
      sourceSelection other assignment operand := by
  simp only [model, TypeFamilySemantics.model, HOL.HenkinModel.standard, interpretation]
  split
  · rename_i absent
    rw [selectionOperand?_selection] at absent
    cases absent
  · rename_i actual recognized
    have same : actual = operand :=
      Option.some.inj (recognized.symm.trans (selectionOperand?_selection operand))
    subst actual
    rfl

/-- The formula uses the actual source symbol, rather than a theorem name or
the internal selection signature of the standard-theory model. -/
def selectionFormula (operand : Ty) : HOL.ClosedFormula Symbol :=
  .all (.all (.imp
    (.app (.var (.vs .vz)) (.var .vz))
    (.app (.var (.vs .vz))
      (.app (.const (.constant selectionConstant (selectionType operand)
        (selectionType_toHOL operand))) (.var (.vs .vz))))))

theorem models_selectionFormula (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (ordinary : Meanings other assignment) (operand : Ty) :
    (model other assignment ordinary).models (selectionFormula operand) := by
  change ∀ predicate, (model other assignment ordinary).adm (.arr operand.toHOL .prop) predicate →
    ∀ value, (model other assignment ordinary).adm operand.toHOL value →
      (predicate value).down →
      (predicate ((model other assignment ordinary).constDen
        (.constant selectionConstant (selectionType operand) (selectionType_toHOL operand))
        predicate)).down
  intro predicate _ value _ holds
  rw [model_selection]
  exact sourceSelection_specified other assignment operand predicate ⟨value, holds⟩

/-- Expand the source's Boolean definitions while retaining its actual
selector constant. This is distinct from the primitive-connective formula. -/
def encodedSelectionFormula (operand : Ty) : HOL.ClosedFormula Symbol :=
  HOL.HOLLightBooleanDefinitions.all (HOL.HOLLightBooleanDefinitions.all
    (HOL.HOLLightBooleanDefinitions.imp
      (.app (.var (.vs .vz)) (.var .vz))
      (.app (.var (.vs .vz))
        (.app (.const (.constant selectionConstant (selectionType operand)
          (selectionType_toHOL operand))) (.var (.vs .vz))))))

theorem models_encodedSelectionFormula (other : OperatorFamilies.{w})
    (assignment : Assignment.{w}) (ordinary : Meanings other assignment) (operand : Ty) :
    (model other assignment ordinary).models (encodedSelectionFormula operand) := by
  simp only [encodedSelectionFormula, HOL.HenkinModel.models, HOL.PreModel.models,
    HOL.HOLLightBooleanDefinitions.denote_all,
    HOL.HOLLightBooleanDefinitions.denote_imp _ (model_fullDomains other assignment ordinary)]
  exact models_selectionFormula other assignment ordinary operand

namespace TypeAdmission

open DefinitionAdapters SignatureFormation

/-- The jointly typed image of an actual predicate application. The three
relations refer to the checked source terms, not to declaration labels. -/
structure ApplicationImage (predicate witness conclusion : CanonicalTerm) where
  predicateTerm : HOL.ClosedTerm Symbol (.arr witness.ty.toHOL .prop)
  witnessTerm : HOL.ClosedTerm Symbol witness.ty.toHOL
  predicateTranslated : TranslatesCompositionally [] predicate.term
    (.arr witness.ty.toHOL .prop) predicateTerm
  witnessTranslated : TranslatesCompositionally [] witness.term
    witness.ty.toHOL witnessTerm
  conclusionTranslated : TranslatesCompositionally [] conclusion.term .prop
    (.app predicateTerm witnessTerm)

theorem applicationImage_nonempty {predicate witness conclusion : CanonicalTerm}
    (application : CanonicalTerm.ApplicationSemantics predicate witness conclusion)
    (boolean : conclusion.IsBool) : Nonempty (ApplicationImage predicate witness conclusion) := by
  have predicateType := Ty.eq_function_of_destFunction? application.functionType
  rw [boolean] at predicateType
  have predicateExists : ∃ target : HOL.ClosedTerm Symbol (.arr witness.ty.toHOL .prop),
      TranslatesCompositionally [] predicate.term (.arr witness.ty.toHOL .prop) target := by
    have translated := predicate.exists_translation
    rw [predicateType, Ty.toHOL_function, Ty.toHOL_bool] at translated
    exact translated
  obtain ⟨predicateTerm, predicateTranslated⟩ := predicateExists
  obtain ⟨witnessTerm, witnessTranslated⟩ := witness.exists_translation
  refine ⟨⟨predicateTerm, witnessTerm, predicateTranslated, witnessTranslated, ?_⟩⟩
  obtain ⟨_, _, _, _, shape⟩ := application
  rw [shape]
  exact .app predicateTranslated witnessTranslated

noncomputable def applicationImage {predicate witness conclusion : CanonicalTerm}
    (application : CanonicalTerm.ApplicationSemantics predicate witness conclusion)
    (boolean : conclusion.IsBool) : ApplicationImage predicate witness conclusion :=
  Classical.choice (applicationImage_nonempty application boolean)

def ApplicationImage.formula {predicate witness conclusion : CanonicalTerm}
    (image : ApplicationImage predicate witness conclusion) : HOL.ClosedFormula Symbol :=
  .app image.predicateTerm image.witnessTerm

/-- Selection of translation witnesses cannot change either interpreted term. -/
theorem ApplicationImage.unique {predicate witness conclusion : CanonicalTerm}
    (left right : ApplicationImage predicate witness conclusion) : left = right := by
  have predicateEqual := eq_of_heq (left.predicateTranslated.unique right.predicateTranslated).2
  have witnessEqual := eq_of_heq (left.witnessTranslated.unique right.witnessTranslated).2
  cases left
  cases right
  simp_all

/-- The semantic obligation can be discharged using any valid translation
of the actual source premise. Translation witness selection is immaterial. -/
theorem ApplicationImage.holds_iff {predicate witness conclusion : CanonicalTerm}
    (image : ApplicationImage predicate witness conclusion)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    {formula : HOL.ClosedFormula Symbol}
    (translated : TranslatesCompositionally [] conclusion.term .prop formula) :
    M.models image.formula ↔ M.models formula := by
  have equal := eq_of_heq (image.conclusionTranslated.unique translated).2
  rw [ApplicationImage.formula, equal]

theorem existence_boolean {context : TheoryContext} {instances : InstanceWitnesses}
    {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context instances request = some result) :
    request.existence.sequent.concl.IsBool := by
  have core := (admitSourceTypeInTheory_result accepted).2.1
  have checked := (admitTypeInTheory_result core).2.2.2.2.2.1
  obtain ⟨_, _, _, boolean, _⟩ := checkTypeOperatorDefinition_result checked
  exact boolean

/-- Admission determines a translation of the exact retained predicate and
witness. The existence premise remains the request's actual conclusion. -/
noncomputable def admittedImage {context : TheoryContext} {instances : InstanceWitnesses}
    {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context instances request = some result) :
    ApplicationImage result.core.predicate result.core.witness request.existence.sequent.concl :=
  applicationImage ((admitTypeInTheory_result
    (admitSourceTypeInTheory_result accepted).2.1).1) (existence_boolean accepted)

variable {predicate witness conclusion : CanonicalTerm}
  (image : ApplicationImage predicate witness conclusion)
  (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)

def representedPredicate : HOL.Ty.denote.{0, w + 1} M.Carrier witness.ty.toHOL → Prop :=
  HOL.TypeDefinitionModel.predicateOf M witness.ty.toHOL image.predicateTerm

def representedWitness : HOL.Ty.denote.{0, w + 1} M.Carrier witness.ty.toHOL :=
  M.denote image.witnessTerm (fun index => nomatch index)

theorem witness_valid (holds : M.models image.formula) :
    representedPredicate image M (representedWitness image M) := by
  simp only [representedPredicate, representedWitness, HOL.TypeDefinitionModel.predicateOf,
    ApplicationImage.formula, HOL.HenkinModel.models, HOL.HenkinModel.denote,
    HOL.PreModel.models, HOL.PreModel.denote] at holds ⊢
  convert holds using 1
  apply Iff.of_eq
  apply congrArg ULift.down
  exact congrArg₂ (fun function value => function value)
    (M.denote_closed_valuation_eq image.predicateTerm _ _)
    (M.denote_closed_valuation_eq image.witnessTerm _ _)

/-- The carrier and both defining maps are constructed from the admitted
predicate and the meaning of its actual witness. -/
noncomputable def extension (holds : M.models image.formula) :=
  HOL.TypeDefinitionModel.model M witness.ty.toHOL (representedPredicate image M)
    (representedWitness image M) (witness_valid image M holds)

theorem extension_fullDomains (holds : M.models image.formula) :
    (extension image M holds).FullDomains :=
  HOL.TypeDefinitionModel.fullDomains _ _ _ _ _

theorem extension_preserves_old_truth (full : M.FullDomains)
    (holds : M.models image.formula) (sentence : HOL.ClosedFormula Symbol) :
    (extension image M holds).models
      (HOL.mapTypes HOL.TypeDefinitionModel.includeBase
        HOL.TypeDefinitionModel.Symbol.old sentence) ↔ M.models sentence :=
  HOL.TypeDefinitionModel.models_include M _ _ _ _ full sentence

theorem extension_models_abstractionRepresentation (holds : M.models image.formula) :
    (extension image M holds).models
      (HOL.TypeDefinitionModel.abstractionRepresentationLaw (Const := Symbol) witness.ty.toHOL) :=
  HOL.TypeDefinitionModel.models_abstractionRepresentationLaw M _ _ _ _

theorem extension_models_representationAbstractionPointwise (full : M.FullDomains)
    (holds : M.models image.formula) :
    (extension image M holds).models
      (HOL.TypeDefinitionModel.representationAbstractionPointwiseLaw witness.ty.toHOL
        image.predicateTerm) :=
  HOL.TypeDefinitionModel.models_representationAbstractionPointwiseLaw M _ full _ _ _

noncomputable def extension_inhabited (old : M.InhabitedDomains)
    (holds : M.models image.formula) : (extension image M holds).InhabitedDomains :=
  HOL.TypeDefinitionModel.inhabitedDomains M _ _ _ _ old

noncomputable def extension_choice (old : M.InhabitedDomains)
    (holds : M.models image.formula) : (extension image M holds).HilbertChoice :=
  HOL.TypeDefinitionModel.choice M _ _ _ _ old

noncomputable def extension_infinity {base : AtomicTy} (old : M.DedekindInfinityWitness base)
    (holds : M.models image.formula) :
    (extension image M holds).DedekindInfinityWitness (.inl base) :=
  HOL.TypeDefinitionModel.infinity M _ _ _ _ old

end TypeAdmission

namespace ConstantAdmission

open DefinitionAdapters SignatureFormation

/-- The retained source equation names the admitted definition identity and
its checked body, including the hidden-type-parameter admission guard. -/
theorem source_equation {context : TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context instances name source = some result) :
    result.output.constant = .mk name (.defined source) ∧
      CanonicalTerm.EqualityConstructionSemantics
        (CanonicalTerm.constant result.output.constant result.definition.ty)
        result.definition result.output.definitionTheorem.sequent.concl := by
  have admitted := admitConstantInTheory_result accepted
  have checked := (checkSource_sound _ _ admitted.1).1
  obtain ⟨body, equality, bodyChecked, _, _, origin, construction, parts⟩ :=
    checkConstantDefinition_result admitted.2.2.2.2.1
  have equal := Option.some.inj (bodyChecked.symm.trans checked)
  subst body
  exact ⟨origin, parts.2.2 ▸ construction⟩

noncomputable def body (result : ContextConstantDefinitionResult) :
    HOL.ClosedTerm Symbol result.definition.ty.toHOL :=
  closedTranslation result.definition.term result.definition.exists_translation

theorem body_translated (result : ContextConstantDefinitionResult) :
    TranslatesCompositionally [] result.definition.term result.definition.ty.toHOL (body result) :=
  closedTranslation_spec _ _

/-- The model extension uses the actual translated body. Freshness and
signature registration are provided by the source admission certificate. -/
noncomputable def extension (result : ContextConstantDefinitionResult)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) := M.definitionExtension (body result)

theorem extension_defining_equation (result : ContextConstantDefinitionResult)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :
    (extension result M).models (HOL.HenkinModel.definitionEquation (body result)) :=
  M.definitionExtension_models_equation _

theorem extension_preserves_old_terms (result : ContextConstantDefinitionResult)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) {context : HOL.Ctx AtomicTy}
    {type : HOL.Ty AtomicTy} (term : HOL.Term Symbol context type)
    (valuation : M.Valuation context) :
    (extension result M).denote (HOL.DefinedConst.embed term) valuation = M.denote term valuation :=
  M.definitionExtension_embed _ _ _

theorem extension_preserves_old_truth (result : ContextConstantDefinitionResult)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (sentence : HOL.ClosedFormula Symbol) :
    (extension result M).models (HOL.DefinedConst.embed sentence) ↔ M.models sentence :=
  M.definitionExtension_models_embed _ sentence

/-- The admitted source body at a simultaneous type instance. The source
symbol map is retained, and the body acquires its actual instantiated type. -/
noncomputable def instantiatedExtension (substitution : TypeSubst)
    (result : ContextConstantDefinitionResult)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :=
  M.definitionExtension
    (HOL.mapTypes substitution.baseInstance substitution.symbolInstance (body result))

/-- Source type instantiation and definition extension commute as complete
model data for every admitted constant body. -/
theorem extension_reindex (substitution : TypeSubst) (result : ContextConstantDefinitionResult)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (full : M.FullDomains) :
    extension result (reindexedModel substitution M) =
      HOL.HenkinModel.standardTypeReduct substitution.baseInstance
        (HOL.DefinedConst.typeInstance substitution.baseInstance substitution.symbolInstance)
        (instantiatedExtension substitution result M) :=
  HOL.HenkinModel.definitionExtension_typeReduct _ _ M full (body result)

theorem extension_reindex_preserves_truth (substitution : TypeSubst)
    (result : ContextConstantDefinitionResult)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (full : M.FullDomains)
    (sentence : HOL.ClosedFormula (HOL.DefinedConst Symbol result.definition.ty.toHOL)) :
    (extension result (reindexedModel substitution M)).models sentence ↔
      (instantiatedExtension substitution result M).models
        (HOL.mapTypes substitution.baseInstance
          (HOL.DefinedConst.typeInstance substitution.baseInstance substitution.symbolInstance)
          sentence) :=
  HOL.HenkinModel.definitionExtension_models_typeReduct _ _ M full (body result) sentence

/-- Recheck an actual admitted body at a simultaneous source type instance. -/
def instanceTerm (result : ContextConstantDefinitionResult) (substitution : TypeSubst) :
    CanonicalTerm :=
  (TypeCorrectTermSubstitution.ofTypes substitution).apply result.definition

noncomputable def instanceBody (result : ContextConstantDefinitionResult)
    (substitution : TypeSubst) :
    HOL.ClosedTerm Symbol (substitution.apply result.definition.ty).toHOL :=
  closedTranslation (instanceTerm result substitution).term
    (instanceTerm result substitution).exists_translation

theorem instanceBody_translated (result : ContextConstantDefinitionResult)
    (substitution : TypeSubst) :
    TranslatesCompositionally [] (instanceTerm result substitution).term
      (substitution.apply result.definition.ty).toHOL (instanceBody result substitution) :=
  closedTranslation_spec _ _

theorem instanceBody_identity (result : ContextConstantDefinitionResult) :
    HEq (instanceBody result TypeSubst.empty) (body result) :=
  ((instanceBody_translated result TypeSubst.empty).unique
    ((body_translated result).of_term_eq (TermSubst.typeInstance_identity result.definition.term).symm)).2

/-- Reindex the actual selected body, rather than postulating a coherent
meaning. Sequential source type instances correspond to the existing STT
substitution image, with all symbol and binding occurrences retained. -/
theorem instanceBody_reindex (result : ContextConstantDefinitionResult)
    (first second : TypeSubst) :
    HEq ((TypeCorrectTermSubstitution.ofTypes second).targetMap (instanceBody result first))
      (instanceBody result (first.compose second)) := by
  have translated := (instanceBody_translated result first).applyDB
    (TypeCorrectTermSubstitution.ofTypes second)
  exact (translated.unique ((instanceBody_translated result (first.compose second)).of_term_eq
    (TermSubst.typeInstance_composition first second result.definition.term).symm)).2

/-- Different certificates for one public type yield the same actual body.
This uses the source's hidden-parameter guard, not an assumed parametricity law. -/
theorem instanceBody_independent (result : ContextConstantDefinitionResult)
    (bounded : result.definition.term.typeVariables ⊆ result.definition.ty.typeVariables)
    (first second : TypeSubst)
    (sameInstance : first.apply result.definition.ty = second.apply result.definition.ty) :
    HEq (instanceBody result first) (instanceBody result second) := by
  have sameBody := definition_instance_independent first second
    result.definition.ty result.definition.term bounded sameInstance
  exact ((instanceBody_translated result first).unique
    ((instanceBody_translated result second).of_term_eq sameBody.symm)).2

/-- Interpret every legitimate instance of the new source identity by its
checked body. Unknown identities and types retain their old interpretation.
Certificate choice is immaterial for admitted definitions. -/
noncomputable def sourceExpansion (result : ContextConstantDefinitionResult) :
    ∀ {type}, Symbol type → HOL.ClosedTerm Symbol type
  | _, .variable sourceVar typed => .const (.variable sourceVar typed)
  | type, .constant constant annotation typed => by
      classical
      exact if constant = result.output.constant then
        if instanceExists : ∃ substitution : TypeSubst,
            substitution.apply result.definition.ty = annotation then
          let substitution := Classical.choose instanceExists
          have typeEqual : (substitution.apply result.definition.ty).toHOL = type :=
            (congrArg Ty.toHOL (Classical.choose_spec instanceExists)).trans typed
          typeEqual ▸ instanceBody result substitution
        else .const (.constant constant annotation typed)
      else .const (.constant constant annotation typed)

theorem sourceExpansion_variable (result : ContextConstantDefinitionResult)
    {type : HOL.Ty AtomicTy} (sourceVar : SourceVar) (typed : sourceVar.ty.toHOL = type) :
    sourceExpansion result (.variable sourceVar typed) = .const (.variable sourceVar typed) := rfl

theorem sourceExpansion_other (result : ContextConstantDefinitionResult)
    {type : HOL.Ty AtomicTy} (constant : Const) (annotation : Ty)
    (typed : annotation.toHOL = type) (different : constant ≠ result.output.constant) :
    sourceExpansion result (.constant constant annotation typed) =
      .const (.constant constant annotation typed) := by
  classical
  simp [sourceExpansion, different]

/-- A display annotation which is not a schema instance does not acquire a
definition meaning merely because it uses the registered constant identity. -/
theorem sourceExpansion_noninstance (result : ContextConstantDefinitionResult)
    {type : HOL.Ty AtomicTy} (annotation : Ty) (typed : annotation.toHOL = type)
    (unavailable : ¬ ∃ substitution : TypeSubst,
      substitution.apply result.definition.ty = annotation) :
    sourceExpansion result (.constant result.output.constant annotation typed) =
      .const (.constant result.output.constant annotation typed) := by
  classical
  simp [sourceExpansion, unavailable]

/-- The selected certificate gives the same body as every supplied valid
certificate. The equality is typed heterogeneously to expose its transport. -/
theorem sourceExpansion_instance (result : ContextConstantDefinitionResult)
    (bounded : result.definition.term.typeVariables ⊆ result.definition.ty.typeVariables)
    (substitution : TypeSubst) :
    sourceExpansion result
        (.constant result.output.constant (substitution.apply result.definition.ty) rfl) =
      instanceBody result substitution := by
  classical
  simp only [sourceExpansion, ite_true]
  split
  · rename_i instanceExists
    apply eq_of_heq
    refine HEq.trans ?_ (instanceBody_independent result bounded
      (Classical.choose instanceExists) substitution (Classical.choose_spec instanceExists))
    exact eqRec_heq _ _
  · rename_i unavailable
    exact False.elim (unavailable ⟨substitution, rfl⟩)

/-- A shared denotation node for the existing constant-substitution reduct.
Its named interface keeps later extensions from unfolding earlier bodies. -/
@[irreducible] noncomputable def sourceMeanings (result : ContextConstantDefinitionResult)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :
    ∀ {type}, Symbol type → HOL.Ty.denote.{0, w + 1} M.Carrier type :=
  (M.constantSubstitutionReduct (sourceExpansion result)).constDen

theorem sourceMeanings_eq (result : ContextConstantDefinitionResult)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :
    @sourceMeanings result M =
      @(M.constantSubstitutionReduct (sourceExpansion result)).constDen := by
  unfold sourceMeanings
  rfl

noncomputable def sourcePreModel (result : ContextConstantDefinitionResult)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :
    HOL.PreModel.{0, 0, w + 1} AtomicTy Symbol :=
  { (M.constantSubstitutionReduct (sourceExpansion result)).toPreModel with
    constDen := sourceMeanings result M
    const_mem := by
      intro type constant
      rw [sourceMeanings_eq]
      exact (M.constantSubstitutionReduct (sourceExpansion result)).const_mem constant }

theorem sourcePreModel_eq (result : ContextConstantDefinitionResult)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :
    sourcePreModel result M =
      (M.constantSubstitutionReduct (sourceExpansion result)).toPreModel := by
  unfold sourcePreModel sourceMeanings
  rfl

/-- The source identity has one meaning at every admitted polymorphic
instance. Closure is inherited from the existing substitution reduct. -/
noncomputable def sourceExtension (result : ContextConstantDefinitionResult)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :
    HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol where
  toPreModel := sourcePreModel result M
  term_closed := by
    rw [sourcePreModel_eq]
    exact (M.constantSubstitutionReduct (sourceExpansion result)).term_closed

/-- A constant-only extension keeps the same value universe. -/
@[simp] theorem sourceExtension_carrier (result : ContextConstantDefinitionResult)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :
    (sourceExtension result M).Carrier = M.Carrier := rfl

theorem sourceExtension_eq_reduct (result : ContextConstantDefinitionResult)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :
    sourceExtension result M = M.constantSubstitutionReduct (sourceExpansion result) := by
  apply HOL.HenkinModel.ext_data
    (M := sourceExtension result M)
    (N := M.constantSubstitutionReduct (sourceExpansion result)) rfl
  · rfl
  · exact heq_of_eq (sourceMeanings_eq result M)

attribute [local semireducible] sourceMeanings

theorem sourceExtension_fullDomains (result : ContextConstantDefinitionResult)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (full : M.FullDomains) :
    (sourceExtension result M).FullDomains :=
  (M.constantSubstitutionReduct_fullDomains_iff (sourceExpansion result)).mpr full

/-- Standardizing the admitted meanings retains the existing source extension.
The equation is abstract in the declaration, so callers need not unfold a
concrete definition body to compare model structure fields. -/
theorem sourceStandard_eq_sourceExtension (result : ContextConstantDefinitionResult)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (full : M.FullDomains) :
    HOL.HenkinModel.standard M.Carrier (sourceMeanings result M) = sourceExtension result M :=
  HOL.HenkinModel.standard_eq_of_fullDomains (sourceExtension result M)
    (sourceExtension_fullDomains result M full)

/-- The registered source identity receives the denotation of its actual
body at every admitted public type instance. -/
theorem sourceExtension_constant_instance (result : ContextConstantDefinitionResult)
    (bounded : result.definition.term.typeVariables ⊆ result.definition.ty.typeVariables)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (substitution : TypeSubst) :
    (sourceExtension result M).constDen
        (.constant result.output.constant (substitution.apply result.definition.ty) rfl) =
      M.denote (instanceBody result substitution) (fun index => nomatch index) := by
  change M.denote (sourceExpansion result
    (.constant result.output.constant (substitution.apply result.definition.ty) rfl)) _ = _
  rw [sourceExpansion_instance result bounded substitution]
  congr 1
  funext type index
  cases index

/-- Other declaration identities retain their meaning, including at public
type instances distinct from those of the newly registered definition. -/
theorem sourceExtension_constant_other (result : ContextConstantDefinitionResult)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (constant : Const) (annotation : Ty) {type : HOL.Ty AtomicTy}
    (typed : annotation.toHOL = type) (different : constant ≠ result.output.constant) :
    (sourceExtension result M).constDen (.constant constant annotation typed) =
      M.constDen (.constant constant annotation typed) := by
  change M.denote (sourceExpansion result (.constant constant annotation typed)) _ = _
  rw [sourceExpansion_other result constant annotation typed different]
  rfl

/-- The named denotation node preserves every other declaration, without
unfolding the preceding model's admitted definition bodies. -/
theorem sourceMeanings_constant_other (result : ContextConstantDefinitionResult)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (constant : Const) (annotation : Ty) {type : HOL.Ty AtomicTy}
    (typed : annotation.toHOL = type) (different : constant ≠ result.output.constant) :
    sourceMeanings result M (.constant constant annotation typed) =
      M.constDen (.constant constant annotation typed) :=
  sourceExtension_constant_other result M constant annotation typed different


/-- Constant denotation updates over a fixed carrier. Keeping the preceding
meanings as a function avoids elaborating complete earlier model extensions
when a later declaration refers to an old symbol. -/
@[irreducible] noncomputable def standardSourceMeanings (result : ContextConstantDefinitionResult)
    (carrier : AtomicTy → Type (w + 1))
    (meanings : ∀ {type}, Symbol type → HOL.Ty.denote.{0, w + 1} carrier type) :
    ∀ {type}, Symbol type → HOL.Ty.denote.{0, w + 1} carrier type :=
  sourceMeanings result (HOL.HenkinModel.standard carrier meanings)

theorem standardSourceMeanings_eq (result : ContextConstantDefinitionResult)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (full : M.FullDomains) :
    @standardSourceMeanings result M.Carrier M.constDen = @sourceMeanings result M := by
  unfold standardSourceMeanings
  have congruent {first second : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol}
      (same : first = second) : HEq (@sourceMeanings result first) (@sourceMeanings result second) := by
    cases same
    rfl
  exact eq_of_heq (congruent (HOL.HenkinModel.standard_eq_of_fullDomains M full))

theorem standardSourceMeanings_constant_other (result : ContextConstantDefinitionResult)
    (carrier : AtomicTy → Type (w + 1))
    (meanings : ∀ {type}, Symbol type → HOL.Ty.denote.{0, w + 1} carrier type)
    (constant : Const) (annotation : Ty) {type : HOL.Ty AtomicTy}
    (typed : annotation.toHOL = type) (different : constant ≠ result.output.constant) :
    standardSourceMeanings result carrier meanings (.constant constant annotation typed) =
      meanings (.constant constant annotation typed) := by
  unfold standardSourceMeanings
  exact sourceMeanings_constant_other result
    (HOL.HenkinModel.standard carrier meanings) constant annotation typed different

/-- The fixed-carrier presentation has exactly the original extension's
semantics on full-domain models; this is not a new declaration authority. -/
theorem standardSourceModel_eq_sourceExtension (result : ContextConstantDefinitionResult)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (full : M.FullDomains) :
    HOL.HenkinModel.standard M.Carrier
      (standardSourceMeanings result M.Carrier M.constDen) = sourceExtension result M := by
  rw [standardSourceMeanings_eq result M full]
  exact sourceStandard_eq_sourceExtension result M full


/-- Expanding a fresh declaration leaves every translation omitting it
unchanged, including open terms and primitive equality. -/
theorem sourceExpansion_preserves_translation (result : ContextConstantDefinitionResult)
    {context : HOL.Ctx AtomicTy} {term : DBTerm} {type : HOL.Ty AtomicTy}
    {target : HOL.Term Symbol context type}
    (translated : TranslatesCompositionally context term type target)
    (omitted : term.OmitsConstant result.output.constant) :
    HOL.substConst (sourceExpansion result) target = target := by
  induction translated with
  | equality recognized typed => rfl
  | constant unrecognized typed =>
      simp only [HOL.substConst, sourceExpansion_other _ _ _ _ omitted, HOL.weakenCtx_const]
  | free typed => simp only [HOL.substConst, sourceExpansion_variable, HOL.weakenCtx_const]
  | bound index => rfl
  | app _ _ functionIH argumentIH =>
      simp only [HOL.substConst, functionIH omitted.1, argumentIH omitted.2]
  | abs typed _ bodyIH => simp only [HOL.substConst, bodyIH omitted]

theorem sourceExtension_preserves_translation (result : ContextConstantDefinitionResult)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    {context : HOL.Ctx AtomicTy} {term : DBTerm} {type : HOL.Ty AtomicTy}
    {target : HOL.Term Symbol context type}
    (translated : TranslatesCompositionally context term type target)
    (omitted : term.OmitsConstant result.output.constant) (valuation : M.Valuation context) :
    (sourceExtension result M).denote target valuation = M.denote target valuation := by
  change (M.constantSubstitutionReduct (sourceExpansion result)).denote target valuation = _
  rw [← M.denote_substConst]
  rw [sourceExpansion_preserves_translation result translated omitted]

theorem admitted_parameters_bounded {context : TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context instances name source = some result) :
    result.definition.term.typeVariables ⊆ result.definition.ty.typeVariables := by
  have admitted := admitConstantInTheory_result accepted
  have sourceChecked := (checkSource_sound _ _ admitted.1).1
  obtain ⟨definition, _, definitionChecked, _, bounded, _, _, _⟩ :=
    checkConstantDefinition_result admitted.2.2.2.2.1
  have same := Option.some.inj (definitionChecked.symm.trans sourceChecked)
  simpa only [same] using bounded

theorem admitted_identity_fresh {context : TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context instances name source = some result) :
    context.signature.constants result.output.constant = none := by
  have fresh : .constant name ∉ context.names := by
    intro used
    rw [admitConstantInTheory_repeated_refused context instances name source used] at accepted
    cases accepted
  apply context.constant_unregistered result.output.constant
  have actualName : constantName result.output.constant = name := by
    rw [(source_equation accepted).1]
    rfl
  simpa only [actualName] using fresh

/-- Admission connects a direct readout of the actual named source body to
the denotation used by the polymorphic model extension. No source name is a
semantic credential: the readout must translate the checked body. -/
theorem sourceExtension_constant_translation
    {context : TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context instances name source = some result)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (full : M.FullDomains)
    (substitution : TypeSubst) {type : HOL.Ty AtomicTy}
    {target : HOL.ClosedTerm Symbol type}
    (translated : Translates []
      ((TypeCorrectTermSubstitution.ofTypes substitution).raw.applyDB (source.toDB []))
      type target) :
    HEq ((sourceExtension result M).constDen
      (.constant result.output.constant (substitution.apply result.definition.ty) rfl))
      (M.denote target (fun index => nomatch index)) := by
  have sourceChecked := (checkSource_sound _ _ (admitConstantInTheory_result accepted).1).1
  have sameBody := (SourceTerm.check_eq_some_iff _ _).mp sourceChecked
  rw [sameBody] at translated
  change Translates [] (instanceTerm result substitution).term type target at translated
  refine HEq.trans (heq_of_eq (sourceExtension_constant_instance result
    (admitted_parameters_bounded accepted) M substitution)) ?_
  exact HEq.symm (translated.denote_heq_compositional
    (instanceBody_translated result substitution) M full (fun index => nomatch index))

/-- A typed public instance can use its own source annotation; the admission
and translation establish equality with the interpreted defining body. -/
theorem sourceExtension_constant_translates
    {context : TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context instances name source = some result)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (full : M.FullDomains)
    (substitution : TypeSubst) (annotation : Ty)
    {type : HOL.Ty AtomicTy} (typed : annotation.toHOL = type)
    (publicInstance : annotation = substitution.apply result.definition.ty)
    {target : HOL.ClosedTerm Symbol type}
    (translated : Translates []
      ((TypeCorrectTermSubstitution.ofTypes substitution).raw.applyDB (source.toDB []))
      type target) :
    (sourceExtension result M).constDen (.constant result.output.constant annotation typed) =
      M.denote target (fun index => nomatch index) := by
  subst annotation
  cases typed
  exact eq_of_heq (sourceExtension_constant_translation accepted M full substitution translated)

/-- Distinct registered declaration names suffice to preserve an older
constant, because admission fixes the complete identity of the new one. -/
theorem sourceExtension_constant_other_name
    {context : TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context instances name source = some result)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (constant : Const) (annotation : Ty) {type : HOL.Ty AtomicTy}
    (typed : annotation.toHOL = type) (different : constantName constant ≠ name) :
    (sourceExtension result M).constDen (.constant constant annotation typed) =
      M.constDen (.constant constant annotation typed) := by
  apply sourceExtension_constant_other
  intro same
  apply different
  rw [same, (source_equation accepted).1]
  rfl

theorem admitted_body_omits_identity {context : TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context instances name source = some result) :
    result.definition.term.OmitsConstant result.output.constant :=
  ((checkSource_sound _ _ (admitConstantInTheory_result accepted).1).2).omits_unregistered
    (admitted_identity_fresh accepted)

/-- Every old-language formula retains exactly its truth value, even though
the new declaration supplies all of its legitimate polymorphic instances. -/
theorem sourceExtension_preserves_old_truth
    {context : TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context instances name source = some result)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    {term : DBTerm} {formula : HOL.ClosedFormula Symbol}
    (formed : AnnotationsFormed context.signature term)
    (translated : TranslatesCompositionally [] term .prop formula) :
    (sourceExtension result M).models formula ↔ M.models formula := by
  change (M.constantSubstitutionReduct (sourceExpansion result)).models formula ↔ M.models formula
  rw [← M.models_substConst]
  rw [sourceExpansion_preserves_translation result translated
    (formed.omits_unregistered (admitted_identity_fresh accepted))]

noncomputable def instanceEquation (result : ContextConstantDefinitionResult) (substitution : TypeSubst) :
    HOL.ClosedFormula Symbol :=
  .eq (.const (.constant result.output.constant (substitution.apply result.definition.ty) rfl))
    (instanceBody result substitution)

/-- Every instance of an actual admitted definition satisfies its defining
equation in the constructed source-symbol model, with no new axiom premise. -/
theorem sourceExtension_models_instanceEquation
    {context : TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context instances name source = some result)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (substitution : TypeSubst) :
    (sourceExtension result M).models (instanceEquation result substitution) := by
  change (M.constantSubstitutionReduct (sourceExpansion result)).models
    (instanceEquation result substitution)
  apply (M.models_substConst (sourceExpansion result) (instanceEquation result substitution)).mp
  have unchanged := sourceExpansion_preserves_translation result
    (instanceBody_translated result substitution)
    ((admitted_body_omits_identity accepted).typeInstance substitution)
  simp only [instanceEquation, HOL.substConst,
    sourceExpansion_instance result (admitted_parameters_bounded accepted),
    unchanged, HOL.weakenCtx_nil]
  apply M.eqv_refl
  exact M.term_closed _ _ (by intro type index; nomatch index)

private theorem typeInstance_equalityDB (substitution : TypeSubst) (operand : Ty)
    (left right : DBTerm) :
    (TermSubst.mk substitution []).applyDB (CanonicalTerm.equalityDB operand left right) =
      CanonicalTerm.equalityDB (substitution.apply operand)
        ((TermSubst.mk substitution []).applyDB left)
        ((TermSubst.mk substitution []).applyDB right) := by
  simp only [CanonicalTerm.equalityDB, TermSubst.applyDB_app, TermSubst.applyDB_const,
    TypeSubst.apply_equality]

/-- Model validity applies to the exact equation returned by the source
admission operation, after any simultaneous type instance and either choice
of its compositional translation. -/
theorem sourceExtension_models_source_equation
    {context : TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context instances name source = some result)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (substitution : TypeSubst) {formula : HOL.ClosedFormula Symbol}
    (translated : TranslatesCompositionally []
      ((TermSubst.mk substitution []).applyDB result.output.definitionTheorem.sequent.concl.term)
      .prop formula) :
    (sourceExtension result M).models formula := by
  have shape := (source_equation accepted).2.2
  rw [shape, typeInstance_equalityDB] at translated
  simp only [CanonicalTerm.constant, TermSubst.applyDB_const] at translated
  obtain ⟨operand, left, right, typed, leftTranslated, rightTranslated, rfl⟩ :=
    translated.equalityDB_inv
  cases typed
  have notEquality : result.output.constant ≠ Const.equality := by
    rw [(source_equation accepted).1]
    intro same
    have origins := (Const.mk.inj same).2
    cases origins
  have unrecognized : equalityOperand? result.output.constant
      (substitution.apply result.definition.ty) = none := by
    unfold equalityOperand?
    simp [Const.same_eq_true_iff, notEquality]
  have leftEqual := eq_of_heq (leftTranslated.unique
    (TranslatesCompositionally.constant (Γ := []) unrecognized rfl)).2
  have rightEqual := eq_of_heq (rightTranslated.unique
    (instanceBody_translated result substitution)).2
  subst left right
  have valid := sourceExtension_models_instanceEquation accepted M substitution
  simpa only [instanceEquation, equalityLambda, HOL.HenkinModel.models, HOL.PreModel.models,
    HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.HenkinModel.extend, HOL.PreModel.extend]
    using valid

theorem selection_preserved
    {context : TheoryContext} {instances : InstanceWitnesses} {name : Name}
    {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context instances name source = some result)
    {schema : Ty} (registered : context.signature.constants selectionConstant = some schema)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (operand : Ty)
    (specified : model.models (selectionFormula operand)) :
    (sourceExtension result model).models (selectionFormula operand) := by
  have apart : selectionConstant ≠ result.output.constant := by
    intro same
    rw [same, admitted_identity_fresh accepted] at registered
    cases registered
  intro predicate admissible value present trueValue
  have old := specified predicate admissible value present trueValue
  have retained := sourceExtension_constant_other result model selectionConstant (selectionType operand)
    (selectionType_toHOL operand) apart
  exact (congrArg (fun selected => (predicate selected).down) (congrFun retained predicate)).mpr old

def infinity_preserved (result : ContextConstantDefinitionResult)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (base : AtomicTy)
    (witness : model.DedekindInfinityWitness base) :
    (sourceExtension result model).DedekindInfinityWitness base where
  successor := witness.successor
  successor_admissible := witness.successor_admissible
  successor_injective := witness.successor_injective
  omitted := witness.omitted
  omitted_not_image := witness.omitted_not_image

end ConstantAdmission

namespace Controls

open TypeAdmission SignatureFormation

/-- The control uses the same checked source predicate, witness, and
premise as registered type-definition admission. -/
noncomputable def identityImage : ApplicationImage DefinitionAdapters.ContextControls.identityPredicate
    DefinitionAdapters.Controls.identityTerm
    DefinitionAdapters.ContextControls.identityTypeRequest.existence.sequent.concl :=
  applicationImage DefinitionAdapters.ContextControls.identityType_application
    (CanonicalTerm.EqualityConstructionSemantics.resultIsBool
      (CanonicalTerm.equalityOfSameType_semantics _ _ rfl))

theorem identityImage_holds (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) : M.models identityImage.formula := by
  have proved := compositionallyProvable_refl (Θ := ∅)
    (CanonicalTerm.equalityOfSameType_semantics DefinitionAdapters.Controls.identityTerm
      DefinitionAdapters.Controls.identityTerm rfl)
  obtain ⟨formula, translated, provable⟩ := proved
  apply (identityImage.holds_iff M translated).mpr
  exact provable_models provable M (M.functionsRespectEqv_of_fullDomains full) (by
    intro sentence member
    simp [compositionalHypotheses] at member)

theorem identity_source_admitted :
    (DefinitionAdapters.admitSourceTypeInTheory
      DefinitionAdapters.ContextControls.coreContext
      DefinitionAdapters.ContextControls.equalityCertificates
      DefinitionAdapters.ContextControls.identityTypeRequest).isSome = true := by
  open DefinitionAdapters DefinitionAdapters.ContextControls in
    have view := CanonicalTerm.applicationView?_eq_some _ _ _ identityType_application
  unfold DefinitionAdapters.admitSourceTypeInTheory
  rw [view]
  cases admitted : DefinitionAdapters.admitTypeInTheoryFromApplication
      DefinitionAdapters.ContextControls.coreContext
      DefinitionAdapters.ContextControls.equalityCertificates
      DefinitionAdapters.ContextControls.identityTypeRequest
      DefinitionAdapters.ContextControls.identityPredicate
      DefinitionAdapters.Controls.identityTerm
      DefinitionAdapters.ContextControls.identityType_application with
  | none =>
      have nonempty := DefinitionAdapters.ContextControls.identityType_admitted
      rw [admitted] at nonempty
      cases nonempty
  | some core =>
      simp only [admitted]
      have boolean : DefinitionAdapters.ContextControls.identityTypeRequest.existence.sequent.concl.isBoolB = true :=
        (CanonicalTerm.isBoolB_eq_true_iff _).mpr
          (CanonicalTerm.EqualityConstructionSemantics.resultIsBool
            (CanonicalTerm.equalityOfSameType_semantics _ _ rfl))
      simp only [boolean, dif_pos, Option.isSome_some]

/-- A fully instantiated model includes parameterized list carriers, the
source selector, and the genuine infinite individual carrier. -/
noncomputable def initialModel : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol :=
  model TypeFamilySemantics.Controls.initialOther
    (fun _ => TypeFamilySemantics.Controls.natural.{w})
    (pointedMeanings _ _)

theorem initialModel_fullDomains : initialModel.{w}.FullDomains := model_fullDomains _ _ _

theorem initialModel_models_eta (domain codomain : Ty) :
    initialModel.{w}.models (HOL.HOLLightStandardTheory.etaFormula domain.toHOL codomain.toHOL) :=
  model_models_eta _ _ _ _ _

theorem initialModel_models_selection (operand : Ty) :
    initialModel.{w}.models (selectionFormula operand) := models_selectionFormula _ _ _ _

noncomputable def initialModel_inhabited : initialModel.{w}.InhabitedDomains :=
  TypeFamilySemantics.model_inhabitedDomains _ _ _

def initialModel_infinity :
    initialModel.{w}.DedekindInfinityWitness TypeFamilySemantics.Controls.individual where
  successor := TypeFamilySemantics.Controls.infinityWitness.successor
  successor_admissible := initialModel_fullDomains _ _
  successor_injective := TypeFamilySemantics.Controls.infinityWitness.successor_injective
  omitted := TypeFamilySemantics.Controls.infinityWitness.omitted
  omitted_not_image := TypeFamilySemantics.Controls.infinityWitness.omitted_not_image

theorem initialModel_models_infinity :
    initialModel.{w}.models
      (HOL.StandardAxiomProperties.infinityFormula TypeFamilySemantics.Controls.individual) :=
  HOL.StandardAxiomProperties.models_infinityFormula _ _ initialModel_infinity

/-- The same constructed source-family model validates the definition-erased
readings of all three standard source commitments. Its infinite carrier and
selector are the previously constructed data, not new validity assumptions. -/
theorem initialModel_encoded_standard_commitments :
    (∀ domain codomain : Ty, initialModel.{w}.models
      (HOL.HOLLightBooleanDefinitions.etaFormula domain.toHOL codomain.toHOL)) ∧
    (∀ operand : Ty, initialModel.{w}.models (encodedSelectionFormula operand)) ∧
    initialModel.{w}.models
      (HOL.HOLLightBooleanDefinitions.infinityFormula TypeFamilySemantics.Controls.individual) :=
  ⟨fun domain codomain => HOL.HOLLightBooleanDefinitions.models_etaFormula
      initialModel domain.toHOL codomain.toHOL,
    fun operand => models_encodedSelectionFormula _ _ _ operand,
    HOL.HOLLightBooleanDefinitions.models_infinityFormula
      initialModel initialModel_fullDomains _ initialModel_infinity⟩

noncomputable def identityConstantResult : DefinitionAdapters.ContextConstantDefinitionResult :=
  Classical.choose (Option.isSome_iff_exists.mp
    DefinitionAdapters.ContextControls.identity_definition_admitted)

theorem identityConstantResult_admitted :
    DefinitionAdapters.admitConstantInTheory DefinitionAdapters.ContextControls.baseContext
      DefinitionAdapters.ContextControls.certificates (Name.global "identity")
      DefinitionAdapters.Controls.identitySource = some identityConstantResult :=
  Classical.choose_spec (Option.isSome_iff_exists.mp
    DefinitionAdapters.ContextControls.identity_definition_admitted)

noncomputable def identityConstantExtension :=
  ConstantAdmission.extension identityConstantResult initialModel.{w}

theorem identityConstantExtension_models_equation :
    identityConstantExtension.{w}.models
      (HOL.HenkinModel.definitionEquation (ConstantAdmission.body identityConstantResult)) :=
  ConstantAdmission.extension_defining_equation _ _

theorem identityConstantExtension_preserves_old_truth (sentence : HOL.ClosedFormula Symbol) :
    identityConstantExtension.{w}.models (HOL.DefinedConst.embed sentence) ↔
      initialModel.{w}.models sentence :=
  ConstantAdmission.extension_preserves_old_truth _ _ sentence

def polymorphicIdentitySource : SourceTerm :=
  .abs (Name.global "x") (.var TypeFamilySemantics.Controls.alpha)
    (.var (Name.global "x") (.var TypeFamilySemantics.Controls.alpha))

def polymorphicIdentityTerm : CanonicalTerm :=
  ⟨.abs (.var TypeFamilySemantics.Controls.alpha) (.bound 0),
    Ty.function (.var TypeFamilySemantics.Controls.alpha) (.var TypeFamilySemantics.Controls.alpha),
    by simp [DBTerm.inferType]⟩

theorem polymorphicIdentitySource_checked :
    polymorphicIdentitySource.check = some polymorphicIdentityTerm := by
  rw [SourceTerm.check_eq_some_iff]
  simp [polymorphicIdentitySource, polymorphicIdentityTerm, SourceTerm.toDB, boundIndex,
    sourceVarSame]

theorem polymorphicIdentitySource_admitted :
    checkSource DefinitionAdapters.ContextControls.coreContext.signature (fun _ _ => ⟨[]⟩)
      polymorphicIdentitySource = some polymorphicIdentityTerm := by
  simp [checkSource, polymorphicIdentitySource_checked, polymorphicIdentityTerm,
    annotationsFormedB, typeFormedB]

theorem polymorphicIdentity_definition_admitted :
    (DefinitionAdapters.admitConstantInTheory DefinitionAdapters.ContextControls.coreContext
      (fun _ _ => ⟨[]⟩) (Name.global "polymorphicIdentity") polymorphicIdentitySource).isSome = true := by
  rw [DefinitionAdapters.admitConstantInTheory_isSome_iff]
  refine ⟨polymorphicIdentityTerm, polymorphicIdentitySource_admitted, ?_, ?_⟩
  · exact TypeFormed.function _
      (DefinitionAdapters.ContextControls.core_includes.1 _ _
        DefinitionAdapters.ContextControls.function_registered)
      (by simp [TypeFormed])
      (by simp [TypeFormed])
  · refine ⟨?_, polymorphicIdentityTerm, polymorphicIdentitySource_checked, .abs .bound, ?_⟩
    · simp [DefinitionAdapters.ContextControls.coreContext,
        DefinitionAdapters.ContextControls.baseContext,
        DefinitionAdapters.ContextControls.booleanContext, DefinitionAdapters.TheoryContext.addConstant,
        DefinitionAdapters.TheoryContext.addTypeOperator, DefinitionAdapters.TheoryContext.empty,
        DefinitionAdapters.constantName, Const.equality, Name.global]
    · simp [polymorphicIdentityTerm, DBTerm.typeVariables, Ty.typeVariables,
        Ty.typeVariablesList, Ty.function]

/-- This is a real source admission, with a type parameter in both the
defining body and the public constant schema. -/
def polymorphicIdentityResult : DefinitionAdapters.ContextConstantDefinitionResult :=
  (DefinitionAdapters.admitConstantInTheory DefinitionAdapters.ContextControls.coreContext
    (fun _ _ => ⟨[]⟩)
    (Name.global "polymorphicIdentity") polymorphicIdentitySource).get
      polymorphicIdentity_definition_admitted

def functionInstance : TypeSubst := TypeSubst.ofList
  [(TypeFamilySemantics.Controls.alpha, Ty.function Ty.bool Ty.bool)]

theorem polymorphicIdentity_schema :
    polymorphicIdentityResult.definition.ty =
      Ty.function (.var TypeFamilySemantics.Controls.alpha) (.var TypeFamilySemantics.Controls.alpha) := by
  have accepted := (Option.some_get polymorphicIdentity_definition_admitted).symm
  have source := (DefinitionAdapters.admitConstantInTheory_result accepted).1
  rw [polymorphicIdentitySource_admitted] at source
  have same := Option.some.inj source
  exact (congrArg CanonicalTerm.ty same).symm

theorem polymorphicIdentity_function_schema :
    functionInstance.apply polymorphicIdentityResult.definition.ty =
      Ty.function (Ty.function Ty.bool Ty.bool) (Ty.function Ty.bool Ty.bool) := by
  rw [polymorphicIdentity_schema]
  simp [functionInstance, TypeSubst.ofList,
    TypeSubst.lookup, TypeSubst.insert, TypeSubst.empty, TypeSubst.eraseKey,
    Ty.same, Ty.function, TypeFamilySemantics.Controls.alpha]

theorem polymorphicIdentity_function_model_coherence :
    ConstantAdmission.extension polymorphicIdentityResult
        (reindexedModel functionInstance initialModel.{w}) =
      HOL.HenkinModel.standardTypeReduct functionInstance.baseInstance
        (HOL.DefinedConst.typeInstance functionInstance.baseInstance functionInstance.symbolInstance)
        (ConstantAdmission.instantiatedExtension functionInstance
          polymorphicIdentityResult initialModel.{w}) :=
  ConstantAdmission.extension_reindex _ _ _ initialModel_fullDomains

/-- The source-identity model handles all instances at once. This control
uses the actual admitted source definition and the constructed standard model. -/
theorem polymorphicIdentity_source_equation_all_instances (substitution : TypeSubst) :
    (ConstantAdmission.sourceExtension polymorphicIdentityResult initialModel.{w}).models
      (ConstantAdmission.instanceEquation polymorphicIdentityResult substitution) :=
  ConstantAdmission.sourceExtension_models_instanceEquation
    (Option.some_get polymorphicIdentity_definition_admitted).symm _ _

theorem polymorphicIdentity_source_preserves_old_truth {term : DBTerm}
    {formula : HOL.ClosedFormula Symbol}
    (formed : AnnotationsFormed DefinitionAdapters.ContextControls.coreContext.signature term)
    (translated : TranslatesCompositionally [] term .prop formula) :
    (ConstantAdmission.sourceExtension polymorphicIdentityResult initialModel.{w}).models formula ↔
      initialModel.{w}.models formula :=
  ConstantAdmission.sourceExtension_preserves_old_truth
    (Option.some_get polymorphicIdentity_definition_admitted).symm _ formed translated

theorem polymorphicIdentity_source_reindex (substitution : TypeSubst) :
    HEq ((TypeCorrectTermSubstitution.ofTypes substitution).targetMap
      (ConstantAdmission.instanceBody polymorphicIdentityResult functionInstance))
      (ConstantAdmission.instanceBody polymorphicIdentityResult
        (functionInstance.compose substitution)) :=
  ConstantAdmission.instanceBody_reindex _ _ _

theorem polymorphicIdentity_boolean_not_instance :
    ¬ ∃ substitution : TypeSubst,
      substitution.apply polymorphicIdentityResult.definition.ty = Ty.bool := by
  rintro ⟨substitution, instanceEqual⟩
  rw [polymorphicIdentity_schema, TypeSubst.apply_function] at instanceEqual
  have heads := congrArg Ty.destFunction? instanceEqual
  simp only [Ty.destFunction?_function, Ty.destFunction?_bool] at heads
  cases heads

theorem polymorphicIdentity_wrong_annotation_unexpanded :
    ConstantAdmission.sourceExpansion polymorphicIdentityResult
        (.constant polymorphicIdentityResult.output.constant Ty.bool rfl) =
      .const (.constant polymorphicIdentityResult.output.constant Ty.bool rfl) :=
  ConstantAdmission.sourceExpansion_noninstance _ _ _ polymorphicIdentity_boolean_not_instance

noncomputable def identityExtension := extension identityImage initialModel.{w}
  (identityImage_holds initialModel initialModel_fullDomains)

theorem identityExtension_preserves_old_truth (sentence : HOL.ClosedFormula Symbol) :
    identityExtension.{w}.models
      (HOL.mapTypes HOL.TypeDefinitionModel.includeBase
        HOL.TypeDefinitionModel.Symbol.old sentence) ↔ initialModel.{w}.models sentence :=
  extension_preserves_old_truth _ _ initialModel_fullDomains _ sentence

theorem identityExtension_models_first_law :
    identityExtension.{w}.models
      (HOL.TypeDefinitionModel.abstractionRepresentationLaw (Const := Symbol)
        DefinitionAdapters.Controls.identityTerm.ty.toHOL) :=
  extension_models_abstractionRepresentation _ _ _

theorem identityExtension_models_pointwise_second_law :
    identityExtension.{w}.models
      (HOL.TypeDefinitionModel.representationAbstractionPointwiseLaw
        DefinitionAdapters.Controls.identityTerm.ty.toHOL identityImage.predicateTerm) :=
  extension_models_representationAbstractionPointwise _ _ initialModel_fullDomains _

noncomputable def identityExtension_choice : identityExtension.{w}.HilbertChoice :=
  extension_choice _ _ initialModel_inhabited _

noncomputable def identityExtension_infinity :
    identityExtension.{w}.DedekindInfinityWitness (.inl TypeFamilySemantics.Controls.individual) :=
  extension_infinity _ _ initialModel_infinity _

theorem empty_carrier_not_admissible :
    ¬ Nonempty (HOL.WitnessedTypeDefinition.Carrier
      (fun _ : HOL.Ty.denote.{0, w + 1} initialModel.Carrier .prop => False)) :=
  HOL.WitnessedTypeDefinition.no_empty_definition

theorem wrong_annotation_refused : selectionOperand? selectionConstant Ty.bool = none := by
  simp [selectionOperand?, Ty.bool, Ty.destFunction?]

def sameSpellingDifferentDefinition : Const :=
  .mk (Name.global "@") (.defined (.abs (Name.global "x") Ty.bool
    (.var (Name.global "x") Ty.bool)))

/-- A same-spelled definition is not the declared primitive selector. -/
theorem definition_origin_mismatch_refused (operand : Ty) :
    selectionOperand? sameSpellingDifferentDefinition (selectionType operand) = none := by
  simp [selectionOperand?, sameSpellingDifferentDefinition, selectionConstant,
    Const.same, ConstProvenance.same]

end Controls

end Mettapedia.Languages.HOLLight.ModelInterpretation
