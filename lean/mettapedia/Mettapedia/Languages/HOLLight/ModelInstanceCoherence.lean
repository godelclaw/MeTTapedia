import Mettapedia.Languages.HOLLight.ModelAssignmentSupport
import Mettapedia.Languages.HOLLight.SourceTypeDefinitionTransport

/-!
# Coherent source instances and operator-family extensions

The constructed ordinary meanings use the inhabitant of the actual evaluated
source domain. This differs from the earlier intrinsic-HOL default construction:
the latter assigns Boolean `True`, whereas the source Boolean domain retains
`False` as its inhabitant. The difference prevents that earlier construction
from commuting with a source parameter instantiated as Boolean.

Source instantiation and fresh operator extension preserve the complete domain,
its inhabitant and its selector. Theorems below compare the original typed
symbols and their actual substitutions. Recognizing the source selection
constant requires its original declaration instance; arbitrary malformed
annotations are not granted an instantiation law.

Original constant admission propagates formed-source model agreement through
the complete chronological constant history. A subsequent actual type admission
then preserves the full preceding source language when that history is rebuilt
over the extended family table. Uniform witnessed-family construction and
type-reduct commutation through the complete constant history remain further
mixed-history obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ModelInstanceCoherence

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics ModelInterpretation SignatureFormation

universe w

/-- The retained inhabitant of the complete source type, transported into the
existing typed HOL carrier. -/
def sourceDefault (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (type : HOL.Ty AtomicTy) : HOL.Ty.denote.{0, w + 1} (atomicCarrier other assignment) type :=
  cast (congrArg (HOL.Ty.denote (atomicCarrier other assignment))
    (Ty.toHOL_fromHOL type))
    (holValue other assignment (Ty.fromHOL type)
      (evaluate (primitiveFamilies other) assignment (Ty.fromHOL type)).inhabitant)

theorem sourceDefault_inhabitant (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (type : HOL.Ty AtomicTy) :
    HEq (sourceDefault other assignment type)
      (evaluate (primitiveFamilies other) assignment (Ty.fromHOL type)).inhabitant :=
  (cast_heq _ _).trans (cast_heq _ _)

/-- Ordinary source meanings follow the evaluated source-domain data. This is
a constructed choice of interpretation, without a model-validity assumption. -/
def domainMeanings (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    Meanings other assignment := fun {type} _ => sourceDefault other assignment type

noncomputable def initialModel (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol :=
  ModelInterpretation.model other assignment (domainMeanings other assignment)

theorem initialModel_fullDomains (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    (initialModel other assignment).FullDomains := ModelInterpretation.model_fullDomains _ _ _

theorem initialModel_carrier (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    (initialModel other assignment).Carrier = atomicCarrier other assignment := rfl

theorem initialModel_models_eta (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (domain codomain : Ty) :
    (initialModel other assignment).models (HOL.HOLLightStandardTheory.etaFormula domain.toHOL codomain.toHOL) :=
  ModelInterpretation.model_models_eta other assignment (domainMeanings other assignment) domain codomain

theorem initialModel_models_selection (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (operand : Ty) : (initialModel other assignment).models (selectionFormula operand) :=
  ModelInterpretation.models_selectionFormula other assignment (domainMeanings other assignment) operand

theorem sourceDefault_domain_eq (firstOther secondOther : OperatorFamilies.{w})
    (first second : Assignment.{w}) (firstType secondType : HOL.Ty AtomicTy)
    (sameDomain : evaluate (primitiveFamilies firstOther) first (Ty.fromHOL firstType) =
      evaluate (primitiveFamilies secondOther) second (Ty.fromHOL secondType)) :
    HEq (sourceDefault firstOther first firstType) (sourceDefault secondOther second secondType) := by
  refine (sourceDefault_inhabitant _ _ _).trans ?_
  refine HEq.trans ?_ (sourceDefault_inhabitant _ _ _).symm
  exact (cast_heq (congrArg Domain.Carrier sameDomain) _).symm.trans
    (heq_of_eq (Domain.cast_inhabitant sameDomain))

theorem fromHOL_substitute (substitution : TypeSubst) (type : HOL.Ty AtomicTy) :
    Ty.fromHOL (HOL.Ty.substitute substitution.baseInstance type) =
      substitution.apply (Ty.fromHOL type) := by
  have equal := congrArg Ty.fromHOL (TypeSubst.substitute_toHOL substitution (Ty.fromHOL type))
  simpa only [Ty.toHOL_fromHOL, Ty.fromHOL_toHOL] using equal

/-- The actual ordinary symbol instance commutes with source substitution.
Its carrier changes along the original source substitution, rather than an
independently supplied comparison of values. -/
theorem domainMeanings_instance (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (substitution : TypeSubst) {type : HOL.Ty AtomicTy} (symbol : Symbol type) :
    HEq (domainMeanings other (reindex (primitiveFamilies other) substitution assignment) symbol)
      (domainMeanings other assignment (substitution.symbolInstance symbol)) := by
  apply sourceDefault_domain_eq
  rw [fromHOL_substitute, evaluate_apply]

theorem sourceSelection_instance (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (substitution : TypeSubst) (operand : Ty) :
    HEq (sourceSelection other (reindex (primitiveFamilies other) substitution assignment) operand)
      (sourceSelection other assignment (substitution.apply operand)) :=
  ModelAssignmentSupport.sourceSelection_domain_eq _ _ _ _ _ _
    (evaluate_apply _ _ _ _).symm

theorem selectionType_apply (substitution : TypeSubst) (operand : Ty) :
    substitution.apply (selectionType operand) = selectionType (substitution.apply operand) := by
  simp only [selectionType, TypeSubst.apply_function, TypeSubst.apply_bool]

/-- Original declaration admission supplies the operand of every occurrence
of the selection constant. No post-substitution recognizer is substituted for
that source licence. -/
theorem declared_selection_instance (signature : Signature) (parameter : Name)
    (registered : signature.constants selectionConstant = some (selectionType (.var parameter)))
    {annotation : Ty} (admitted : ConstantInstance signature selectionConstant annotation) :
    ∃ operand, annotation = selectionType operand := by
  obtain ⟨schema, substitution, found, equal⟩ := admitted
  have schemaEq : schema = selectionType (.var parameter) := Option.some.inj (found.symm.trans registered)
  subst schema
  exact ⟨substitution.apply (.var parameter), equal.symm.trans (selectionType_apply _ _)⟩

/-- An extension at a nonprimitive complete operator identity commutes with
the source's primitive-family interpretation. Malformed primitive applications
retain their original fallback as well. -/
theorem primitiveFamilies_extend (other : OperatorFamilies.{w}) (operator : TypeOp)
    (family : List Domain.{w} → Domain.{w}) (notBool : operator ≠ TypeOp.bool)
    (notFunction : operator ≠ TypeOp.function) :
    primitiveFamilies (extend other operator family) =
      extend (primitiveFamilies other) operator family := by
  funext candidate arguments
  by_cases boolean : candidate = TypeOp.bool
  · subst candidate
    simp [primitiveFamilies, extend, TypeOp.same_eq_true_iff, Ne.symm notBool]
  · by_cases function : candidate = TypeOp.function
    · subst candidate
      simp [primitiveFamilies, extend, TypeOp.same_eq_true_iff, boolean, Ne.symm notFunction]
    · simp [primitiveFamilies, extend, TypeOp.same_eq_true_iff, boolean, function]

/-- Every originally formed type preserves its complete evaluated domain
through the genuinely fresh source operator extension. -/
theorem domain_extend_formed (signature : Signature) (other : OperatorFamilies.{w})
    (operator : TypeOp) (family : List Domain.{w} → Domain.{w})
    (notBool : operator ≠ TypeOp.bool) (notFunction : operator ≠ TypeOp.function)
    (fresh : signature.typeOperators operator = none) (assignment : Assignment.{w})
    (type : Ty) (formed : TypeFormed signature type) :
    evaluate (primitiveFamilies (extend other operator family)) assignment type =
      evaluate (primitiveFamilies other) assignment type := by
  rw [primitiveFamilies_extend other operator family notBool notFunction]
  exact evaluate_extend_formed signature _ _ _ _ fresh type formed

theorem domainMeanings_extend_formed (signature : Signature) (other : OperatorFamilies.{w})
    (operator : TypeOp) (family : List Domain.{w} → Domain.{w})
    (notBool : operator ≠ TypeOp.bool) (notFunction : operator ≠ TypeOp.function)
    (fresh : signature.typeOperators operator = none) (assignment : Assignment.{w})
    {type : HOL.Ty AtomicTy} (symbol : Symbol type)
    (formed : TypeFormed signature (Ty.fromHOL type)) :
    HEq (domainMeanings (extend other operator family) assignment symbol)
      (domainMeanings other assignment symbol) :=
  sourceDefault_domain_eq _ _ _ _ _ _
    (domain_extend_formed signature other operator family notBool notFunction fresh assignment _ formed)

theorem sourceSelection_extend_formed (signature : Signature) (other : OperatorFamilies.{w})
    (operator : TypeOp) (family : List Domain.{w} → Domain.{w})
    (notBool : operator ≠ TypeOp.bool) (notFunction : operator ≠ TypeOp.function)
    (fresh : signature.typeOperators operator = none) (assignment : Assignment.{w})
    (operand : Ty) (formed : TypeFormed signature operand) :
    HEq (sourceSelection (extend other operator family) assignment operand)
      (sourceSelection other assignment operand) :=
  ModelAssignmentSupport.sourceSelection_domain_eq _ _ _ _ _ _
    (domain_extend_formed signature other operator family notBool notFunction fresh assignment _ formed)

theorem selectionOperand?_absent (constant : Const) (annotation : Ty)
    (different : constant ≠ selectionConstant) : selectionOperand? constant annotation = none := by
  simp [selectionOperand?, Const.same_eq_true_iff, different]

private theorem initial_constant_ordinary (other : OperatorFamilies.{w})
    (assignment : Assignment.{w}) (constant : Const) (annotation : Ty)
    {type : HOL.Ty AtomicTy} (typed : annotation.toHOL = type)
    (different : constant ≠ selectionConstant) :
    (initialModel other assignment).constDen (.constant constant annotation typed) =
      domainMeanings other assignment (.constant constant annotation typed) := by
  change interpretation other assignment (domainMeanings other assignment)
    (.constant constant annotation typed) = _
  simp only [interpretation]
  split
  · rfl
  · rename_i operand recognized
    exact False.elim (different ((selectionOperand?_eq_some_iff _ _ _).mp recognized).1)

private theorem initial_constant_typed (other : OperatorFamilies.{w})
    (assignment : Assignment.{w}) (constant : Const) (annotation : Ty)
    {left right : HOL.Ty AtomicTy} (leftTyped : annotation.toHOL = left)
    (rightTyped : annotation.toHOL = right) :
    HEq ((initialModel other assignment).constDen (.constant constant annotation leftTyped))
      ((initialModel other assignment).constDen (.constant constant annotation rightTyped)) := by
  subst left right
  rfl

private theorem initial_constant_annotations (other : OperatorFamilies.{w})
    (assignment : Assignment.{w}) (constant : Const) {first second : Ty}
    (same : first = second) {left right : HOL.Ty AtomicTy}
    (leftTyped : first.toHOL = left) (rightTyped : second.toHOL = right) :
    HEq ((initialModel other assignment).constDen (.constant constant first leftTyped))
      ((initialModel other assignment).constDen (.constant constant second rightTyped)) := by
  cases same
  exact initial_constant_typed _ _ _ _ _ _

/-- Actual free-variable symbols retain their source type-instance law. -/
theorem initial_variable_instance (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (substitution : TypeSubst) (sourceVar : SourceVar)
    {type : HOL.Ty AtomicTy} (typed : sourceVar.ty.toHOL = type) :
    HEq ((initialModel other (reindex (primitiveFamilies other) substitution assignment)).constDen
        (.variable sourceVar typed))
      ((initialModel other assignment).constDen
        (substitution.symbolInstance (.variable sourceVar typed))) :=
  domainMeanings_instance other assignment substitution (.variable sourceVar typed)

/-- Every originally admitted constant occurrence commutes with its actual
type instance. The original selection declaration prevents recognition from
appearing only after an otherwise malformed annotation is instantiated. -/
theorem initial_constant_instance (signature : Signature) (parameter : Name)
    (registered : signature.constants selectionConstant = some (selectionType (.var parameter)))
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) (substitution : TypeSubst)
    (constant : Const) (annotation : Ty) (admitted : ConstantInstance signature constant annotation)
    {type : HOL.Ty AtomicTy} (typed : annotation.toHOL = type) :
    HEq ((initialModel other (reindex (primitiveFamilies other) substitution assignment)).constDen
        (.constant constant annotation typed))
      ((initialModel other assignment).constDen
        (substitution.symbolInstance (.constant constant annotation typed))) := by
  cases typed
  by_cases selection : constant = selectionConstant
  · subst constant
    obtain ⟨operand, rfl⟩ := declared_selection_instance signature parameter registered admitted
    have first := ModelInterpretation.model_selection other
      (reindex (primitiveFamilies other) substitution assignment) (domainMeanings _ _) operand
    have second := ModelInterpretation.model_selection other assignment (domainMeanings _ _)
      (substitution.apply operand)
    refine (initial_constant_typed _ _ _ _ rfl (selectionType_toHOL operand)).trans ?_
    refine (heq_of_eq first).trans ((sourceSelection_instance other assignment substitution operand).trans ?_)
    refine (heq_of_eq second).symm.trans ?_
    simp only [TypeSubst.symbolInstance]
    exact initial_constant_annotations _ _ _ (selectionType_apply substitution operand).symm
      (selectionType_toHOL _) _
  · rw [initial_constant_ordinary _ _ _ _ _ selection]
    simp only [TypeSubst.symbolInstance]
    rw [initial_constant_ordinary _ _ _ _ _ selection]
    exact domainMeanings_instance other assignment substitution (.constant constant annotation rfl)

/-- The new initial family earns finite assignment support. It therefore
feeds the existing chronological constant-history theorem without an assumed
locality condition. -/
theorem initial_symbol_local (other : OperatorFamilies.{w}) :
    ModelAssignmentSupport.SymbolLocal (initialModel other) := by
  intro first second type symbol agree
  cases symbol with
  | «variable» sourceVar typed =>
      apply sourceDefault_domain_eq
      exact evaluate_parameter_agreement _ first second _ agree
  | constant constant annotation typed =>
      cases typed
      change HEq (interpretation other first (domainMeanings other first)
        (.constant constant annotation rfl))
        (interpretation other second (domainMeanings other second) (.constant constant annotation rfl))
      simp only [interpretation]
      split
      · apply sourceDefault_domain_eq
        exact evaluate_parameter_agreement _ first second _ agree
      · rename_i operand recognized
        have shape := (selectionOperand?_eq_some_iff _ _ _).mp recognized
        have operandAgree : ∀ name ∈ operand.typeVariables, first name = second name := by
          intro name member
          apply agree name
          rw [Ty.fromHOL_toHOL, shape.2]
          simp only [selectionType, Ty.function, Ty.typeVariables, Ty.typeVariablesList,
            Finset.mem_union]
          exact Or.inl (Or.inl member)
        exact (eqRec_heq _ _).trans
          ((ModelAssignmentSupport.sourceSelection_parameter_agreement other first second operand
            operandAgree).trans (eqRec_heq _ _).symm)

theorem history_initial_symbol_local {initial final : DefinitionAdapters.TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final)
    (other : OperatorFamilies.{w}) :
    ModelAssignmentSupport.SymbolLocal (fun assignment => history.extendModel (initialModel other assignment)) :=
  ModelAssignmentSupport.history_symbol_local history other (initialModel other)
    (fun _ => rfl) (initialModel_fullDomains other) (initial_symbol_local other)

theorem initial_symbol_extend_formed (signature : Signature) (other : OperatorFamilies.{w})
    (operator : TypeOp) (family : List Domain.{w} → Domain.{w})
    (notBool : operator ≠ TypeOp.bool) (notFunction : operator ≠ TypeOp.function)
    (fresh : signature.typeOperators operator = none) (assignment : Assignment.{w})
    {type : HOL.Ty AtomicTy} (symbol : Symbol type)
    (formed : TypeFormed signature (Ty.fromHOL type)) :
    HEq ((initialModel (extend other operator family) assignment).constDen symbol)
      ((initialModel other assignment).constDen symbol) := by
  cases symbol with
  | «variable» sourceVar typed =>
      exact domainMeanings_extend_formed signature other operator family notBool notFunction
        fresh assignment (.variable sourceVar typed) formed
  | constant constant annotation typed =>
      cases typed
      change HEq (interpretation (extend other operator family) assignment
        (domainMeanings (extend other operator family) assignment) (.constant constant annotation rfl))
        (interpretation other assignment (domainMeanings other assignment) (.constant constant annotation rfl))
      simp only [interpretation]
      split
      · exact domainMeanings_extend_formed signature other operator family notBool notFunction
          fresh assignment (.constant constant annotation rfl) formed
      · rename_i operand recognized
        have shape := (selectionOperand?_eq_some_iff _ _ _).mp recognized
        have annotationFormed : TypeFormed signature annotation := by
          simpa only [Ty.fromHOL_toHOL] using formed
        rw [shape.2] at annotationFormed
        have operandFormed := (TypeFormed.function_components signature
          (TypeFormed.function_components signature annotationFormed).1).1
        exact (eqRec_heq _ _).trans ((sourceSelection_extend_formed signature other operator family
          notBool notFunction fresh assignment operand operandFormed).trans (eqRec_heq _ _).symm)

private theorem translated_type_formed (signature : Signature)
    (functionArity : signature.typeOperators TypeOp.function = some 2)
    {context : HOL.Ctx AtomicTy} {term : DBTerm} {type : HOL.Ty AtomicTy}
    {target : HOL.Term Symbol context type} (translation : TranslatesCompositionally context term type target)
    (formed : AnnotationsFormed signature term)
    (contextFormed : ContextFormed signature (context.map Ty.fromHOL)) :
    TypeFormed signature (Ty.fromHOL type) := by
  obtain ⟨sourceType, checked, typed⟩ := translation.inferType_eq
    (context := context.map Ty.fromHOL)
    (by
      simp only [List.map_map, Function.comp_def, Ty.toHOL_fromHOL]
      exact List.map_id _)
  have sourceFormed := formed.inferredType signature functionArity contextFormed checked
  simpa only [← typed, Ty.fromHOL_toHOL] using sourceFormed

private theorem apply_heq {A A' B B' : Type (w + 1)}
    (domain : A = A') (codomain : B = B') {first : A → B} {second : A' → B'}
    {left : A} {right : A'} (functions : HEq first second) (arguments : HEq left right) :
    HEq (first left) (second right) := by
  cases domain
  cases codomain
  exact heq_of_eq (congrArg₂ (fun f x => f x) (eq_of_heq functions) (eq_of_heq arguments))

private theorem equality_heq {A B : Type (w + 1)} (carrier : A = B)
    {first second : A} {otherFirst otherSecond : B}
    (left : HEq first otherFirst) (right : HEq second otherSecond) :
    (first = second) ↔ (otherFirst = otherSecond) := by
  cases carrier
  rw [eq_of_heq left, eq_of_heq right]

private theorem eqv_iff_eq (model : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : model.FullDomains) (type : HOL.Ty AtomicTy)
    (first second : HOL.Ty.denote.{0, w + 1} model.Carrier type) :
    model.Eqv type first second ↔ first = second := by
  constructor
  · exact model.eq_of_eqv_of_fullDomains full
  · intro equal
    subst second
    exact model.eqv_refl (full type first)

set_option backward.isDefEq.respectTransparency false in
/-- Denotation comparison is restricted to the original formed source
language. In particular it retains the original constant-instance licences,
all function arguments and every open bound valuation. -/
theorem denote_formed_agreement (signature : Signature)
    (functionArity : signature.typeOperators TypeOp.function = some 2)
    (first second : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (firstFull : first.FullDomains) (secondFull : second.FullDomains)
    (carriers : ∀ type, TypeFormed signature (Ty.fromHOL type) →
      HOL.Ty.denote.{0, w + 1} first.Carrier type = HOL.Ty.denote.{0, w + 1} second.Carrier type)
    (constants : ∀ constant annotation {type} (typed : annotation.toHOL = type),
      TypeFormed signature annotation → ConstantInstance signature constant annotation →
      HEq (first.constDen (.constant constant annotation typed))
        (second.constDen (.constant constant annotation typed)))
    (variableValues : ∀ sourceVar {type} (typed : sourceVar.ty.toHOL = type),
      TypeFormed signature sourceVar.ty → HEq (first.constDen (.variable sourceVar typed))
        (second.constDen (.variable sourceVar typed)))
    {context : HOL.Ctx AtomicTy} {term : DBTerm} {type : HOL.Ty AtomicTy}
    {target : HOL.Term Symbol context type} (translation : TranslatesCompositionally context term type target) :
    AnnotationsFormed signature term → ContextFormed signature (context.map Ty.fromHOL) →
    ∀ (firstValuation : first.Valuation context) (secondValuation : second.Valuation context),
      (∀ type (index : HOL.Var context type), HEq (firstValuation index) (secondValuation index)) →
      HEq (first.denote target firstValuation) (second.denote target secondValuation) := by
  induction translation with
  | @equality context constant annotation operand type recognized typed =>
      intro formed contextFormed firstValuation secondValuation same
      cases formed with
      | constant annotationFormed declared =>
          obtain ⟨rfl, rfl⟩ := (equalityOperand?_eq_some_iff _ _ _).mp recognized
          have operandFormed := (TypeFormed.function_components signature annotationFormed).1
          have carrier := carriers type (by simpa only [← typed, Ty.fromHOL_toHOL] using operandFormed)
          change HEq (fun left right => ULift.up (first.Eqv type left right))
            (fun left right => ULift.up (second.Eqv type left right))
          apply Function.hfunext carrier
          intro left otherLeft lefts
          apply Function.hfunext carrier
          intro right otherRight rights
          apply heq_of_eq
          apply ULift.ext
          apply propext
          exact (eqv_iff_eq first firstFull type left right).trans
            ((equality_heq carrier lefts rights).trans
              (eqv_iff_eq second secondFull type otherLeft otherRight).symm)
  | constant unrecognized typed =>
      intro formed contextFormed firstValuation secondValuation same
      cases formed with
      | constant annotationFormed declared => exact constants _ _ typed annotationFormed declared
  | free typed =>
      intro formed contextFormed firstValuation secondValuation same
      cases formed with
      | free annotationFormed => exact variableValues _ typed annotationFormed
  | bound index =>
      intro formed contextFormed firstValuation secondValuation same
      exact same _ index
  | @app context function argument domain codomain functionTarget argumentTarget
      functionTranslation argumentTranslation functionIH argumentIH =>
      intro formed contextFormed firstValuation secondValuation same
      cases formed with
      | app functionFormed argumentFormed =>
          exact apply_heq
            (carriers domain (translated_type_formed signature functionArity argumentTranslation
              argumentFormed contextFormed))
            (carriers codomain (translated_type_formed signature functionArity
              (.app functionTranslation argumentTranslation) (.app functionFormed argumentFormed) contextFormed))
            (functionIH functionFormed contextFormed firstValuation secondValuation same)
            (argumentIH argumentFormed contextFormed firstValuation secondValuation same)
  | @abs context domain body type codomain bodyTarget typed bodyTranslation bodyIH =>
      intro formed contextFormed firstValuation secondValuation same
      cases formed with
      | abs domainFormed bodyFormed =>
          apply Function.hfunext (carriers type (by simpa only [← typed, Ty.fromHOL_toHOL] using domainFormed))
          intro left right values
          apply bodyIH bodyFormed
          · intro sourceType member
            simp only [List.map_cons, List.mem_cons, ← typed, Ty.fromHOL_toHOL] at member
            rcases member with rfl | old
            · exact domainFormed
            · exact contextFormed _ old
          · intro boundType index
            cases index with
            | vz => exact values
            | vs index => exact same _ index

/-- The actual source type reduct agrees with the constructed reindexed
model on every originally admitted term. The comparison does not identify
the two models on arbitrary unlicensed symbol annotations. -/
theorem initialModel_denote_reindex (signature : Signature)
    (functionArity : signature.typeOperators TypeOp.function = some 2) (parameter : Name)
    (registered : signature.constants selectionConstant = some (selectionType (.var parameter)))
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) (substitution : TypeSubst)
    {context : HOL.Ctx AtomicTy} {term : DBTerm} {type : HOL.Ty AtomicTy}
    {target : HOL.Term Symbol context type} (translation : TranslatesCompositionally context term type target)
    (formed : AnnotationsFormed signature term)
    (contextFormed : ContextFormed signature (context.map Ty.fromHOL))
    (firstValuation : (initialModel other (reindex (primitiveFamilies other) substitution assignment)).Valuation context)
    (secondValuation : (reindexedModel substitution (initialModel other assignment)).Valuation context)
    (same : ∀ type (index : HOL.Var context type), HEq (firstValuation index) (secondValuation index)) :
    HEq ((initialModel other (reindex (primitiveFamilies other) substitution assignment)).denote target firstValuation)
      ((reindexedModel substitution (initialModel other assignment)).denote target secondValuation) := by
  refine denote_formed_agreement signature functionArity _ _
    (initialModel_fullDomains _ _) (reindexedModel_fullDomains _ _)
    ?_ ?_ ?_ translation formed contextFormed firstValuation secondValuation same
  · intro targetType targetFormed
    have reductCarrier : (reindexedModel substitution (initialModel other assignment)).Carrier =
        atomicCarrier other (reindex (primitiveFamilies other) substitution assignment) := by
      simpa only [initialModel, ModelInterpretation.model] using reindexedModel_carrier other assignment
        (interpretation other assignment (domainMeanings other assignment)) substitution
    change HOL.Ty.denote (atomicCarrier other (reindex (primitiveFamilies other) substitution assignment)) targetType = _
    rw [reductCarrier]
  · intro constant annotation targetType typed annotationFormed declared
    change HEq ((initialModel other (reindex (primitiveFamilies other) substitution assignment)).constDen
      (.constant constant annotation typed))
      ((HOL.Ty.denoteSubstituteEquiv substitution.baseInstance (initialModel other assignment).Carrier targetType).symm
        ((initialModel other assignment).constDen (substitution.symbolInstance (.constant constant annotation typed))))
    exact (initial_constant_instance signature parameter registered other assignment substitution
      constant annotation declared typed).trans (HOL.Ty.denoteSubstituteEquiv_symm_apply_heq _ _ _ _).symm
  · intro sourceVar targetType typed variableFormed
    change HEq ((initialModel other (reindex (primitiveFamilies other) substitution assignment)).constDen
      (.variable sourceVar typed))
      ((HOL.Ty.denoteSubstituteEquiv substitution.baseInstance (initialModel other assignment).Carrier targetType).symm
        ((initialModel other assignment).constDen (substitution.symbolInstance (.variable sourceVar typed))))
    exact (initial_variable_instance other assignment substitution sourceVar typed).trans
      (HOL.Ty.denoteSubstituteEquiv_symm_apply_heq _ _ _ _).symm

/-- Truth of an original formed sentence follows its actual source type
instance. This law supplies the predicate/existence transport needed by a
uniform witnessed type family. -/
theorem initialModel_models_instance (signature : Signature)
    (functionArity : signature.typeOperators TypeOp.function = some 2) (parameter : Name)
    (registered : signature.constants selectionConstant = some (selectionType (.var parameter)))
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) (substitution : TypeSubst)
    {term : DBTerm} {formula : HOL.ClosedFormula Symbol}
    (translation : TranslatesCompositionally [] term .prop formula)
    (formed : AnnotationsFormed signature term) :
    (initialModel other (reindex (primitiveFamilies other) substitution assignment)).models formula ↔
      (initialModel other assignment).models
        (HOL.mapTypes substitution.baseInstance substitution.symbolInstance formula) := by
  have truth : (initialModel other (reindex (primitiveFamilies other) substitution assignment)).models formula ↔
      (reindexedModel substitution (initialModel other assignment)).models formula := by
    change ((initialModel other (reindex (primitiveFamilies other) substitution assignment)).denote formula _).down ↔
      ((reindexedModel substitution (initialModel other assignment)).denote formula _).down
    apply iff_of_eq
    apply congrArg (fun value : ULift.{w + 1, 0} Prop => value.down)
    apply eq_of_heq
    apply initialModel_denote_reindex signature functionArity parameter registered other assignment substitution
      translation formed
    · intro type member
      simp at member
    · intro type index
      nomatch index
  exact truth.trans (reindexedModel_models substitution _ (initialModel_fullDomains _ _) formula)

/-- Actual old-language denotation is preserved when the full source operator
table is extended. The stored type annotations and bound positions are not
erased in this comparison. -/
theorem initialModel_denote_extend_formed (signature : Signature)
    (functionArity : signature.typeOperators TypeOp.function = some 2)
    (other : OperatorFamilies.{w}) (operator : TypeOp) (family : List Domain.{w} → Domain.{w})
    (notBool : operator ≠ TypeOp.bool) (notFunction : operator ≠ TypeOp.function)
    (fresh : signature.typeOperators operator = none) (assignment : Assignment.{w})
    {context : HOL.Ctx AtomicTy} {term : DBTerm} {type : HOL.Ty AtomicTy}
    {target : HOL.Term Symbol context type} (translation : TranslatesCompositionally context term type target)
    (formed : AnnotationsFormed signature term)
    (contextFormed : ContextFormed signature (context.map Ty.fromHOL))
    (firstValuation : (initialModel (extend other operator family) assignment).Valuation context)
    (secondValuation : (initialModel other assignment).Valuation context)
    (same : ∀ type (index : HOL.Var context type), HEq (firstValuation index) (secondValuation index)) :
    HEq ((initialModel (extend other operator family) assignment).denote target firstValuation)
      ((initialModel other assignment).denote target secondValuation) := by
  refine denote_formed_agreement signature functionArity _ _ (initialModel_fullDomains _ _)
    (initialModel_fullDomains _ _) ?_ ?_ ?_ translation formed contextFormed
    firstValuation secondValuation same
  · intro targetType targetFormed
    rw [initialModel_carrier, initialModel_carrier]
    have domains := domain_extend_formed signature other operator family notBool notFunction fresh assignment
      (Ty.fromHOL targetType) targetFormed
    have values := (evaluate_toHOL (extend other operator family) assignment (Ty.fromHOL targetType)).symm.trans
      ((congrArg Domain.Carrier domains).trans (evaluate_toHOL other assignment (Ty.fromHOL targetType)))
    simpa only [Ty.toHOL_fromHOL] using values
  · intro constant annotation targetType typed annotationFormed declared
    apply initial_symbol_extend_formed signature other operator family notBool notFunction fresh
    simpa only [← typed, Ty.fromHOL_toHOL] using annotationFormed
  · intro sourceVar targetType typed variableFormed
    apply initial_symbol_extend_formed signature other operator family notBool notFunction fresh
    simpa only [← typed, Ty.fromHOL_toHOL] using variableFormed

theorem initialModel_models_extend_formed (signature : Signature)
    (functionArity : signature.typeOperators TypeOp.function = some 2)
    (other : OperatorFamilies.{w}) (operator : TypeOp) (family : List Domain.{w} → Domain.{w})
    (notBool : operator ≠ TypeOp.bool) (notFunction : operator ≠ TypeOp.function)
    (fresh : signature.typeOperators operator = none) (assignment : Assignment.{w})
    {term : DBTerm} {formula : HOL.ClosedFormula Symbol}
    (translation : TranslatesCompositionally [] term .prop formula)
    (formed : AnnotationsFormed signature term) :
    (initialModel (extend other operator family) assignment).models formula ↔
      (initialModel other assignment).models formula := by
  change ((initialModel (extend other operator family) assignment).denote formula _).down ↔
    ((initialModel other assignment).denote formula _).down
  apply iff_of_eq
  apply congrArg (fun value : ULift.{w + 1, 0} Prop => value.down)
  apply eq_of_heq
  apply initialModel_denote_extend_formed signature functionArity other operator family
    notBool notFunction fresh assignment translation formed
  · intro type member
    simp at member
  · intro type index
    nomatch index

/-- Complete provenance makes the admitted new operator distinct from both
reserved source operators, even if their displayed strings coincide. -/
theorem sourceOperator_nonprimitive (request : TypeOperatorDefinitionRequest) :
    SourceTypeDefinitionTransport.operator request ≠ TypeOp.bool ∧
      SourceTypeDefinitionTransport.operator request ≠ TypeOp.function := by
  constructor <;> intro same <;> cases (TypeOp.mk.inj same).2

/-- The actual source type-definition admission earns every freshness and
primitive-identity premise of old-language preservation. The new family is
arbitrary here; witnessed predicate families are a nontrivial specialization. -/
theorem admitted_initialModel_models_old
    {context : DefinitionAdapters.TheoryContext} {instances : InstanceWitnesses}
    {request : TypeOperatorDefinitionRequest}
    {result : DefinitionAdapters.SourceTypeDefinitionResult}
    (accepted : DefinitionAdapters.admitSourceTypeInTheory context instances request = some result)
    (other : OperatorFamilies.{w}) (family : List Domain.{w} → Domain.{w}) (assignment : Assignment.{w})
    {term : DBTerm} {formula : HOL.ClosedFormula Symbol}
    (translation : TranslatesCompositionally [] term .prop formula)
    (formed : AnnotationsFormed context.signature term) :
    (initialModel (extend other (SourceTypeDefinitionTransport.operator request) family) assignment).models formula ↔
      (initialModel other assignment).models formula :=
  initialModel_models_extend_formed context.signature
    (SourceTypeDefinitionTransport.admitted_function_arity accepted) other _ family
    (sourceOperator_nonprimitive request).1 (sourceOperator_nonprimitive request).2
    (SourceTypeDefinitionTransport.admitted_operator_fresh accepted) assignment translation formed

/-- Formation of the public instance earns formation of every replacement
that actually occurs in its schema. Unused entries are not granted a licence. -/
theorem formed_instance_parameter (signature : Signature) (substitution : TypeSubst)
    (schema : Ty) (formed : TypeFormed signature (substitution.apply schema))
    (parameter : Name) (occurs : parameter ∈ schema.typeVariables) :
    TypeFormed signature (substitution.apply (.var parameter)) := by
  cases schema with
  | var name =>
      have same : parameter = name := by simpa only [Ty.typeVariables, Finset.mem_singleton] using occurs
      subst parameter
      exact formed
  | op operator arguments =>
      rw [TypeSubst.apply_op] at formed
      simp only [TypeFormed] at formed
      obtain ⟨argument, member, argumentOccurs⟩ := mem_typeVariablesList parameter arguments |>.mp occurs
      exact formed_instance_parameter signature substitution argument
        (formed.2 (substitution.apply argument) (List.mem_map.mpr ⟨argument, member, rfl⟩)) parameter argumentOccurs
termination_by sizeOf schema

theorem type_instance_formed_supported (signature : Signature) (substitution : TypeSubst)
    (type : Ty) (formed : TypeFormed signature type)
    (replacements : ∀ parameter ∈ type.typeVariables,
      TypeFormed signature (substitution.apply (.var parameter))) :
    TypeFormed signature (substitution.apply type) := by
  cases type with
  | var parameter => exact replacements parameter (by simp [Ty.typeVariables])
  | op operator arguments =>
      simp only [TypeFormed] at formed
      simp only [TypeSubst.apply_op, TypeFormed, List.length_map]
      refine ⟨formed.1, ?_⟩
      intro argument member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      apply type_instance_formed_supported signature substitution original (formed.2 original originalMember)
      intro parameter occurs
      exact replacements parameter ((mem_typeVariablesList parameter arguments).mpr ⟨original, originalMember, occurs⟩)
termination_by sizeOf type

/-- Original annotation and constant-instance formation needs only the
replacement types actually occurring in the source term. This preserves the
original complete symbols, binders and declaration-instance witnesses. -/
theorem annotations_instance_formed_supported (signature : Signature) (substitution : TypeSubst)
    {term : DBTerm} (formed : AnnotationsFormed signature term)
    (replacements : ∀ parameter ∈ term.typeVariables,
      TypeFormed signature (substitution.apply (.var parameter))) :
    AnnotationsFormed signature ((TermSubst.mk substitution []).applyDB term) := by
  induction formed with
  | @constant constant annotation annotationFormed declared =>
      simp only [DBTerm.typeVariables] at replacements
      simp only [TermSubst.applyDB_const]
      exact .constant (type_instance_formed_supported signature substitution annotation annotationFormed replacements)
        (declared.substitute signature substitution)
  | @free sourceVar annotationFormed =>
      simp only [DBTerm.typeVariables] at replacements
      simp only [TermSubst.applyDB, TermSubst.lookup]
      exact .free (type_instance_formed_supported signature substitution sourceVar.ty annotationFormed replacements)
  | bound index =>
      simp only [TermSubst.applyDB_bound]
      exact .bound index
  | @app function argument functionFormed argumentFormed functionIH argumentIH =>
      simp only [DBTerm.typeVariables] at replacements
      simp only [TermSubst.applyDB_app]
      exact .app (functionIH (fun parameter occurs => replacements parameter (Finset.mem_union_left _ occurs)))
        (argumentIH (fun parameter occurs => replacements parameter (Finset.mem_union_right _ occurs)))
  | @abs domain body domainFormed bodyFormed bodyIH =>
      simp only [DBTerm.typeVariables] at replacements
      simp only [TermSubst.applyDB_abs]
      exact .abs (type_instance_formed_supported signature substitution domain domainFormed
        (fun parameter occurs => replacements parameter (Finset.mem_union_left _ occurs)))
        (bodyIH (fun parameter occurs => replacements parameter (Finset.mem_union_right _ occurs)))

/-- A formed public instance of an actually admitted constant definition
earns formation of its entire defining body. The no-hidden-parameter guard
and the original checked annotations are used; unused substitution entries
may contain unrelated malformed types without affecting the result. -/
theorem admitted_instance_body_formed
    {context : DefinitionAdapters.TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : DefinitionAdapters.ContextConstantDefinitionResult}
    (accepted : DefinitionAdapters.admitConstantInTheory context instances name source = some result)
    (substitution : TypeSubst) (publicFormed : TypeFormed context.signature (substitution.apply result.definition.ty)) :
    AnnotationsFormed context.signature (ConstantAdmission.instanceTerm result substitution).term := by
  apply annotations_instance_formed_supported context.signature substitution
    ((checkSource_sound _ _ (DefinitionAdapters.admitConstantInTheory_result accepted).1).2)
  intro parameter occurs
  exact formed_instance_parameter context.signature substitution result.definition.ty publicFormed parameter
    (ConstantAdmission.admitted_parameters_bounded accepted occurs)

/-- Source formation does not inspect the constant table. This reverse
transport is required after a genuine constant registration; signature
inclusion alone supplies only its forward direction. -/
theorem typeFormed_eq_of_operators (first second : Signature)
    (operators : first.typeOperators = second.typeOperators) (type : Ty) :
    TypeFormed first type ↔ TypeFormed second type := by
  cases type with
  | var name => simp only [TypeFormed]
  | op operator arguments =>
      simp only [TypeFormed, operators]
      constructor
      · rintro ⟨registered, children⟩
        exact ⟨registered, fun argument member =>
          (typeFormed_eq_of_operators first second operators argument).mp (children argument member)⟩
      · rintro ⟨registered, children⟩
        exact ⟨registered, fun argument member =>
          (typeFormed_eq_of_operators first second operators argument).mpr (children argument member)⟩
termination_by sizeOf type

theorem admitted_constant_signature
    {context : DefinitionAdapters.TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : DefinitionAdapters.ContextConstantDefinitionResult}
    (accepted : DefinitionAdapters.admitConstantInTheory context instances name source = some result) :
    result.context.signature = context.signature.addConstant result.output.constant result.definition.ty := by
  unfold DefinitionAdapters.admitConstantInTheory at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · split at accepted
      · split at accepted
        · cases accepted
        · rename_i result' admitted
          have same := Option.some.inj accepted
          subst result
          rw [(DefinitionAdapters.admitConstant_result admitted).2.2.1]
          rfl
      · cases accepted
    · cases accepted

/-- A comparison of actual models on the licensed source language. Its
fields are transported values and carriers, not assumed truth preservation. -/
structure SourceAgreement (signature : Signature)
    (first second : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) : Prop where
  carriers : ∀ type, TypeFormed signature (Ty.fromHOL type) →
    HOL.Ty.denote.{0, w + 1} first.Carrier type = HOL.Ty.denote.{0, w + 1} second.Carrier type
  constants : ∀ constant annotation {type} (typed : annotation.toHOL = type),
    TypeFormed signature annotation → ConstantInstance signature constant annotation →
    HEq (first.constDen (.constant constant annotation typed))
      (second.constDen (.constant constant annotation typed))
  variableValues : ∀ sourceVar {type} (typed : sourceVar.ty.toHOL = type),
    TypeFormed signature sourceVar.ty → HEq (first.constDen (.variable sourceVar typed))
      (second.constDen (.variable sourceVar typed))

theorem SourceAgreement.denote {signature : Signature}
    {first second : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol}
    (agreement : SourceAgreement signature first second)
    (functionArity : signature.typeOperators TypeOp.function = some 2)
    (firstFull : first.FullDomains) (secondFull : second.FullDomains)
    {context : HOL.Ctx AtomicTy} {term : DBTerm} {type : HOL.Ty AtomicTy}
    {target : HOL.Term Symbol context type} (translation : TranslatesCompositionally context term type target)
    (formed : AnnotationsFormed signature term)
    (contextFormed : ContextFormed signature (context.map Ty.fromHOL))
    (firstValuation : first.Valuation context) (secondValuation : second.Valuation context)
    (same : ∀ type (index : HOL.Var context type), HEq (firstValuation index) (secondValuation index)) :
    HEq (first.denote target firstValuation) (second.denote target secondValuation) :=
  denote_formed_agreement signature functionArity first second firstFull secondFull
    agreement.carriers agreement.constants agreement.variableValues translation formed contextFormed
    firstValuation secondValuation same

set_option backward.isDefEq.respectTransparency false in
/-- An actual admitted polymorphic constant extension preserves source
agreement. All parameters used by an instance of the defining body are earned
from its public formed type and the original hidden-parameter guard. -/
theorem SourceAgreement.constantExtension
    {context : DefinitionAdapters.TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : DefinitionAdapters.ContextConstantDefinitionResult}
    (accepted : DefinitionAdapters.admitConstantInTheory context instances name source = some result)
    (functionArity : context.signature.typeOperators TypeOp.function = some 2)
    {first second : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol}
    (agreement : SourceAgreement context.signature first second)
    (firstFull : first.FullDomains) (secondFull : second.FullDomains) :
    SourceAgreement result.context.signature (ConstantAdmission.sourceExtension result first)
      (ConstantAdmission.sourceExtension result second) := by
  have signatureEq := admitted_constant_signature accepted
  have operators : result.context.signature.typeOperators = context.signature.typeOperators := by
    rw [signatureEq]
    rfl
  have formedBack := fun type => typeFormed_eq_of_operators result.context.signature context.signature operators type
  refine ⟨?_, ?_, ?_⟩
  · intro type formed
    exact agreement.carriers type ((formedBack _).mp formed)
  · intro constant annotation type typed formed declared
    have priorFormed := (formedBack annotation).mp formed
    by_cases newConstant : constant = result.output.constant
    · subst constant
      obtain ⟨schema, substitution, found, equal⟩ := declared
      have registered := (DefinitionAdapters.admitConstantInTheory_result accepted).2.2.2.2.2.1
      have schemaEq : schema = result.definition.ty := Option.some.inj (found.symm.trans registered)
      subst schema
      subst annotation
      cases typed
      rw [ConstantAdmission.sourceExtension_constant_instance result
          (ConstantAdmission.admitted_parameters_bounded accepted),
        ConstantAdmission.sourceExtension_constant_instance result
          (ConstantAdmission.admitted_parameters_bounded accepted)]
      apply agreement.denote functionArity firstFull secondFull
        (ConstantAdmission.instanceBody_translated result substitution)
        (admitted_instance_body_formed accepted substitution priorFormed)
      · intro type member
        simp at member
      · intro type index
        nomatch index
    · rw [ConstantAdmission.sourceExtension_constant_other result first constant annotation typed newConstant,
        ConstantAdmission.sourceExtension_constant_other result second constant annotation typed newConstant]
      apply agreement.constants constant annotation typed priorFormed
      obtain ⟨schema, substitution, found, equal⟩ := declared
      refine ⟨schema, substitution, ?_, equal⟩
      rw [signatureEq] at found
      simpa [Signature.addConstant, Const.same_eq_true_iff, newConstant] using found
  · intro sourceVar type typed formed
    rw [ConstantAdmission.sourceExtension_eq_reduct result first,
      ConstantAdmission.sourceExtension_eq_reduct result second]
    change HEq (first.denote (ConstantAdmission.sourceExpansion result (.variable sourceVar typed))
      (fun index => nomatch index)) (second.denote (ConstantAdmission.sourceExpansion result (.variable sourceVar typed))
      (fun index => nomatch index))
    rw [ConstantAdmission.sourceExpansion_variable]
    exact agreement.variableValues sourceVar typed ((formedBack _).mp formed)

/-- Source agreement survives a complete original constant-definition history,
with every chronological source admission rather than an assumed final-model
comparison. -/
theorem SourceAgreement.constantHistory {initial final : DefinitionAdapters.TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final)
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    {first second : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol}
    (agreement : SourceAgreement initial.signature first second)
    (firstFull : first.FullDomains) (secondFull : second.FullDomains) :
    SourceAgreement final.signature (history.extendModel first) (history.extendModel second) := by
  induction history with
  | nil => exact agreement
  | snoc prior instances name source result accepted ih =>
      exact ih.constantExtension accepted
        (prior.includes.1 TypeOp.function 2 functionArity)
        (prior.fullDomains first firstFull) (prior.fullDomains second secondFull)

theorem initial_operator_agreement (signature : Signature) (other : OperatorFamilies.{w})
    (operator : TypeOp) (family : List Domain.{w} → Domain.{w})
    (notBool : operator ≠ TypeOp.bool) (notFunction : operator ≠ TypeOp.function)
    (fresh : signature.typeOperators operator = none) (assignment : Assignment.{w}) :
    SourceAgreement signature (initialModel (extend other operator family) assignment)
      (initialModel other assignment) := by
  refine ⟨?_, ?_, ?_⟩
  · intro type formed
    rw [initialModel_carrier, initialModel_carrier]
    have domains := domain_extend_formed signature other operator family notBool notFunction fresh assignment
      (Ty.fromHOL type) formed
    have values := (evaluate_toHOL (extend other operator family) assignment (Ty.fromHOL type)).symm.trans
      ((congrArg Domain.Carrier domains).trans (evaluate_toHOL other assignment (Ty.fromHOL type)))
    simpa only [Ty.toHOL_fromHOL] using values
  · intro constant annotation type typed formed declared
    apply initial_symbol_extend_formed signature other operator family notBool notFunction fresh
    simpa only [← typed, Ty.fromHOL_toHOL] using formed
  · intro sourceVar type typed formed
    apply initial_symbol_extend_formed signature other operator family notBool notFunction fresh
    simpa only [← typed, Ty.fromHOL_toHOL] using formed

theorem SourceAgreement.models {signature : Signature}
    {first second : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol}
    (agreement : SourceAgreement signature first second)
    (functionArity : signature.typeOperators TypeOp.function = some 2)
    (firstFull : first.FullDomains) (secondFull : second.FullDomains)
    {term : DBTerm} {formula : HOL.ClosedFormula Symbol}
    (translation : TranslatesCompositionally [] term .prop formula)
    (formed : AnnotationsFormed signature term) : first.models formula ↔ second.models formula := by
  change (first.denote formula _).down ↔ (second.denote formula _).down
  apply iff_of_eq
  apply congrArg (fun value : ULift.{w + 1, 0} Prop => value.down)
  apply eq_of_heq
  apply agreement.denote functionArity firstFull secondFull translation formed
  · intro type member
    simp at member
  · intro type index
    nomatch index

/-- Reconstructing all preceding constant definitions over an extended
operator table preserves their actual source meanings at every old licensed
instance. Complete definition bodies, rather than supplied final truth, earn
this comparison. -/
theorem constantHistory_operator_agreement {initial final : DefinitionAdapters.TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final)
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    (other : OperatorFamilies.{w}) (operator : TypeOp) (family : List Domain.{w} → Domain.{w})
    (notBool : operator ≠ TypeOp.bool) (notFunction : operator ≠ TypeOp.function)
    (fresh : final.signature.typeOperators operator = none) (assignment : Assignment.{w}) :
    SourceAgreement final.signature
      (history.extendModel (initialModel (extend other operator family) assignment))
      (history.extendModel (initialModel other assignment)) := by
  have initiallyFresh : initial.signature.typeOperators operator = none := by
    cases found : initial.signature.typeOperators operator with
    | none => rfl
    | some arity =>
        have finalFound := history.includes.1 operator arity found
        rw [fresh] at finalFound
        cases finalFound
  exact SourceAgreement.constantHistory history functionArity
    (initial_operator_agreement initial.signature other operator family notBool notFunction initiallyFresh assignment)
    (initialModel_fullDomains _ _) (initialModel_fullDomains _ _)

/-- A genuine source type admission after an arbitrary original constant
history preserves truth of the full preceding source language. The new
operator family may be the uniform witnessed predicate family; no pointwise
or final-history semantic conclusion is assumed. -/
theorem admitted_constantHistory_models_old
    {initial final : DefinitionAdapters.TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final)
    (functionArity : initial.signature.typeOperators TypeOp.function = some 2)
    {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest}
    {result : DefinitionAdapters.SourceTypeDefinitionResult}
    (accepted : DefinitionAdapters.admitSourceTypeInTheory final instances request = some result)
    (other : OperatorFamilies.{w}) (family : List Domain.{w} → Domain.{w}) (assignment : Assignment.{w})
    {term : DBTerm} {formula : HOL.ClosedFormula Symbol}
    (translation : TranslatesCompositionally [] term .prop formula)
    (formed : AnnotationsFormed final.signature term) :
    (history.extendModel (initialModel (extend other (SourceTypeDefinitionTransport.operator request) family) assignment)).models
      formula ↔ (history.extendModel (initialModel other assignment)).models formula :=
  (constantHistory_operator_agreement history functionArity other _ family
    (sourceOperator_nonprimitive request).1 (sourceOperator_nonprimitive request).2
    (SourceTypeDefinitionTransport.admitted_operator_fresh accepted) assignment).models
      (history.includes.1 TypeOp.function 2 functionArity)
      (history.fullDomains _ (initialModel_fullDomains _ _))
      (history.fullDomains _ (initialModel_fullDomains _ _)) translation formed

namespace Controls

def parameter : Name := Name.global "A"
def booleanInstance : TypeSubst := ⟨[(parameter, Ty.bool)]⟩
def parameterVariable : SourceVar := ⟨Name.global "x", .var parameter⟩

private theorem booleanInstance_apply : booleanInstance.apply (.var parameter) = Ty.bool := by
  exact (Ty.same_eq_true_iff _ _).mp (by decide +kernel)

/-- The earlier intrinsic-HOL default is not a coherent source instance:
the actual instantiated domain retains `False`, while the intrinsic Boolean
default supplies `True`. This concerns the existing meanings, not the kernel. -/
theorem pointed_boolean_instance_failure (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ¬ HEq ((ModelInterpretation.model other
      (reindex (primitiveFamilies other) booleanInstance assignment) (pointedMeanings _ _)).constDen
        (Symbol.ofVar parameterVariable))
      ((ModelInterpretation.model other assignment (pointedMeanings _ _)).constDen
        (booleanInstance.symbolInstance (Symbol.ofVar parameterVariable))) := by
  intro same
  have first : HEq ((ModelInterpretation.model other
      (reindex (primitiveFamilies other) booleanInstance assignment) (pointedMeanings _ _)).constDen
        (Symbol.ofVar parameterVariable)) (ULift.up (False : Prop) : ULift.{w + 1, 0} Prop) := by
    change HEq ((standardModel other (reindex (primitiveFamilies other) booleanInstance assignment)).defaultValue
      (fun atomic => (evaluate (primitiveFamilies other)
        (reindex (primitiveFamilies other) booleanInstance assignment) atomic.val).inhabitant)
      (Ty.var parameter).toHOL) _
    rw [Ty.toHOL_of_isAtomic (show (Ty.var parameter).IsAtomic from ⟨rfl, rfl⟩)]
    change HEq (evaluate (primitiveFamilies other)
      (reindex (primitiveFamilies other) booleanInstance assignment) (.var parameter)).inhabitant _
    have domains : evaluate (primitiveFamilies other)
        (reindex (primitiveFamilies other) booleanInstance assignment) (.var parameter) = proposition := by
      rw [evaluate_var]
      change evaluate (primitiveFamilies other) assignment (booleanInstance.apply (.var parameter)) = _
      rw [booleanInstance_apply, evaluate_bool]
    exact (cast_heq (congrArg Domain.Carrier domains) _).symm.trans
      (heq_of_eq (Domain.cast_inhabitant domains))
  have second : HEq ((ModelInterpretation.model other assignment (pointedMeanings _ _)).constDen
        (booleanInstance.symbolInstance (Symbol.ofVar parameterVariable)))
      (ULift.up (True : Prop) : ULift.{w + 1, 0} Prop) := by
    change HEq ((standardModel other assignment).defaultValue
      (fun atomic => (evaluate (primitiveFamilies other) assignment atomic.val).inhabitant)
      (HOL.Ty.substitute booleanInstance.baseInstance (Ty.var parameter).toHOL)) _
    rw [TypeSubst.substitute_toHOL, booleanInstance_apply, Ty.toHOL_bool]
    rfl
  have falseTrue : (False : Prop) = True :=
    congrArg ULift.down (eq_of_heq (first.symm.trans (same.trans second)))
  exact Eq.mpr falseTrue True.intro

/-- The new constructed meanings pass the same original source instance,
including the type-changing Boolean replacement. -/
theorem domain_boolean_instance (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    HEq ((initialModel other (reindex (primitiveFamilies other) booleanInstance assignment)).constDen
        (Symbol.ofVar parameterVariable))
      ((initialModel other assignment).constDen (booleanInstance.symbolInstance (Symbol.ofVar parameterVariable))) :=
  initial_variable_instance other assignment booleanInstance parameterVariable rfl

def malformedSelectionInstance : TypeSubst := ⟨[(parameter, selectionType Ty.bool)]⟩

/-- A raw selection annotation can gain recognition under substitution.
This is why the positive theorem retains original declaration admission. -/
theorem selection_recognition_requires_original_licence :
    selectionOperand? selectionConstant (.var parameter) = none ∧
      selectionOperand? selectionConstant (malformedSelectionInstance.apply (.var parameter)) = some Ty.bool := by
  constructor
  · simp [selectionOperand?, Ty.destFunction?]
  · have instanceEq : malformedSelectionInstance.apply (.var parameter) = selectionType Ty.bool :=
      (Ty.same_eq_true_iff _ _).mp (by decide +kernel)
    rw [instanceEq, selectionOperand?_selection]

/-- The original declaration judgement refuses that malformed annotation. -/
theorem malformed_selection_not_declared (signature : Signature)
    (registered : signature.constants selectionConstant = some (selectionType (.var parameter))) :
    ¬ ConstantInstance signature selectionConstant (.var parameter) := by
  intro admitted
  obtain ⟨operand, same⟩ := declared_selection_instance signature parameter registered admitted
  cases same

def unusedMalformedInstance : TypeSubst :=
  ⟨[(TypeFamilySemantics.Controls.alpha, Ty.bool),
    (Name.global "unused", .op TypeOp.function [])]⟩

def usedMalformedInstance : TypeSubst :=
  ⟨[(TypeFamilySemantics.Controls.alpha, .op TypeOp.function [])]⟩

/-- The unused malformed replacement is actually unformed in the original
signature; it is not silently counted as a legitimate source type. -/
theorem unused_replacement_unformed :
    ¬ TypeFormed DefinitionAdapters.ContextControls.coreContext.signature
      (unusedMalformedInstance.apply (.var (Name.global "unused"))) := by
  have replacement : unusedMalformedInstance.apply (.var (Name.global "unused")) =
      .op TypeOp.function [] := (Ty.same_eq_true_iff _ _).mp (by decide +kernel)
  rw [replacement]
  intro formed
  have registered := DefinitionAdapters.ContextControls.core_includes.1 TypeOp.function 2
    DefinitionAdapters.ContextControls.function_registered
  simp only [TypeFormed, List.length_nil, registered] at formed
  cases formed.1

/-- A genuine polymorphic definition still has every original body annotation
formed when the malformed entry is unused. The checked public type earns the
licence of all parameters actually occurring in its body. -/
theorem unused_malformed_entry_preserves_body_formation :
    AnnotationsFormed DefinitionAdapters.ContextControls.coreContext.signature
      (ConstantAdmission.instanceTerm ModelInterpretation.Controls.polymorphicIdentityResult
        unusedMalformedInstance).term := by
  apply admitted_instance_body_formed
    (Option.some_get ModelInterpretation.Controls.polymorphicIdentity_definition_admitted).symm
  apply (typeFormedB_eq_true_iff _ _).mp
  decide +kernel

/-- Using that malformed replacement at the public parameter is refused by
the original type-formation operation. -/
theorem used_malformed_entry_refused :
    typeFormedB DefinitionAdapters.ContextControls.coreContext.signature
      (usedMalformedInstance.apply ModelInterpretation.Controls.polymorphicIdentityResult.definition.ty) = false := by
  decide +kernel

open DefinitionAdapters.ContextControls

/-- The later type definition is accepted after the actual two-row,
dependency-bearing polymorphic constant history. -/
theorem type_after_polymorphic_history_admitted :
    (DefinitionAdapters.admitSourceTypeInTheory
      DefinitionHistoryModels.Controls.polymorphicAliasResult.context equalityCertificates identityTypeRequest).isSome = true := by
  decide +kernel

def typeAfterPolymorphicHistory : DefinitionAdapters.SourceTypeDefinitionResult :=
  (DefinitionAdapters.admitSourceTypeInTheory
    DefinitionHistoryModels.Controls.polymorphicAliasResult.context equalityCertificates identityTypeRequest).get
    type_after_polymorphic_history_admitted

theorem typeAfterPolymorphicHistory_admitted :
    DefinitionAdapters.admitSourceTypeInTheory
      DefinitionHistoryModels.Controls.polymorphicAliasResult.context equalityCertificates identityTypeRequest =
        some typeAfterPolymorphicHistory := (Option.some_get type_after_polymorphic_history_admitted).symm

/-- Rerunning both prior polymorphic definitions over any genuinely extended
family table preserves the actual alias at an admitted Boolean instance. The
later original type admission earns operator freshness. -/
theorem polymorphic_alias_preserved_by_later_type (other : OperatorFamilies.{w})
    (assignment : Assignment.{w}) (family : List Domain.{w} → Domain.{w}) :
    HEq ((DefinitionHistoryModels.Controls.polymorphicDefinitions.extendModel
      (initialModel (extend other (SourceTypeDefinitionTransport.operator identityTypeRequest) family) assignment)).constDen
      (.constant DefinitionHistoryModels.Controls.polymorphicAliasResult.output.constant
        (booleanInstance.apply DefinitionHistoryModels.Controls.polymorphicAliasResult.definition.ty) rfl))
      ((DefinitionHistoryModels.Controls.polymorphicDefinitions.extendModel (initialModel other assignment)).constDen
        (.constant DefinitionHistoryModels.Controls.polymorphicAliasResult.output.constant
          (booleanInstance.apply DefinitionHistoryModels.Controls.polymorphicAliasResult.definition.ty) rfl)) := by
  have agreement := constantHistory_operator_agreement DefinitionHistoryModels.Controls.polymorphicDefinitions
    (core_includes.1 TypeOp.function 2 function_registered) other _ family
    (sourceOperator_nonprimitive identityTypeRequest).1 (sourceOperator_nonprimitive identityTypeRequest).2
    (SourceTypeDefinitionTransport.admitted_operator_fresh typeAfterPolymorphicHistory_admitted) assignment
  apply agreement.constants
  · apply (typeFormedB_eq_true_iff _ _).mp
    decide +kernel
  · refine ⟨_, booleanInstance, ?_, rfl⟩
    exact (DefinitionAdapters.admitConstantInTheory_result
      (Option.some_get DefinitionHistoryModels.Controls.polymorphic_alias_admission).symm).2.2.2.2.2.1

end Controls

theorem SourceAgreement.restrictSignature {smaller larger : Signature}
    {first second : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol}
    (included : smaller.Includes larger) (agreement : SourceAgreement larger first second) :
    SourceAgreement smaller first second where
  carriers := fun type formed => agreement.carriers type (formed.mono included)
  constants := fun constant annotation _ typed formed declared =>
    agreement.constants constant annotation typed (formed.mono included) (declared.mono included)
  variableValues := fun sourceVar _ typed formed => agreement.variableValues sourceVar typed (formed.mono included)

end Mettapedia.Languages.HOLLight.ModelInstanceCoherence
