import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.AuthoredNativeFreeExtensionReadout
import Mettapedia.CategoryTheory.InternalPredicateConstructorImage

/-!
# Native constructor and continuation witnesses in the relative fragment

The constructor graph uses the genuine dependent constructor section. The
response span uses the native event projection and specified target map.
Existential predicates recover precisely the inhabitants of the generated
native graph and response families, including their complete contextual
arguments and continuation evidence. Substitution uses actual displayed
pullbacks, and preserves the supplied native continuation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.AuthoredNativeFreeExtensionFibres

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory Mettapedia.GSLT.Core Mettapedia.GSLT.Topos
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.TypeTheory Mettapedia.TypeTheory.Calculi.NativeDependent
open NativeLocalTypeFormers ContextualLocalUniverses DisplayedPresheafComprehension
open CurriedBindingLanguage CurriedNativeModalModel
open RelativeClosedSyntax GeneratedCategory

universe u

def liftedSpan {C : Type u} [Category.{u} C]
    {events input output : Cᵒᵖ ⥤ Type u} (observe : events ⟶ input) (project : events ⟶ output) :
    InternalPredicateModalSpanComparison.Span (AsSmallYoneda.Small (Cᵒᵖ ⥤ Type u))
      ((AsSmallYoneda.up (Cᵒᵖ ⥤ Type u)).obj input)
      ((AsSmallYoneda.up (Cᵒᵖ ⥤ Type u)).obj output) where
  events := (AsSmallYoneda.up (Cᵒᵖ ⥤ Type u)).obj events
  source := (AsSmallYoneda.up (Cᵒᵖ ⥤ Type u)).map observe
  target := (AsSmallYoneda.up (Cᵒᵖ ⥤ Type u)).map project

theorem liftedSpan_predicate_read {C : Type u} [Category.{u} C]
    {events input output : Cᵒᵖ ⥤ Type u} (observe : events ⟶ input) (project : events ⟶ output)
    (post : Subfunctor output) :
    InternalPredicateModalSpanComparison.Span.possibility
      (AsSmallPredicateDoctrine.higherOrder (PresheafPredicateHigherOrder.higherOrder C)).toFirstOrder
      (liftedSpan observe project) post = (post.preimage project).image observe := rfl

def refinementImageWitnessEquiv {C : Type u} [Category.{u} C] {P : Cᵒᵖ ⥤ Type u}
    (A : NativeType P) (guard : Subfunctor (totalSpace A.decoded)) (X : Cᵒᵖ)
    (input : P.obj X) :
    (PresheafNativeStableRefinement.chosen A guard).decoded.obj ⟨X, input⟩ ≃
      {point : (totalSpace A.decoded).obj X | point ∈ guard.obj X ∧ point.1 = input} :=
  ((PresheafNativeStableRefinement.decodeIso A guard).app ⟨X, input⟩).toEquiv.trans {
    toFun := fun value => ⟨⟨input, value.val⟩, value.property, rfl⟩
    invFun := fun value => by
      rcases value with ⟨⟨base, event⟩, held, same⟩
      cases same
      exact ⟨event, held⟩
    left_inv := fun _ => rfl
    right_inv := by
      rintro ⟨⟨base, event⟩, held, same⟩
      cases same
      rfl }

theorem refinementImage_nonempty_iff {C : Type u} [Category.{u} C] {P : Cᵒᵖ ⥤ Type u}
    (A : NativeType P) (guard : Subfunctor (totalSpace A.decoded)) (X : Cᵒᵖ)
    (input : P.obj X) :
    input ∈ (guard.image (totalProjection A.decoded)).obj X ↔
      Nonempty ((PresheafNativeStableRefinement.chosen A guard).decoded.obj ⟨X, input⟩) := by
  constructor
  · rintro ⟨point, held, same⟩
    exact ⟨(refinementImageWitnessEquiv A guard X input).symm ⟨point, held, same⟩⟩
  · rintro ⟨value⟩
    let witness := refinementImageWitnessEquiv A guard X input value
    exact ⟨witness.val, witness.property.1, witness.property.2⟩

private def genericResponseWitnessEquiv {plan : Plan}
    {modal : List (NativeModalHeaders.Header plan)}
    (declarations : NativeSignature.Installation plan.snapshot.language)
    (admission : BindingSemanticAdmission.Admitted plan.snapshot.language)
    (diagram : Diagram plan modal) (index : Fin modal.length)
    (X : Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf.Base
      (algebra plan.snapshot.language))
    (input : (inputScope diagram index).1.obj X)
    (function : (PredicateVariables.predicate
      (CurriedNativeModalResponse.programAtInput diagram index)).decoded.sections) :
    (CurriedNativeModalResponse.responseMeaning declarations admission diagram index function).decoded.obj
      ⟨X, input⟩ ≃
      {point : (eventScope diagram index).1.obj X |
        point ∈ (CurriedNativeModalResponse.responseGuard declarations admission diagram index function).obj X ∧
          (totalProjection (eventNative diagram index).decoded).app X point = input} :=
  refinementImageWitnessEquiv (eventNative diagram index)
    (CurriedNativeModalResponse.responseGuard declarations admission diagram index function) X input

private theorem genericResponse_nonempty_iff {plan : Plan}
    {modal : List (NativeModalHeaders.Header plan)}
    (declarations : NativeSignature.Installation plan.snapshot.language)
    (admission : BindingSemanticAdmission.Admitted plan.snapshot.language)
    (diagram : Diagram plan modal) (index : Fin modal.length)
    (X : Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf.Base
      (algebra plan.snapshot.language))
    (input : (inputScope diagram index).1.obj X)
    (function : (PredicateVariables.predicate
      (CurriedNativeModalResponse.programAtInput diagram index)).decoded.sections) :
    input ∈ ((CurriedNativeModalResponse.responseGuard declarations admission diagram index function).image
      (totalProjection (eventNative diagram index).decoded)).obj X ↔
      Nonempty ((CurriedNativeModalResponse.responseMeaning declarations admission diagram index function).decoded.obj
        ⟨X, input⟩) :=
  refinementImage_nonempty_iff (eventNative diagram index)
    (CurriedNativeModalResponse.responseGuard declarations admission diagram index function) X input

variable (installed : AuthoredPipeline.Installed)

abbrev constructors := installed.operational.declarations
abbrev admitted := installed.operational.nativeMeaning_admitted
abbrev constructorMeaning := constructorModel (constructors installed) (admitted installed)

def structuralGraphMap (constructor : (constructors installed).Constructor) :=
  sectionLift ((constructorMeaning installed).termType constructor).decoded
    ((constructorMeaning installed).termValue constructor)

def structuralPredicate (constructor : (constructors installed).Constructor) :
    Subfunctor (totalSpace ((constructorMeaning installed).termType constructor).decoded) :=
  (⊤ : Subfunctor ((constructorMeaning installed).termParameters constructor).1).image
    (structuralGraphMap installed constructor)

theorem structural_predicate_iff (constructor : (constructors installed).Constructor)
    (X : AuthoredProgramReduction.Base installed)
    (arguments : ((constructorMeaning installed).termParameters constructor).1.obj X)
    (candidate : ((constructorMeaning installed).termType constructor).decoded.obj ⟨X, arguments⟩) :
    (⟨arguments, candidate⟩ : (totalSpace ((constructorMeaning installed).termType constructor).decoded).obj X) ∈
      (structuralPredicate installed constructor).obj X ↔
        candidate = ((constructorMeaning installed).termValue constructor).val ⟨X, arguments⟩ := by
  change (∃ input, input ∈ (⊤ : Subfunctor
    ((constructorMeaning installed).termParameters constructor).1).obj X ∧
      (⟨input, ((constructorMeaning installed).termValue constructor).val ⟨X, input⟩⟩ :
        (totalSpace ((constructorMeaning installed).termType constructor).decoded).obj X) =
          ⟨arguments, candidate⟩) ↔ _
  constructor
  · rintro ⟨input, _, same⟩
    have baseEquality := congrArg Sigma.fst same
    cases baseEquality
    exact (sigma_mk_injective same).symm
  · intro same
    exact ⟨arguments, trivial, congrArg (Sigma.mk arguments) same.symm⟩

def structuralFibreEquiv (constructor : (constructors installed).Constructor)
    (X : AuthoredProgramReduction.Base installed)
    (arguments : ((constructorMeaning installed).termParameters constructor).1.obj X) :
    (CurriedBindingLanguage.structuralNative (constructors installed) (admitted installed) constructor).decoded.obj
        ⟨X, arguments⟩ ≃
      {candidate : ((constructorMeaning installed).termType constructor).decoded.obj ⟨X, arguments⟩ |
        (⟨arguments, candidate⟩ :
          (totalSpace ((constructorMeaning installed).termType constructor).decoded).obj X) ∈
            (structuralPredicate installed constructor).obj X} :=
  (CurriedBindingLanguage.structuralFibreEquiv (constructors installed) (admitted installed) constructor _).trans
    (Equiv.subtypeEquiv (Equiv.refl _) (fun candidate =>
      (structural_predicate_iff installed constructor X arguments candidate).symm))

def structuralSyntax (constructor : (constructors installed).Constructor) :=
  AuthoredNativeFreeExtensionSyntax.sharedArrow (AuthoredProgramReduction.sourceClass installed)
    (RelativeClosedPredicateLogic.existentialRaw
      ((AuthoredProgramReduction.up installed).map (structuralGraphMap installed constructor)))

def structuralReading (constructor : (constructors installed).Constructor) :=
  AuthoredNativeFreeExtensionReadout.existentialReading installed
    ((AuthoredProgramReduction.up installed).map (structuralGraphMap installed constructor))

theorem structural_function_read (constructor : (constructors installed).Constructor) :
    structuralReading installed constructor =
      HigherOrderInternalPredicateQuantifier.existsOperation
        (AuthoredNativeFreeExtensionReadout.doctrine installed)
        ((AuthoredProgramReduction.up installed).map (structuralGraphMap installed constructor)) :=
  AuthoredNativeFreeExtensionReadout.existentialReading_complete installed _

theorem structural_root_read (constructor : (constructors installed).Constructor) :
    InternalPredicateConstructorImage.root
      (AuthoredNativeFreeExtensionReadout.doctrine installed)
      ((AuthoredProgramReduction.up installed).map (structuralGraphMap installed constructor)) =
        structuralPredicate installed constructor := rfl

abbrev programAtInput (index : Fin installed.operational.modal.length) :=
  CurriedNativeModalResponse.programAtInput installed.computedDiagram index

def responseProjection (index : Fin installed.operational.modal.length) :=
  totalProjection (eventNative installed.computedDiagram index).decoded

def responseTarget (index : Fin installed.operational.modal.length) :=
  CurriedNativeModalResponse.answerMap (constructors installed) (admitted installed)
    installed.computedDiagram index

def responseSpan (index : Fin installed.operational.modal.length) :
    InternalPredicateModalSpanComparison.Span (AuthoredProgramReduction.Category installed)
      ((AuthoredProgramReduction.up installed).obj (inputScope installed.computedDiagram index).1)
      ((AuthoredProgramReduction.up installed).obj (totalSpace (programAtInput installed index).decoded)) :=
  liftedSpan (responseProjection installed index) (responseTarget installed index)

def responseSyntax (index : Fin installed.operational.modal.length) :=
  AuthoredNativeFreeExtensionReadout.spanSyntax installed
    ((AuthoredProgramReduction.up installed).map (responseProjection installed index))
    ((AuthoredProgramReduction.up installed).map (responseTarget installed index))

def responseReading (index : Fin installed.operational.modal.length) :=
  AuthoredNativeFreeExtensionReadout.spanReading installed
    ((AuthoredProgramReduction.up installed).map (responseProjection installed index))
    ((AuthoredProgramReduction.up installed).map (responseTarget installed index))

def responsePredicate (index : Fin installed.operational.modal.length)
    (function : (Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.PredicateVariables.predicate
      (programAtInput installed index)).decoded.sections) :
    Subfunctor (inputScope installed.computedDiagram index).1 :=
  (CurriedNativeModalResponse.responseGuard (constructors installed) (admitted installed)
    installed.computedDiagram index function).image (responseProjection installed index)

def responsePost (index : Fin installed.operational.modal.length)
    (function : (Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.PredicateVariables.predicate
      (programAtInput installed index)).decoded.sections) :
    (AuthoredNativeFreeExtensionReadout.doctrine installed).Fiber
      ((AuthoredProgramReduction.up installed).obj (totalSpace (programAtInput installed index).decoded)) :=
  CurriedNativeModalResponse.continuationMeaning installed.computedDiagram index function

theorem response_span_read (index : Fin installed.operational.modal.length) :
    responseReading installed index =
      InternalPredicateModalSpanComparison.operation
        (AuthoredNativeFreeExtensionReadout.doctrine installed)
        (responseSpan installed index) :=
  AuthoredNativeFreeExtensionReadout.spanReading_complete installed _ _

theorem response_predicate_read (index : Fin installed.operational.modal.length)
    (function : (Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.PredicateVariables.predicate
      (programAtInput installed index)).decoded.sections) :
    InternalPredicateModalSpanComparison.Span.possibility
      (AuthoredNativeFreeExtensionReadout.doctrine installed).toFirstOrder
      (responseSpan installed index)
      (responsePost installed index function) = responsePredicate installed index function :=
  liftedSpan_predicate_read (responseProjection installed index) (responseTarget installed index)
    (CurriedNativeModalResponse.continuationMeaning installed.computedDiagram index function)

theorem response_predicate_iff (index : Fin installed.operational.modal.length)
    (X : AuthoredProgramReduction.Base installed)
    (input : (inputScope installed.computedDiagram index).1.obj X)
    (function : (Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.PredicateVariables.predicate
      (programAtInput installed index)).decoded.sections) :
    input ∈ (responsePredicate installed index function).obj X ↔
      Nonempty ((CurriedNativeModalResponse.responseMeaning (constructors installed) (admitted installed)
        installed.computedDiagram index function).decoded.obj ⟨X, input⟩) :=
  genericResponse_nonempty_iff (constructors installed) (admitted installed)
    installed.computedDiagram index X input function

def responseWitness (index : Fin installed.operational.modal.length)
    (X : AuthoredProgramReduction.Base installed)
    (input : (inputScope installed.computedDiagram index).1.obj X)
    (function : (Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.PredicateVariables.predicate
      (programAtInput installed index)).decoded.sections) :=
  {point : (eventScope installed.computedDiagram index).1.obj X |
    point ∈ (CurriedNativeModalResponse.responseGuard (constructors installed) (admitted installed)
      installed.computedDiagram index function).obj X ∧
        (responseProjection installed index).app X point = input}

def responseWitnessEquiv (index : Fin installed.operational.modal.length)
    (X : AuthoredProgramReduction.Base installed)
    (input : (inputScope installed.computedDiagram index).1.obj X)
    (function : (Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.PredicateVariables.predicate
      (programAtInput installed index)).decoded.sections) :
    (CurriedNativeModalResponse.responseMeaning (constructors installed) (admitted installed)
      installed.computedDiagram index function).decoded.obj ⟨X, input⟩ ≃
        responseWitness installed index X input function :=
  genericResponseWitnessEquiv (constructors installed) (admitted installed)
    installed.computedDiagram index X input function

theorem structural_constructor_present (constructor : (constructors installed).Constructor)
    (X : AuthoredProgramReduction.Base installed)
    (arguments : ((constructorMeaning installed).termParameters constructor).1.obj X) :
    (⟨arguments, ((constructorMeaning installed).termValue constructor).val ⟨X, arguments⟩⟩ :
      (totalSpace ((constructorMeaning installed).termType constructor).decoded).obj X) ∈
        (structuralPredicate installed constructor).obj X :=
  (structural_predicate_iff installed constructor X arguments _).mpr rfl

theorem structural_wrong_candidate_refused (constructor : (constructors installed).Constructor)
    (X : AuthoredProgramReduction.Base installed)
    (arguments : ((constructorMeaning installed).termParameters constructor).1.obj X)
    (candidate : ((constructorMeaning installed).termType constructor).decoded.obj ⟨X, arguments⟩)
    (different : candidate ≠ ((constructorMeaning installed).termValue constructor).val ⟨X, arguments⟩) :
    (⟨arguments, candidate⟩ : (totalSpace ((constructorMeaning installed).termType constructor).decoded).obj X) ∉
      (structuralPredicate installed constructor).obj X :=
  fun member => different ((structural_predicate_iff installed constructor X arguments candidate).mp member)

theorem generated_structural_type_read (constructor : (constructors installed).Constructor) :
    installed.generatedModel.evaluateType ((constructorMeaning installed).termParameters constructor)
      (Refinement.SignatureSum.typeLeft (Refinement.SignatureSum.typeLeft
        (Refinement.SignatureSum.typeLeft ((constructors installed).structuralType constructor)))) =
      some (CurriedBindingLanguage.structuralNative (constructors installed) (admitted installed) constructor) :=
  (installed.source_type_meaning installed.computedDiagram _ _).trans
    (CurriedNativeModalModel.structuralType_left_read (constructors installed) (admitted installed)
      installed.computedDiagram constructor)

theorem generated_response_type_read (index : Fin installed.operational.modal.length)
    (continuation : Refinement.TermExpr installed.operational.symbols 1)
    (function : (Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.PredicateVariables.predicate
      (programAtInput installed index)).decoded.sections)
    (functionRead : installed.generatedModel.evaluateTerm (inputScope installed.computedDiagram index)
      (Refinement.SignatureSum.termLeft (Refinement.SignatureSum.termLeft continuation)) =
      some ⟨Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.PredicateVariables.predicate
        (programAtInput installed index), function⟩) :
    installed.generatedModel.evaluateType (inputScope installed.computedDiagram index)
      (Refinement.SignatureSum.typeLeft (Refinement.SignatureSum.typeLeft
        (NativeModalContinuation.responseType (BindingPipeline.plan installed.operational.generated)
          (constructors installed) installed.operational.modal index (.var 0) continuation))) =
      some (CurriedNativeModalResponse.responseMeaning (constructors installed) (admitted installed)
        installed.computedDiagram index function) := by
  have sourceFunction := (installed.source_term_meaning installed.computedDiagram _ continuation).symm.trans functionRead
  exact (installed.source_type_meaning installed.computedDiagram _ _).trans
    (CurriedNativeModalResponse.response_type_read (constructors installed) (admitted installed)
      installed.computedDiagram index continuation function sourceFunction)

theorem generated_substituted_response_read (index : Fin installed.operational.modal.length)
    (continuation : Refinement.TermExpr installed.operational.symbols 1)
    (function : (Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.PredicateVariables.predicate
      (programAtInput installed index)).decoded.sections)
    (functionRead : installed.generatedModel.evaluateTerm (inputScope installed.computedDiagram index)
      (Refinement.SignatureSum.termLeft (Refinement.SignatureSum.termLeft continuation)) =
      some ⟨Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.PredicateVariables.predicate
        (programAtInput installed index), function⟩)
    {n : Nat} (context : Refinement.Scope (Worlds (AuthoredProgramReduction.language installed)) n)
    (substitution : Refinement.Substitution installed.operational.symbols 1 n)
    (represented : Refinement.ModelSubstitution (installed.sourceModel installed.computedDiagram)
      context (inputScope installed.computedDiagram index) substitution) :
    installed.generatedModel.evaluateType context
      (Refinement.SignatureSum.typeLeft (Refinement.SignatureSum.typeLeft
        (NativeModalContinuation.responseType (BindingPipeline.plan installed.operational.generated)
          (constructors installed) installed.operational.modal index
          ((.var 0 : Refinement.TermExpr installed.operational.symbols 1).substitute substitution)
          (continuation.substitute substitution)))) =
      some ((CurriedNativeModalResponse.responseMeaning (constructors installed) (admitted installed)
        installed.computedDiagram index function).reindex represented.arrow) := by
  have sourceFunction := (installed.source_term_meaning installed.computedDiagram _ continuation).symm.trans functionRead
  exact (installed.source_type_meaning installed.computedDiagram context _).trans
    (CurriedNativeModalResponse.substituted_response_type_read (constructors installed) (admitted installed)
      installed.computedDiagram index continuation function sourceFunction context substitution represented)

theorem response_baseChange (index : Fin installed.operational.modal.length)
    {context : AuthoredProgramReduction.Presheaves installed}
    (incoming : context ⟶ (inputScope installed.computedDiagram index).1)
    (function : (Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.PredicateVariables.predicate
      (programAtInput installed index)).decoded.sections) :
    (responsePredicate installed index function).preimage incoming =
      ((CurriedNativeModalResponse.responseGuard (constructors installed) (admitted installed)
        installed.computedDiagram index function).preimage
          (totalReindexMap incoming (eventNative installed.computedDiagram index).decoded)).image
            (totalProjection (reindexDisplayed incoming (eventNative installed.computedDiagram index).decoded)) :=
  image_beckChevalley
    (totalReindexMap incoming (eventNative installed.computedDiagram index).decoded)
    (totalProjection (reindexDisplayed incoming (eventNative installed.computedDiagram index).decoded))
    (responseProjection installed index) incoming
    (totalReindexMap_isPullback incoming (eventNative installed.computedDiagram index).decoded).flip
    (CurriedNativeModalResponse.responseGuard (constructors installed) (admitted installed)
      installed.computedDiagram index function)

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.AuthoredNativeFreeExtensionFibres
