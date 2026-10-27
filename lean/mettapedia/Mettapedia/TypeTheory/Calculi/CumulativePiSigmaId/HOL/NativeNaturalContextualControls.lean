import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalContextualConstructors
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalAnnotatedReindexingControls

/-!
# Contextual natural conversion with changing dependent types and annotations

The controls use the original natural declarations. They include a type-valued
beta step inside a product and a lambda domain, a natural computation beneath
a lambda binder, and an argument computation in the original dependent
successor method. The latter derives the target's typing at the source's
displayed result type.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
namespace AnnotatedConversion.Contextual.Controls

open Mettapedia.Logic
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Annotated NativeNaturalVectorFamilies
open AnnotatedConversion.Controls AnnotatedConversion.ReindexingControls

def typeBeta : BetaInstance operations profile [] .nil where
  contextFormed := .nil
  domain := .const natName
  body := .const natName
  argument := .const zeroName
  family := .head (.sort Tower.zero)
  domainLevel := .sort Tower.zero
  productLevel := .sort (.max Tower.zero (.succ Tower.zero))
  domainUniverse := .sort _
  productUniverse := .sort _
  domainTyped := Programs.Annotated.Functions.natural_typed profile
  productTyped := .piForm (Programs.Annotated.Functions.natural_typed profile) (.sort _)
    (.headType (.sort _)) (.sort _) (.sorts _ _)
  bodyTyped := Programs.Annotated.Functions.natural_typed profile
  argumentTyped := Programs.Annotated.Functions.zero_typed profile
  domainCarrier := operations.number
  resultCarrier := .arr operations.number .prop
  domainCode := HOL.PredicateProducts.full operations.number
  bodyCode := HOL.PredicateProducts.full operations.number
  argumentCode := operations.zero
  domainReading := .natural
  bodyReading := .natural
  argumentReading := .zero

def typeProof : Proof operations profile profile typeBeta.source typeBeta.target
    (SourceCertificates.emit (.step (Step.beta (enabled := profile) typeBeta))).code :=
  .base (.step (.beta typeBeta))

def zeroBody : State operations profile
    ⟨[operations.number], .snoc .nil typeBeta.source.term, .const natName, operations.number⟩ where
  contextFormed := .snoc .nil ⟨.sort Tower.zero, .sort _, typeBeta.source.typed⟩
  term := .const zeroName
  typed := Programs.Annotated.Functions.zero_typed profile
  code := HOL.weaken operations.zero
  reading := .zero

def naturalFamily : State operations profile
    ⟨[operations.number], .snoc .nil typeBeta.source.term, .head (.sort Tower.zero), .arr operations.number .prop⟩ where
  contextFormed := zeroBody.contextFormed
  term := .const natName
  typed := Programs.Annotated.Functions.natural_typed profile
  code := HOL.PredicateProducts.full operations.number
  reading := .natural

theorem lambdaType_formed : CTyped (Programs.Annotated.church profile) .nil
    (.pi typeBeta.source.term (.const natName)) (.head (.sort (.max Tower.zero Tower.zero))) :=
  .piForm typeBeta.source.typed (.sort _) naturalFamily.typed (.sort _) (.sorts _ _)

def annotationProof := Proof.lam (.sort Tower.zero) lambdaType_formed (.sort _)
  typeProof (Proof.refl (enabled := profile) zeroBody)

def productProof := Proof.pi (.sort Tower.zero) (.sort Tower.zero) (.sorts Tower.zero Tower.zero)
  typeProof (Proof.refl (enabled := profile) naturalFamily)

theorem annotation_work : annotationProof.work = 1 := by
  simp [annotationProof, Proof.lam, Proof.work, typeProof, BubbleElaboration.stepCount_step]

theorem annotation_code_work :
    (StructuralConversionCode.Code.congLam
      (.refl zeroBody.term.erase : SourceCertificates.Code 1)).stepCount = 0 := by rfl

theorem annotation_erasure_agrees :
    (abstractionSource typeBeta.source zeroBody (.sort _) lambdaType_formed (.sort _)).term.erase =
      (abstractionTarget typeBeta.source typeBeta.target zeroBody zeroBody (.sort _) lambdaType_formed (.sort _)
        typeProof.sourceEqual (.refl zeroBody.typed)).term.erase := rfl

theorem annotation_terms_differ :
    (abstractionSource typeBeta.source zeroBody (.sort _) lambdaType_formed (.sort _)).term ≠
      (abstractionTarget typeBeta.source typeBeta.target zeroBody zeroBody (.sort _) lambdaType_formed (.sort _)
        typeProof.sourceEqual (.refl zeroBody.typed)).term := by
  intro same
  cases same

def naturalDomain : State operations profile
    ⟨operations.parameters, Row.zero.context operations, .head (.sort Tower.zero), .arr operations.number .prop⟩ where
  contextFormed := zeroInstance.contextFormed
  term := .const natName
  typed := Programs.Annotated.Functions.natural_typed profile
  code := HOL.PredicateProducts.full operations.number
  reading := .natural

theorem weakened_result_formed : CTyped (Programs.Annotated.church profile)
    (Row.successor.context operations) (zeroInstance.index.sourceType.subst weaken.source)
    (.head (.sort AnnotatedConversion.Controls.resultLevel)) := by
  simpa only [zeroInstance, canonical, Instance.index, CTm.subst_ids, CTm.subst, Row.parameters] using
    AnnotatedConversion.Controls.result_formed.substitute weaken.typed

theorem open_lambda_formed : CTyped (Programs.Annotated.church profile) (Row.zero.context operations)
    (.pi naturalDomain.term (zeroInstance.index.sourceType.subst weaken.source))
    (.head (.sort (.max Tower.zero AnnotatedConversion.Controls.resultLevel))) :=
  .piForm naturalDomain.typed (.sort _) weakened_result_formed (.sort _) (.sorts _ _)

def underBinder := Proof.lam (.sort _) open_lambda_formed (.sort _)
  (Proof.refl (enabled := profile) naturalDomain) (Proof.base weakenedPath)

def numberBeta : BetaInstance operations profile operations.successorParameters (Row.successor.context operations) where
  contextFormed := successorInstance.contextFormed
  domain := .const natName
  body := .var 0
  argument := openNumber.term
  family := .const natName
  domainLevel := .sort Tower.zero
  productLevel := .sort (.max Tower.zero Tower.zero)
  domainUniverse := .sort _
  productUniverse := .sort _
  domainTyped := Programs.Annotated.Functions.natural_typed profile
  productTyped := .piForm (Programs.Annotated.Functions.natural_typed profile) (.sort _)
    (Programs.Annotated.Functions.natural_typed profile) (.sort _) (.sorts _ _)
  bodyTyped := .var 0
  argumentTyped := openNumber.typed
  domainCarrier := operations.number
  resultCarrier := operations.number
  domainCode := HOL.PredicateProducts.full operations.number
  bodyCode := .var .vz
  argumentCode := openNumber.code
  domainReading := .natural
  bodyReading := AnnotatedReads.var (Γ := operations.number :: operations.successorParameters) .vz
  argumentReading := openNumber.reading

/-- The codomain of the original successor method in its four-variable
caller context, with predecessor and recursive-result binders retained. -/
def methodFamily : CTm Tower.Head 5 :=
  .pi (.app (.var 4) (.var 0)) (.app (.var 5) (.app (.const succName) (.var 1)))

def methodState : State operations profile
    ⟨operations.successorParameters, Row.successor.context operations,
      .pi (.const natName) methodFamily, operations.methodType⟩ where
  contextFormed := successorInstance.contextFormed
  term := .var ⟨1, by decide⟩
  typed := by
    have shape : (Row.successor.context operations).lookup (⟨1, by decide⟩ : Fin 4) =
        CTm.pi (.const natName) methodFamily := by rfl
    change CTyped (Programs.Annotated.church profile) (Row.successor.context operations)
      (.var (⟨1, by decide⟩ : Fin 4)) (.pi (.const natName) methodFamily)
    rw [← shape]
    exact .var (⟨1, by decide⟩ : Fin 4)
  code := .var (.vs .vz)
  reading := AnnotatedReads.var (Γ := operations.successorParameters) (.vs .vz)

def numberProof : Proof operations profile profile numberBeta.source numberBeta.target
    (SourceCertificates.emit (.step (Step.beta (enabled := profile) numberBeta))).code :=
  .base (.step (.beta numberBeta))

def dependentApplication := Proof.app (Proof.refl (enabled := profile) methodState) numberProof

theorem displayed_types_differ :
    CTm.inst0 numberBeta.source.term methodFamily ≠ CTm.inst0 numberBeta.target.term methodFamily := by
  intro same
  cases same

theorem dependent_target_typed : CTyped (Programs.Annotated.church profile) (Row.successor.context operations)
    (.app methodState.term numberBeta.target.term) (CTm.inst0 numberBeta.source.term methodFamily) :=
  (applicationTarget methodState methodState numberBeta.source numberBeta.target
    (.refl methodState.typed) numberProof.sourceEqual).typed

def annotationHOL := annotationProof.hol
def productHOL := productProof.hol
def underBinderHOL := underBinder.hol
def dependentHOL := dependentApplication.hol

theorem annotation_hol_free : annotationHOL.FunctionExtensionalityFree := annotationProof.hol_free
theorem product_hol_free : productHOL.FunctionExtensionalityFree := productProof.hol_free
theorem binder_hol_free : underBinderHOL.FunctionExtensionalityFree := underBinder.hol_free
theorem dependent_hol_free : dependentHOL.FunctionExtensionalityFree := dependentApplication.hol_free

/-- Directly exercise predicate-product congruence with the non-reflexive
type-valued beta equation and the independently represented natural family. -/
def predicateProductProof := HOL.PredicateProducts.congruence typeProof.hol
  (HOL.ProofSyntax.eqRefl (Δ := HOL.weakenHyps (σ := operations.number) (assumptions operations []))
    naturalFamily.code)

theorem predicate_product_free : predicateProductProof.FunctionExtensionalityFree :=
  HOL.PredicateProducts.congruence_free typeProof.hol
    (HOL.ProofSyntax.eqRefl (Δ := HOL.weakenHyps (σ := operations.number) (assumptions operations []))
      naturalFamily.code) typeProof.hol_free True.intro

theorem under_binder_bound : underBinder.certificate.code.stepCount ≤ underBinder.work :=
  underBinder.erased_work_le

theorem annotation_checked : annotationProof.certificate.code.check Tower.rules.headEq
    (Programs.ComputationProfiles.decoder profile).decode
    (abstractionSource typeBeta.source zeroBody (.sort _) lambdaType_formed (.sort _)).term.erase
    (abstractionTarget typeBeta.source typeBeta.target zeroBody zeroBody (.sort _) lambdaType_formed (.sort _)
      typeProof.sourceEqual (.refl zeroBody.typed)).term.erase = true := annotationProof.checked

theorem product_checked : productProof.certificate.code.check Tower.rules.headEq
    (Programs.ComputationProfiles.decoder profile).decode
    (productSource typeBeta.source naturalFamily (.sort _) (.sort _) (.sorts _ _)).term.erase
    (productTarget typeBeta.source typeBeta.target naturalFamily naturalFamily (.sort _) (.sort _) (.sorts _ _)
      typeProof.sourceEqual (.refl naturalFamily.typed)).term.erase = true := productProof.checked

theorem annotation_work_gap : annotationProof.certificate.code.stepCount < annotationProof.work := by
  rw [annotation_work]
  exact Nat.zero_lt_succ 0

theorem product_work : productProof.certificate.code.stepCount = 1 := by
  simp [Proof.certificate, StructuralConversionCode.Code.congPi,
    StructuralConversionCode.Code.stepCount, StructuralConversionCode.Code.stepCount_mapContext,
    SourceCertificates.emit_work, BubbleElaboration.stepCount_step]

theorem dependent_work : dependentApplication.work = 1 := by
  simp [dependentApplication, Proof.app, Proof.work, numberProof, BubbleElaboration.stepCount_step]

theorem forged_product_refused : productProof.certificate.code.check Tower.rules.headEq
    (Programs.ComputationProfiles.decoder profile).decode
    (.pi typeBeta.source.term.erase (.const natName)) (.const natName) = false := by
  decide +kernel

#print axioms annotation_work
#print axioms annotation_terms_differ
#print axioms underBinder
#print axioms dependentApplication
#print axioms displayed_types_differ
#print axioms dependent_target_typed
#print axioms product_hol_free
#print axioms annotation_checked
#print axioms product_checked
#print axioms annotation_work_gap
#print axioms forged_product_refused

end AnnotatedConversion.Contextual.Controls
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
