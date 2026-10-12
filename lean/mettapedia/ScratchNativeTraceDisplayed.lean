import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLTraceDisplayedTerms
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLLeibnizInterface
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLLeibnizRepresentationSemantics

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

open Presentation Mettapedia.Logic HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniformListTraceTypeInterpretation
open ZFSetUniformListTraceTermInterpretation
open NativeTraceLambdaSemantics

universe u

theorem leibnizEqualityValue (a : ZFSet.{u}) (type : HOL.Ty BaseSort) :
    ZFSetUniformListTraceTermInterpretation.interpret
        (FormationSensitiveHOLLeibnizInterface.sourceEquality type)
        (emptyValuation : Valuation a []) =
      NativeHOLUniformListTraceRepresentation.equalityValue a type := by
  unfold FormationSensitiveHOLLeibnizInterface.sourceEquality
    HOLLeibnizProofComparison.Source.leibniz
    NativeHOLUniformListTraceRepresentation.equalityValue
  simp only [ZFSetUniformListTraceTermInterpretation.interpret,
    ZFSetUniformListTraceTermInterpretation.extend,
    HOL.weaken, HOL.rename, HOL.Rename.weaken,
    ZFSetHOLTypeInterpretation.holds_truth]
  apply congrArg ZFSetUniformListTraceTypeInterpretation.lam
  funext left
  apply congrArg ZFSetUniformListTraceTypeInterpretation.lam
  funext right
  apply congrArg ZFSetHOLTypeInterpretation.truth
  apply propext
  constructor
  · intro transported
    let predicate : Value a (.arr type .prop) :=
      ZFSetUniformListTraceTypeInterpretation.lam
        (fun candidate => ZFSetHOLTypeInterpretation.truth (candidate = left))
    have selected := transported predicate
    have reflexive : ZFSetHOLTypeInterpretation.holds
        (ZFSetUniformListTraceTypeInterpretation.app predicate left) := by
      simp [predicate]
    have result := selected reflexive
    have right_eq_left : right = left := by
      have result' : ZFSetHOLTypeInterpretation.holds
          (ZFSetHOLTypeInterpretation.truth (right = left)) := by
        simpa [predicate] using result
      exact (@ZFSetHOLTypeInterpretation.holds_truth.{u} (right = left)).mp result'
    exact right_eq_left.symm
  · rintro rfl
    exact fun _ assumption => assumption

example (type : HOL.Ty BaseSort) :
    HOLNaturalDeductionNativeTranslation.represent
        (FormationSensitiveHOLLeibnizInterface.sourceEquality type) =
      some (FormationSensitiveHOLLeibnizInterface.equality type) := rfl

theorem equality_denotes (a : ZFSet.{u}) {n : Nat} (context : Context.{u} n)
    (type : HOL.Ty BaseSort) :
    NativeHOLTraceDisplayedTerms.Denotes a context
      (type := .arr type (.arr type .prop))
      (Presentation.liftClosed (FormationSensitiveHOLLeibnizInterface.equality type))
      (fun _ => NativeHOLUniformListTraceRepresentation.equalityValue a type) := by
  have sourceMeaning :=
    NativeHOLUniformListTraceRepresentation.representation_square (a := a)
      (FormationSensitiveHOLLeibnizInterface.sourceEquality type)
      (show HOLNaturalDeductionNativeTranslation.represent
          (FormationSensitiveHOLLeibnizInterface.sourceEquality type) =
        some (FormationSensitiveHOLLeibnizInterface.equality type) from rfl)
  have displayed := NativeHOLTraceDisplayedTerms.display_source_denotation sourceMeaning
    context (Presentation.renSub Fin.elim0)
    (fun _ => ZFSetUniformListTraceTermInterpretation.emptyValuation)
    (fun index => nomatch index)
  apply NativeHOLTraceDisplayedTerms.Denotes.change_value
    (by simpa only [Presentation.subst_renSub, Presentation.liftClosed] using displayed)
  funext environment
  exact leibnizEqualityValue a type

example {a : ZFSet.{u}} {n : Nat} {context : Context.{u} n}
    {type : HOL.Ty BaseSort} {x y : Tower.Tm n}
    {left right : context.Environment → Value a type}
    (hx : NativeHOLTraceDisplayedTerms.Denotes a context x left)
    (hy : NativeHOLTraceDisplayedTerms.Denotes a context y right) :
    NativeHOLTraceDisplayedTerms.Denotes a context (type := .prop)
      (.app (.app
        (Presentation.liftClosed (FormationSensitiveHOLLeibnizInterface.equality type)) x) y)
      (fun environment => ZFSetHOLTypeInterpretation.truth
        (left environment = right environment)) := by
  have applied := NativeHOLTraceDisplayedTerms.Denotes.application
    (NativeHOLTraceDisplayedTerms.Denotes.application
      (equality_denotes a context type) hx) hy
  apply NativeHOLTraceDisplayedTerms.Denotes.change_value applied
  funext environment
  exact NativeHOLUniformListTraceRepresentation.equalityValue_apply
    (left environment) (right environment)

theorem expansion_trace_value {a : ZFSet.{u}} {gamma : HOL.Ctx BaseSort}
    {type : HOL.Ty BaseSort} (term : HOL.Term Symbol gamma type)
    (valuation : Valuation a gamma) :
    interpret (HOLLeibnizRepresentationSemantics.expand term) valuation =
      interpret term valuation := by
  apply (ZFSetUniformListTraceTypeInterpretation.decode a type).injective
  rw [ZFSetUniformListTraceTermInterpretation.term_agreement,
    ZFSetUniformListTraceTermInterpretation.term_agreement]
  apply (ZFSetUniformListModel.model a).eq_of_eqv_of_fullDomains
    (ZFSetUniformListModel.fullDomains a)
  apply HOLLeibnizRepresentationSemantics.expansion_meaning term
    (ZFSetUniformListModel.respects a) _
  intro objectType index
  exact ZFSetUniformListModel.fullDomains a objectType
    (ZFSetUniformListTraceTermInterpretation.decodeValuation valuation index)

theorem leibniz_representation_square {a : ZFSet.{u}}
    {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    (term : HOL.Term Symbol gamma type) {code : Tower.Tm gamma.length}
    (represented : FormationSensitiveHOLInterface.represent
      FormationSensitiveHOLLeibnizInterface.signature term = some code)
    {n : Nat} (context : Context.{u} n)
    (objects : Sub Tower.Head gamma.length n)
    (valuation : context.Environment → Valuation a gamma)
    (components : ∀ {objectType : HOL.Ty BaseSort}
      (index : HOL.Var gamma objectType),
      NativeHOLTraceDisplayedTerms.Denotes a context
        (objects (FormationSensitiveHOLInterface.variableIndex index))
        (fun environment => valuation environment index)) :
    NativeHOLTraceDisplayedTerms.Denotes a context (Presentation.subst objects code)
      (fun environment => interpret term (valuation environment)) := by
  have oldRepresented : HOLNaturalDeductionNativeTranslation.represent
      (HOLLeibnizRepresentationSemantics.expand term) = some code := by
    exact (HOLLeibnizRepresentationSemantics.representation_expand term).trans represented
  have oldMeaning := NativeHOLTraceDisplayedTerms.representation_square
    (HOLLeibnizRepresentationSemantics.expand term) oldRepresented
    context objects valuation components
  apply NativeHOLTraceDisplayedTerms.Denotes.change_value oldMeaning
  funext environment
  exact expansion_trace_value term (valuation environment)

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
