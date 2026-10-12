import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeConstructorReadout
import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeSourceFibres
import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeModalReadout
import Mettapedia.OSLF.NativeTypes.Generation.NativeStructuralTypes
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementGraphInterpretation

/-!
# Exact inhabitants of generated authored structural types

The actual Leibniz graph evaluates to the independent constructor operation
graph. Its native comprehension contains precisely the source-carrier value
equal to that operation at each complete contextual argument point. Binding
arguments are interpreted by their earned full function-carrier comparison.
The same meaning is retained in the common constructor-and-event model.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.Binding
open BindingSemanticAdmission Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.NativeDependent
open NativeLocalTypeFormers ContextualLocalUniverses ContextualModelTelescopes
open IntrinsicScopedConditionalPresheaf BindingFunctionArgumentComparison
open Mettapedia.GSLT.LanguageDef.MultiSortedClone

variable {language : LanguageDef}

theorem structuralType_graph (installed : NativeSignature.Installation language)
    (constructor : installed.Constructor) :
    installed.structuralType constructor =
      Refinement.graphComprehension (installed.result constructor).native
        (.primitive constructor Refinement.TermExpr.var) := by
  simp only [NativeSignature.Installation.structuralType, Refinement.graphComprehension,
    NativeSignature.Installation.graph, NativeSignature.Carrier.native_rename,
    Refinement.TermExpr.rename]
  rfl

noncomputable def structuralNative (installed : NativeSignature.Installation language)
    (admitted : Admitted language) (constructor : installed.Constructor) :
    NativeType ((constructorModel installed admitted).termParameters constructor).1 :=
  Refinement.graphNative ((constructorModel installed admitted).termType constructor)
    ((constructorModel installed admitted).termValue constructor)

theorem structuralType_read (installed : NativeSignature.Installation language)
    (admitted : Admitted language) (constructor : installed.Constructor) :
    (constructorModel installed admitted).evaluateType
      ((constructorModel installed admitted).termParameters constructor)
      (installed.structuralType constructor) =
      some (structuralNative installed admitted constructor) := by
  rw [structuralType_graph]
  exact (constructorModel installed admitted).evaluate_graphComprehension _ _ _ _ _
    (constructorModel_carrier_read installed admitted _ _)
    (constructor_primitive_read installed admitted constructor)

/-- The source theorem covers every semantic context and every complete
ordered constructor argument, rather than only selected sample terms. -/
noncomputable def structuralFibreEquiv (installed : NativeSignature.Installation language)
    (admitted : Admitted language) (constructor : installed.Constructor)
    (point : ((constructorModel installed admitted).termParameters constructor).1.Elements) :
    (structuralNative installed admitted constructor).decoded.obj point ≃
      {candidate : ((constructorModel installed admitted).termType constructor).decoded.obj point |
        candidate = ((constructorModel installed admitted).termValue constructor).val point} :=
  Refinement.graphFibreEquiv _ _ point

noncomputable def constructorCarrierTermEquiv (header : NativeSignature.Header language)
    (correct : NativeSignature.HeaderCorrect header) (context : List String)
    (arguments : (carrierScope header.parameters).1.obj
      (Opposite.op (ContextObject.ofList (algebra language).substitution.toClone context))) :
    (carrierNativeType (carrierScope header.parameters).1 (.sort header.result)).decoded.obj
        ⟨Opposite.op (ContextObject.ofList (algebra language).substitution.toClone context), arguments⟩ ≃
      Term (signature language) context language.terms[header.origin.val].category :=
  (nativeCarrierFibreEquiv (carrierScope header.parameters).1 (.sort header.result) _).trans
    (((constructorResultIso header correct).app _).toEquiv.symm.trans
      ((programsIso (algebra language) language.terms[header.origin.val].category).app _).toEquiv)

theorem constructorCarrierTermEquiv_section (admitted : Admitted language)
    (header : NativeSignature.Header language) (correct : NativeSignature.HeaderCorrect header)
    (context : List String) (arguments : (carrierScope header.parameters).1.obj
      (Opposite.op (ContextObject.ofList (algebra language).substitution.toClone context))) :
    constructorCarrierTermEquiv header correct context arguments
      ((constructorSection admitted header correct).val
        ⟨Opposite.op (ContextObject.ofList (algebra language).substitution.toClone context), arguments⟩) =
      constructorTermReadout admitted header correct context arguments := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inhabitants are compared to the independently authored constructor
term, including its original index and every contextual binding argument. -/
noncomputable def structuralTermFibreEquiv (installed : NativeSignature.Installation language)
    (admitted : Admitted language) (constructor : installed.Constructor) (context : List String)
    (arguments : (carrierScope installed.headers[constructor].parameters).1.obj
      (Opposite.op (ContextObject.ofList (algebra language).substitution.toClone context))) :
    (structuralNative installed admitted constructor).decoded.obj
        ⟨Opposite.op (ContextObject.ofList (algebra language).substitution.toClone context), arguments⟩ ≃
      {candidate : Term (signature language) context language.terms[installed.origin constructor].category |
        candidate = applyFunctionArgs (algebra language) (originalOperator admitted (installed.origin constructor))
          ((constructorArgumentsIso admitted installed.headers[constructor]
            (installed_header_correct installed constructor)).hom.app
            (Opposite.op (ContextObject.ofList (algebra language).substitution.toClone context)) arguments)} :=
  (structuralFibreEquiv installed admitted constructor _).trans
    (Equiv.subtypeEquiv
      (constructorCarrierTermEquiv installed.headers[constructor]
        (installed_header_correct installed constructor) context arguments) (fun candidate => by
      simp only [Set.mem_ofPred_eq, NativeSignature.Installation.origin]
      rw [← constructor_term_readout admitted installed.headers[constructor]
        (installed_header_correct installed constructor) context arguments]
      rw [← constructorCarrierTermEquiv_section admitted installed.headers[constructor]
        (installed_header_correct installed constructor) context arguments]
      exact (constructorCarrierTermEquiv installed.headers[constructor]
        (installed_header_correct installed constructor) context arguments).injective.eq_iff.symm))

end Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage

namespace Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeModalModel

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.TypeTheory Mettapedia.TypeTheory.Calculi.NativeDependent
open NativeLocalTypeFormers ContextualLocalUniverses ContextualModelTelescopes
open CurriedBindingLanguage BindingSemanticAdmission

variable {plan : Plan} {modal : List (NativeModalHeaders.Header plan)}

variable (installed : NativeSignature.Installation plan.snapshot.language)
    (admitted : Admitted plan.snapshot.language) (diagram : Diagram plan modal)

set_option backward.isDefEq.respectTransparency false in
theorem constructor_primitive_read (constructor : installed.Constructor) :
    (model installed admitted diagram).evaluateTerm
      (carrierScope installed.headers[constructor].parameters)
      (.primitive (.inl constructor) Refinement.TermExpr.var) =
      some ⟨carrierNativeType (carrierScope installed.headers[constructor].parameters).1
        (.sort installed.headers[constructor].result),
        constructorSection admitted installed.headers[constructor]
          (installed_header_correct installed constructor)⟩ := by
  have read := (model installed admitted diagram).evaluate_primitive
    (carrierScope installed.headers[constructor].parameters) (.inl constructor)
    Refinement.TermExpr.var (𝟙 (carrierScope installed.headers[constructor].parameters).1) (by
      intro position
      change some ((carrierScope installed.headers[constructor].parameters).2.lookup position) = _
      rw [Refinement.ScopeData.components]
      exact congrArg some (Value.substitute_identity _).symm)
  exact read.trans (congrArg some (Value.substitute_identity _))

theorem structuralType_left_graph (constructor : installed.Constructor) :
    Refinement.SignatureSum.typeLeft (T := NativeModalSignature.extraSymbols plan modal)
      (installed.structuralType constructor) =
      Refinement.graphComprehension
        (NativeModalSignature.authoredType plan installed modal (installed.result constructor) _)
        (.primitive (.inl constructor) Refinement.TermExpr.var) := by
  rw [CurriedBindingLanguage.structuralType_graph]
  simp only [Refinement.graphComprehension, NativeEquality.equal, NativeEquality.predicateType,
    Refinement.SignatureSum.typeLeft, Refinement.SignatureSum.propLeft,
    Refinement.SignatureSum.termLeft, Refinement.TermExpr.rename]
  dsimp only [NativeModalSignature.authoredType]
  simp only [← Refinement.SignatureSum.typeLeft_rename]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem structuralType_left_read (constructor : installed.Constructor) :
    (model installed admitted diagram).evaluateType
      (carrierScope installed.headers[constructor].parameters)
      (Refinement.SignatureSum.typeLeft (T := NativeModalSignature.extraSymbols plan modal)
        (installed.structuralType constructor)) =
      some (CurriedBindingLanguage.structuralNative installed admitted constructor) := by
  rw [structuralType_left_graph]
  exact (model installed admitted diagram).evaluate_graphComprehension _ _ _ _ _
    (carrier_read installed admitted diagram _ _)
    (constructor_primitive_read installed admitted diagram constructor)

end Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeModalModel
