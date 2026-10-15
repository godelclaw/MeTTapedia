import Mettapedia.OSLF.NativeTypes.Generation.AuthoredBindingNativeModel
import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeModalResponse

/-!
# Original source and specified target in the common native evaluator

The computed closed semantic gate supplies the actual binding-event diagram.
Decoding its native projection sections recovers the original source and the
complete receipt's specified target in every ambient context. The target is
the authored reduct retained by that event, rather than an unspecified
successor of the source.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredBindingNativeReadout

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf
open Mettapedia.OSLF.NativeTypes.Modal
open CurriedBindingLanguage AuthoredBindingNativeModel
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.PredicateVariables

variable (installed : BindingPipeline.Installed) (closed : checkClosed installed = true)
include closed

private theorem checked : check installed = true :=
  (check_exact installed).mpr ((checkClosed_exact installed).mp closed).2

private theorem freeEmpty :
    (BindingPipeline.plan installed.generated).snapshot.free =
      Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty :=
  ((checkClosed_exact installed).mp closed).1

private def shapes := checkedHeaders installed (checked installed closed)

set_option backward.isDefEq.respectTransparency false in
theorem source_readout (index : Fin installed.modal.length)
    (X : Base (algebra (BindingPipeline.plan installed.generated).snapshot.language))
    (value : (CurriedNativeModalModel.eventScope (closedDiagram installed closed) index).1.obj X) :
    (NativeBindingModalDiagram.programIso (shapes installed closed index)).hom.app X
      (((carrierSectionEquiv (CurriedNativeModalModel.eventScope (closedDiagram installed closed) index).1
        (NativeModalSignature.projectionCarrier _ installed.modal (.source index)))
          (CurriedNativeModalModel.projectionSection (closedDiagram installed closed) (.source index))).app X value) =
      ((CurriedNativeModalModel.eventIso (closedDiagram installed closed) index).hom.app X value).point.val.source := by
  have read := CurriedNativeModalModel.projection_readout
    (closedDiagram installed closed) (.source index) X value
  exact (congrArg ((NativeBindingModalDiagram.programIso (shapes installed closed index)).hom.app X) read).trans
    (NativeBindingModalDiagram.source_read _ (shapes installed closed index)
      (freeEmpty installed closed) ((check_exact installed).mp (checked installed closed)).operational X _)

set_option backward.isDefEq.respectTransparency false in
theorem target_readout (index : Fin installed.modal.length)
    (X : Base (algebra (BindingPipeline.plan installed.generated).snapshot.language))
    (value : (CurriedNativeModalModel.eventScope (closedDiagram installed closed) index).1.obj X) :
    toPattern ((NativeBindingModalDiagram.programIso (shapes installed closed index)).hom.app X
      (((carrierSectionEquiv (CurriedNativeModalModel.eventScope (closedDiagram installed closed) index).1
        (NativeModalSignature.projectionCarrier _ installed.modal (.target index)))
          (CurriedNativeModalModel.projectionSection (closedDiagram installed closed) (.target index))).app X value)) =
      ((CurriedNativeModalModel.eventIso (closedDiagram installed closed) index).hom.app X value).point.val.receipt.target := by
  have read := CurriedNativeModalModel.projection_readout
    (closedDiagram installed closed) (.target index) X value
  exact (congrArg (fun target => toPattern
    ((NativeBindingModalDiagram.programIso (shapes installed closed index)).hom.app X target)) read).trans
    (NativeBindingModalDiagram.target_read _ (shapes installed closed index)
      (freeEmpty installed closed) ((check_exact installed).mp (checked installed closed)).operational
      installed.nativeMeaning_admitted installed.distinctLabels X _)

theorem response_type_read (index : Fin installed.modal.length)
    (continuation : TermExpr installed.symbols 1)
    (function : (predicate (CurriedNativeModalResponse.programAtInput (closedDiagram installed closed) index)).decoded.sections)
    (functionRead : (model installed (freeEmpty installed closed) (checked installed closed)).evaluateTerm
      (CurriedNativeModalModel.inputScope (closedDiagram installed closed) index) continuation =
      some ⟨predicate (CurriedNativeModalResponse.programAtInput (closedDiagram installed closed) index), function⟩) :
    (model installed (freeEmpty installed closed) (checked installed closed)).evaluateType
      (CurriedNativeModalModel.inputScope (closedDiagram installed closed) index)
      (NativeModalContinuation.responseType (BindingPipeline.plan installed.generated)
        installed.declarations installed.modal index (.var 0) continuation) =
      some (CurriedNativeModalResponse.responseMeaning installed.declarations installed.nativeMeaning_admitted
        (closedDiagram installed closed) index function) :=
  CurriedNativeModalResponse.response_type_read installed.declarations installed.nativeMeaning_admitted
    (closedDiagram installed closed) index continuation function functionRead

theorem substituted_response_type_read (index : Fin installed.modal.length)
    (continuation : TermExpr installed.symbols 1)
    (function : (predicate (CurriedNativeModalResponse.programAtInput (closedDiagram installed closed) index)).decoded.sections)
    (functionRead : (model installed (freeEmpty installed closed) (checked installed closed)).evaluateTerm
      (CurriedNativeModalModel.inputScope (closedDiagram installed closed) index) continuation =
      some ⟨predicate (CurriedNativeModalResponse.programAtInput (closedDiagram installed closed) index), function⟩)
    {n : Nat} (context : Scope (Worlds (BindingPipeline.plan installed.generated).snapshot.language) n)
    (substitution : Substitution installed.symbols 1 n)
    (represented : ModelSubstitution (model installed (freeEmpty installed closed) (checked installed closed)) context
      (CurriedNativeModalModel.inputScope (closedDiagram installed closed) index) substitution) :
    (model installed (freeEmpty installed closed) (checked installed closed)).evaluateType context
      (NativeModalContinuation.responseType (BindingPipeline.plan installed.generated)
        installed.declarations installed.modal index ((.var 0 : TermExpr installed.symbols 1).substitute substitution)
        (continuation.substitute substitution)) =
      some ((CurriedNativeModalResponse.responseMeaning installed.declarations installed.nativeMeaning_admitted
        (closedDiagram installed closed) index function).reindex represented.arrow) :=
  CurriedNativeModalResponse.substituted_response_type_read installed.declarations installed.nativeMeaning_admitted
    (closedDiagram installed closed) index continuation function functionRead context substitution represented

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredBindingNativeReadout
