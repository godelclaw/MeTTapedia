import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeModalReadout
import Mettapedia.OSLF.NativeTypes.Generation.NativeModalContinuation
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.PredicateVariables
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSubstitutionEvaluation

/-!
# Continuation meaning in the original binding native model

The generated response type refines the complete event family with the
actual continuation applied to the event's specified target. Its evaluator
is the common constructor-and-event model. The decoder retains the whole
event and its independent input, while substitution changes the supplied
continuation and its argument in the ordinary native grammar.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeModalResponse

open _root_.CategoryTheory
open Mettapedia.TypeTheory Mettapedia.GSLT.Topos
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open NativeLocalTypeFormers NativeLocalTypeOperations ContextualLocalUniverses
open PresheafNativePropositionReadout DisplayedPresheafComprehension
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf PredicateVariables
open CurriedBindingLanguage BindingSemanticAdmission CurriedNativeModalModel

variable {plan : Plan} {modal : List (NativeModalHeaders.Header plan)}
variable (installed : NativeSignature.Installation plan.snapshot.language)
    (admitted : Admitted plan.snapshot.language) (diagram : Diagram plan modal)

noncomputable section

abbrev programAtInput (index : Fin modal.length) : NativeType (inputScope diagram index).1 :=
  carrierNativeType (inputScope diagram index).1 modal[index].program

include installed admitted in
theorem program_at_event (index : Fin modal.length) :
    (programAtInput diagram index).reindex (totalProjection (eventNative diagram index).decoded) =
      carrierNativeType (eventScope diagram index).1 modal[index].program := by
  have renamed := (model installed admitted diagram).evaluateType_rename
    (products_substitution (Worlds plan.snapshot.language))
    (NativeModalSignature.authoredType plan installed modal modal[index].program 1)
    (eventScope diagram index) (inputScope diagram index) Fin.succ
    (ModelRenaming.weaken (inputScope diagram index) (eventNative diagram index))
    (programAtInput diagram index) (carrier_read installed admitted diagram _ _)
  rw [NativeModalSignature.authoredType_rename] at renamed
  exact Option.some.inj (renamed.symm.trans (carrier_read installed admitted diagram _ _))

def targetValue (index : Fin modal.length) :
    ((programAtInput diagram index).reindex
      (totalProjection (eventNative diagram index).decoded)).decoded.sections :=
  castTerm (program_at_event installed admitted diagram index).symm
    (projectionSection diagram (.target index))

def answerMap (index : Fin modal.length) : (eventScope diagram index).1 ⟶
    totalSpace (programAtInput diagram index).decoded :=
  sectionLift _ (targetValue installed admitted diagram index) ≫
    totalReindexMap (totalProjection (eventNative diagram index).decoded)
      (programAtInput diagram index).decoded

def continuationMeaning (index : Fin modal.length)
    (function : (predicate (programAtInput diagram index)).decoded.sections) :=
  nativeHolds ((functionEquiv (programAtInput diagram index)
    (nativeOmega (totalSpace (programAtInput diagram index).decoded))).symm function)

def responseGuard (index : Fin modal.length)
    (function : (predicate (programAtInput diagram index)).decoded.sections) :=
  (continuationMeaning diagram index function).preimage (answerMap installed admitted diagram index)

def responseMeaning (index : Fin modal.length)
    (function : (predicate (programAtInput diagram index)).decoded.sections) :=
  PresheafNativeStableRefinement.chosen (eventNative diagram index)
    (responseGuard installed admitted diagram index function)

theorem specifiedTarget_generic (index : Fin modal.length) :
    NativeModalContinuation.specifiedTarget plan installed modal index
      ((.var 0 : TermExpr (NativeModalSignature.symbols plan installed modal) 1).rename Fin.succ) (.var 0) =
      nativeProjection installed (.target index) := by
  apply congrArg (TermExpr.primitive (S := NativeModalSignature.symbols plan installed modal) (.inr (.target index)))
  funext position
  cases position using Fin.cases with
  | zero => rfl
  | succ position =>
      cases position using Fin.cases with
      | zero => rfl
      | succ impossible => exact Fin.elim0 impossible

theorem target_read (index : Fin modal.length) :
    (model installed admitted diagram).evaluateTerm (eventScope diagram index)
      (NativeModalContinuation.specifiedTarget plan installed modal index
        ((.var 0 : TermExpr (NativeModalSignature.symbols plan installed modal) 1).rename Fin.succ) (.var 0)) =
      some ⟨(programAtInput diagram index).reindex
        (totalProjection (eventNative diagram index).decoded), targetValue installed admitted diagram index⟩ := by
  rw [specifiedTarget_generic]
  exact (projection_primitive_read installed admitted diagram (.target index)).trans
    (congrArg some (nativeValue_cast (program_at_event installed admitted diagram index).symm _))

theorem response_guard_read (index : Fin modal.length)
    (continuation : TermExpr (NativeModalSignature.symbols plan installed modal) 1)
    (function : (predicate (programAtInput diagram index)).decoded.sections)
    (functionRead : (model installed admitted diagram).evaluateTerm (inputScope diagram index) continuation =
      some ⟨predicate (programAtInput diagram index), function⟩) :
    (model installed admitted diagram).evaluatePredicate (eventScope diagram index)
      (NativeModalContinuation.continuationGuard plan installed modal index (.var 0) continuation) =
      some (responseGuard installed admitted diagram index function) := by
  have domainWeak := (model installed admitted diagram).evaluateType_rename
    (products_substitution (Worlds plan.snapshot.language))
    (NativeModalSignature.authoredType plan installed modal modal[index].program 1)
    (eventScope diagram index) (inputScope diagram index) Fin.succ
    (ModelRenaming.weaken (inputScope diagram index) (eventNative diagram index))
    (programAtInput diagram index) (carrier_read installed admitted diagram _ _)
  rw [NativeModalSignature.authoredType_rename] at domainWeak
  have result := FixedPointSyntax.evaluate_application (model installed admitted diagram) (eventScope diagram index)
    (NativeModalSignature.authoredType plan installed modal modal[index].program 2)
    ((programAtInput diagram index).reindex (totalProjection (eventNative diagram index).decoded))
    (continuation.rename Fin.succ)
    (NativeModalContinuation.specifiedTarget plan installed modal index
      ((.var 0 : TermExpr (NativeModalSignature.symbols plan installed modal) 1).rename Fin.succ) (.var 0))
    (weakenFunction (programAtInput diagram index) function (totalProjection (eventNative diagram index).decoded))
    (targetValue installed admitted diagram index) domainWeak
    (evaluate_function_weaken (model installed admitted diagram) (inputScope diagram index) continuation
      (programAtInput diagram index) (eventNative diagram index) function functionRead)
    (target_read installed admitted diagram index)
  rw [FixedPointSyntax.applicationValue_holds, functionBody_substitution,
    PresheafNativePropositionSubstitution.nativeHolds_substituteNative,
    ← Subfunctor.preimage_comp] at result
  exact result

theorem response_type_read (index : Fin modal.length)
    (continuation : TermExpr (NativeModalSignature.symbols plan installed modal) 1)
    (function : (predicate (programAtInput diagram index)).decoded.sections)
    (functionRead : (model installed admitted diagram).evaluateTerm (inputScope diagram index) continuation =
      some ⟨predicate (programAtInput diagram index), function⟩) :
    (model installed admitted diagram).evaluateType (inputScope diagram index)
      (NativeModalContinuation.responseType plan installed modal index (.var 0) continuation) =
      some (responseMeaning installed admitted diagram index function) :=
  (model installed admitted diagram).evaluate_comprehension (inputScope diagram index) _ _ _ _
    (event_type_read installed admitted diagram index)
    (response_guard_read installed admitted diagram index continuation function functionRead)

theorem substituted_response_type_read (index : Fin modal.length)
    (continuation : TermExpr (NativeModalSignature.symbols plan installed modal) 1)
    (function : (predicate (programAtInput diagram index)).decoded.sections)
    (functionRead : (model installed admitted diagram).evaluateTerm (inputScope diagram index) continuation =
      some ⟨predicate (programAtInput diagram index), function⟩)
    {n : Nat} (context : Scope (Worlds plan.snapshot.language) n)
    (substitution : Substitution (NativeModalSignature.symbols plan installed modal) 1 n)
    (represented : ModelSubstitution (model installed admitted diagram) context
      (inputScope diagram index) substitution) :
    (model installed admitted diagram).evaluateType context
      (NativeModalContinuation.responseType plan installed modal index
        ((.var 0 : TermExpr (NativeModalSignature.symbols plan installed modal) 1).substitute substitution)
        (continuation.substitute substitution)) =
      some ((responseMeaning installed admitted diagram index function).reindex represented.arrow) := by
  have read := (model installed admitted diagram).evaluateType_substitute
    (products_substitution (Worlds plan.snapshot.language))
    (NativeModalContinuation.responseType plan installed modal index (.var 0) continuation)
    context (inputScope diagram index) substitution represented
    (responseMeaning installed admitted diagram index function)
    (response_type_read installed admitted diagram index continuation function functionRead)
  rw [NativeModalContinuation.responseType_substitute] at read
  have nativeSubstitution : (NativeModel (Worlds plan.snapshot.language)).toCwf.tySub
      (responseMeaning installed admitted diagram index function) represented.arrow =
      (responseMeaning installed admitted diagram index function).reindex represented.arrow := rfl
  exact read.trans (congrArg some nativeSubstitution)

def responseDecode (index : Fin modal.length)
    (function : (predicate (programAtInput diagram index)).decoded.sections) :=
  PresheafNativeStableRefinement.decodeIso (eventNative diagram index)
    (responseGuard installed admitted diagram index function)

abbrev responseValue (index : Fin modal.length) (X : Base (algebra plan.snapshot.language))
    (input : (diagram.input index).obj X)
    (function : (predicate (programAtInput diagram index)).decoded.sections) :=
  (responseMeaning installed admitted diagram index function).decoded.obj
    ⟨X, (inputIso diagram index).inv.app X input⟩

abbrev acceptedFibre (index : Fin modal.length) (X : Base (algebra plan.snapshot.language))
    (input : (diagram.input index).obj X)
    (function : (predicate (programAtInput diagram index)).decoded.sections) :=
  {value : nativeEventFibre diagram index X input |
    (⟨(inputIso diagram index).inv.app X input, value⟩ : (eventScope diagram index).1.obj X) ∈
      (responseGuard installed admitted diagram index function).obj X}

def responseFibreEquiv (index : Fin modal.length) (X : Base (algebra plan.snapshot.language))
    (input : (diagram.input index).obj X)
    (function : (predicate (programAtInput diagram index)).decoded.sections) :
    responseValue installed admitted diagram index X input function ≃
      acceptedFibre installed admitted diagram index X input function :=
  ((responseDecode installed admitted diagram index function).app
    ⟨X, (inputIso diagram index).inv.app X input⟩).toEquiv

abbrev acceptedEvent (index : Fin modal.length) (X : Base (algebra plan.snapshot.language))
    (input : (diagram.input index).obj X)
    (function : (predicate (programAtInput diagram index)).decoded.sections) :=
  {event : {event : (diagram.events index).obj X | (diagram.observe index).app X event = input} |
    (⟨(inputIso diagram index).inv.app X input,
      (eventFibreEquiv diagram index X input).symm event⟩ : (eventScope diagram index).1.obj X) ∈
      (responseGuard installed admitted diagram index function).obj X}

def responseEventEquiv (index : Fin modal.length) (X : Base (algebra plan.snapshot.language))
    (input : (diagram.input index).obj X)
    (function : (predicate (programAtInput diagram index)).decoded.sections) :
    responseValue installed admitted diagram index X input function ≃
      acceptedEvent installed admitted diagram index X input function :=
  (responseFibreEquiv installed admitted diagram index X input function).trans
    (Equiv.subtypeEquiv (eventFibreEquiv diagram index X input) (fun value => by
      change (⟨(inputIso diagram index).inv.app X input, value⟩ : (eventScope diagram index).1.obj X) ∈
          (responseGuard installed admitted diagram index function).obj X ↔
        (⟨(inputIso diagram index).inv.app X input,
          (eventFibreEquiv diagram index X input).symm (eventFibreEquiv diagram index X input value)⟩ :
            (eventScope diagram index).1.obj X) ∈ (responseGuard installed admitted diagram index function).obj X
      rw [Equiv.symm_apply_apply]))

theorem response_decode_encode (index : Fin modal.length) (X : Base (algebra plan.snapshot.language))
    (input : (diagram.input index).obj X)
    (function : (predicate (programAtInput diagram index)).decoded.sections)
    (event : acceptedEvent installed admitted diagram index X input function) :
    responseEventEquiv installed admitted diagram index X input function
      ((responseEventEquiv installed admitted diagram index X input function).symm event) = event :=
  Equiv.apply_symm_apply _ _

theorem response_encode_decode (index : Fin modal.length) (X : Base (algebra plan.snapshot.language))
    (input : (diagram.input index).obj X)
    (function : (predicate (programAtInput diagram index)).decoded.sections)
    (value : responseValue installed admitted diagram index X input function) :
    (responseEventEquiv installed admitted diagram index X input function).symm
      (responseEventEquiv installed admitted diagram index X input function value) = value :=
  Equiv.symm_apply_apply _ _

end
end Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeModalResponse
