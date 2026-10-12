import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.PredicateNaming
import Mettapedia.OSLF.NativeTypes.Modal.NativeContinuation
import Mettapedia.OSLF.NativeTypes.Modal.NativeEventInterpretation

/-!
# Exact continuation semantics for receipt-backed native responses

The independently constructed answer map reads the specified right-hand side
of a complete operational event. Pulling the continuation's complete predicate
body back along this map gives the response guard. The common native parser
computes this exact comprehension, retaining the whole event witness.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeResponseComparison

open _root_.CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT.Topos
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open NativeLocalTypeFormers NativeLocalTypeOperations ContextualLocalUniverses
open PresheafNativePropositionReadout DisplayedPresheafComprehension
open Mettapedia.OSLF.NativeTypes.Modal NativeEventDeclarations NativeEventInterpretation
open PredicateVariables

universe u
variable {plan : Plan} {W : Type u} [Category.{u} W]

noncomputable section

abbrev patternAtInput : NativeType (inputScope (W := W)).1 :=
  (patternMeaning (W := W)).reindex
    ((NativeModel (Base (W := W))).toEmpty (inputScope (W := W)).1)

abbrev eventMeaning (index : Index plan) : NativeType (inputScope (W := W)).1 :=
  RepresentableIndexedDeclarations.fibreMeaning (eventArrow (W := W) index)

theorem pattern_at_event (index : Index plan) :
    (patternAtInput (W := W)).reindex (totalProjection (eventMeaning (W := W) index).decoded) =
      readoutType (W := W) (.target index) := by
  rw [patternAtInput, ← LocalType.reindex_comp]
  have same : totalProjection (eventMeaning (W := W) index).decoded ≫
      (NativeModel (Base (W := W))).toEmpty (inputScope (W := W)).1 =
        (NativeModel (Base (W := W))).toEmpty (eventScope (W := W) index).1 :=
    (NativeModel (Base (W := W))).toEmpty_unique _ _
  exact congrArg (LocalType.reindex (patternMeaning (W := W))) same

def targetValue (index : Index plan) :
    ((patternAtInput (W := W)).reindex
      (totalProjection (eventMeaning (W := W) index).decoded)).decoded.sections :=
  castTerm (pattern_at_event index).symm (readoutValue (W := W) (.target index))

/-- The full target section is paired with its original input context.
This preserves the dependent continuation's argument and parameter. -/
def answerMap (index : Index plan) : (eventScope (W := W) index).1 ⟶
    totalSpace (patternAtInput (W := W)).decoded :=
  sectionLift _ (targetValue index) ≫
    totalReindexMap (totalProjection (eventMeaning (W := W) index).decoded)
      (patternAtInput (W := W)).decoded

def continuationMeaning (function : (predicate (patternAtInput (W := W))).decoded.sections) :=
  nativeHolds ((functionEquiv (patternAtInput (W := W))
    (nativeOmega (totalSpace (patternAtInput (W := W)).decoded))).symm function)

def responseGuard (index : Index plan)
    (function : (predicate (patternAtInput (W := W))).decoded.sections) :=
  (continuationMeaning function).preimage (answerMap (W := W) index)

def responseMeaning (index : Index plan)
    (function : (predicate (patternAtInput (W := W))).decoded.sections) :=
  PresheafNativeStableRefinement.chosen (eventMeaning (W := W) index) (responseGuard index function)

theorem specifiedTarget_generic (index : Index plan) :
    NativeContinuation.specifiedTarget index ((.var 0 : TermExpr (symbols plan) 1).rename Fin.succ) (.var 0) =
      projection (.target index) := by
  apply congrArg (TermExpr.primitive (S := symbols plan) (.target index))
  funext position
  cases position using Fin.cases with
  | zero => rfl
  | succ position =>
      cases position using Fin.cases with
      | zero => rfl
      | succ impossible => exact Fin.elim0 impossible

theorem target_read (index : Index plan) :
    (model (W := W)).evaluateTerm (eventScope (W := W) index)
      (NativeContinuation.specifiedTarget index ((.var 0 : TermExpr (symbols plan) 1).rename Fin.succ) (.var 0)) =
      some ⟨(patternAtInput (W := W)).reindex
        (totalProjection (eventMeaning (W := W) index).decoded), targetValue index⟩ := by
  rw [specifiedTarget_generic]
  exact (projection_read (.target index)).trans
    (congrArg some (nativeValue_cast (pattern_at_event index).symm _))

theorem response_guard_read (index : Index plan) (continuation : TermExpr (symbols plan) 1)
    (function : (predicate (patternAtInput (W := W))).decoded.sections)
    (functionRead : (model (W := W)).evaluateTerm inputScope continuation =
      some ⟨predicate (patternAtInput (W := W)), function⟩) :
    (model (W := W)).evaluatePredicate (eventScope (W := W) index)
      (NativeContinuation.continuationGuard index (.var 0) continuation) =
        some (responseGuard index function) := by
  have domainWeak := (model (plan := plan) (W := W)).evaluateType_rename
    (products_substitution (Base (W := W))) (carrierType (plan := plan) .pattern 1)
    (eventScope (W := W) index) inputScope Fin.succ
    (ModelRenaming.weaken inputScope (eventMeaning (W := W) index))
    (patternAtInput (W := W)) (carrier_read (plan := plan) .pattern inputScope)
  rw [carrierType_rename] at domainWeak
  have result := FixedPointSyntax.evaluate_application (model (W := W)) (eventScope (W := W) index)
    (carrierType .pattern 2)
    ((patternAtInput (W := W)).reindex (totalProjection (eventMeaning (W := W) index).decoded))
    (continuation.rename Fin.succ)
    (NativeContinuation.specifiedTarget index ((.var 0 : TermExpr (symbols plan) 1).rename Fin.succ) (.var 0))
    (weakenFunction (patternAtInput (W := W)) function
      (totalProjection (eventMeaning (W := W) index).decoded)) (targetValue index) domainWeak
    (evaluate_function_weaken (model (W := W)) inputScope continuation
      (patternAtInput (W := W)) (eventMeaning (W := W) index) function functionRead)
    (target_read index)
  rw [FixedPointSyntax.applicationValue_holds, functionBody_substitution,
    PresheafNativePropositionSubstitution.nativeHolds_substituteNative,
    ← Subfunctor.preimage_comp] at result
  exact result

/-- The actual generated common-grammar comprehension denotes exactly the
complete event fibre satisfying the continuation at its specified RHS. -/
theorem response_type_read (index : Index plan) (continuation : TermExpr (symbols plan) 1)
    (function : (predicate (patternAtInput (W := W))).decoded.sections)
    (functionRead : (model (W := W)).evaluateTerm inputScope continuation =
      some ⟨predicate (patternAtInput (W := W)), function⟩) :
    (model (W := W)).evaluateType inputScope
      (NativeContinuation.responseType index (.var 0) continuation) =
        some (responseMeaning index function) :=
  (model (W := W)).evaluate_comprehension inputScope _ _ _ _ (event_type_read index)
    (response_guard_read index continuation function functionRead)

/-- Decoding preserves the complete event value; only the continuation's
truth proof is propositional. No receipt or origin is erased by this map. -/
def responseDecode (index : Index plan)
    (function : (predicate (patternAtInput (W := W))).decoded.sections) :=
  PresheafNativeStableRefinement.decodeIso (eventMeaning (W := W) index) (responseGuard index function)

abbrev responseValue (index : Index plan) (world : W) (input : NativeEventFibre.Input)
    (function : (predicate (patternAtInput (W := W))).decoded.sections) :=
  (responseMeaning index function).decoded.obj
    ⟨Opposite.op (RepresentableIndexedDeclarations.PresheafReadout.worldObject world),
      eventArgument index world input⟩

abbrev acceptedFibre (index : Index plan) (world : W) (input : NativeEventFibre.Input)
    (function : (predicate (patternAtInput (W := W))).decoded.sections) :=
  {value : nativeFibre index world input |
    (⟨eventArgument index world input, value⟩ : (eventScope (W := W) index).1.obj
      (Opposite.op (RepresentableIndexedDeclarations.PresheafReadout.worldObject world))) ∈
        (responseGuard index function).obj
          (Opposite.op (RepresentableIndexedDeclarations.PresheafReadout.worldObject world))}

/-- The actual comprehension decoder is a bijection on complete values,
retaining the original receipt-backed fibre rather than its endpoint. -/
def responseFibreEquiv (index : Index plan) (world : W) (input : NativeEventFibre.Input)
    (function : (predicate (patternAtInput (W := W))).decoded.sections) :
    responseValue index world input function ≃ acceptedFibre index world input function :=
  ((responseDecode index function).app
    ⟨Opposite.op (RepresentableIndexedDeclarations.PresheafReadout.worldObject world),
      eventArgument index world input⟩).toEquiv

abbrev acceptedEvent (index : Index plan) (world : W) (input : NativeEventFibre.Input)
    (function : (predicate (patternAtInput (W := W))).decoded.sections) :=
  {event : {event : NativeEventFibre.Event (schema plan index) | event.input _ = input} |
    (⟨eventArgument index world input, (nativeEventEquiv index world input).symm event⟩ :
      (eventScope (W := W) index).1.obj
        (Opposite.op (RepresentableIndexedDeclarations.PresheafReadout.worldObject world))) ∈
      (responseGuard index function).obj
        (Opposite.op (RepresentableIndexedDeclarations.PresheafReadout.worldObject world))}

/-- Composition of the earned native comprehension decoder and the earned
original-event decoder preserves all scope, premise and origin witnesses. -/
def responseEventEquiv (index : Index plan) (world : W) (input : NativeEventFibre.Input)
    (function : (predicate (patternAtInput (W := W))).decoded.sections) :
    responseValue index world input function ≃ acceptedEvent index world input function :=
  (responseFibreEquiv index world input function).trans
    (Equiv.subtypeEquiv (nativeEventEquiv index world input) (fun value => by
      change (⟨eventArgument index world input, value⟩ : (eventScope (W := W) index).1.obj
        (Opposite.op (RepresentableIndexedDeclarations.PresheafReadout.worldObject world))) ∈
          (responseGuard index function).obj
            (Opposite.op (RepresentableIndexedDeclarations.PresheafReadout.worldObject world)) ↔
        (⟨eventArgument index world input, (nativeEventEquiv index world input).symm
          (nativeEventEquiv index world input value)⟩ : (eventScope (W := W) index).1.obj
            (Opposite.op (RepresentableIndexedDeclarations.PresheafReadout.worldObject world))) ∈
          (responseGuard index function).obj
            (Opposite.op (RepresentableIndexedDeclarations.PresheafReadout.worldObject world))
      rw [Equiv.symm_apply_apply]))

theorem response_decode_encode (index : Index plan) (world : W) (input : NativeEventFibre.Input)
    (function : (predicate (patternAtInput (W := W))).decoded.sections)
    (event : acceptedEvent index world input function) :
    responseEventEquiv index world input function
      ((responseEventEquiv index world input function).symm event) = event :=
  Equiv.apply_symm_apply _ _

theorem response_encode_decode (index : Index plan) (world : W) (input : NativeEventFibre.Input)
    (function : (predicate (patternAtInput (W := W))).decoded.sections)
    (value : responseValue index world input function) :
    (responseEventEquiv index world input function).symm
      (responseEventEquiv index world input function value) = value :=
  Equiv.symm_apply_apply _ _

theorem response_target_is_specified (index : Index plan) (world : W)
    (input : NativeEventFibre.Input)
    (function : (predicate (patternAtInput (W := W))).decoded.sections)
    (value : responseValue index world input function) :
    (schema plan index).rhs? input.2 =
      some (responseEventEquiv index world input function value).val.val.target := by
  have assignment := congrArg Prod.snd
    (responseEventEquiv index world input function value).val.property
  change (responseEventEquiv index world input function value).val.val.assignment = input.2 at assignment
  rw [← assignment]
  exact (responseEventEquiv index world input function value).val.val.specified

end
end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeResponseComparison
