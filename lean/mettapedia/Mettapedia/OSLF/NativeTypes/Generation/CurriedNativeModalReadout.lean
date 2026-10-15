import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeModalModel

/-!
# Complete operational readouts of the common native model

Native event comprehension recovers actual complete events, not only their
targets. The native evaluator returns the generated primitive's actual
dependent section. Decoding that section gives the original natural event
projection, and the input square preserves its conditioning data.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeModalModel

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.NativeDependent
open NativeLocalTypeFormers ContextualLocalUniverses
open DisplayedPresheafComprehension
open Mettapedia.TypeTheory.ContextualModelTelescopes
open CurriedBindingLanguage BindingSemanticAdmission

variable {plan : Plan} {installed : NativeSignature.Installation plan.snapshot.language}
    {modal : List (NativeModalHeaders.Header plan)}

variable (installed : NativeSignature.Installation plan.snapshot.language)
    (admitted : Admitted plan.snapshot.language) (diagram : Diagram plan modal)

def nativeProjection (projectionSymbol : NativeModalSignature.Projection plan modal) :
    Refinement.TermExpr (NativeModalSignature.symbols plan installed modal) 2 :=
  .primitive (.inr projectionSymbol) Refinement.TermExpr.var

set_option backward.isDefEq.respectTransparency false in
theorem projection_primitive_read (projectionSymbol : NativeModalSignature.Projection plan modal) :
    (model installed admitted diagram).evaluateTerm (eventScope diagram projectionSymbol.index)
      (nativeProjection installed projectionSymbol) =
      some ⟨carrierNativeType (eventScope diagram projectionSymbol.index).1
        (NativeModalSignature.projectionCarrier plan modal projectionSymbol),
        projectionSection diagram projectionSymbol⟩ := by
  have read := (model installed admitted diagram).evaluate_primitive
    (eventScope diagram projectionSymbol.index) (.inr projectionSymbol)
    Refinement.TermExpr.var (𝟙 (eventScope diagram projectionSymbol.index).1) (by
      intro position
      change (model installed admitted diagram).evaluateTerm (eventScope diagram projectionSymbol.index)
        (.var position) = some (((eventScope diagram projectionSymbol.index).2.lookup position).substitute
          ((Refinement.NativeModel (Worlds plan.snapshot.language)).toCwf.idS _))
      rw [Value.substitute_identity]
      rfl)
  change (model installed admitted diagram).evaluateTerm (eventScope diagram projectionSymbol.index) _ =
    some (Value.substitute (K := (Refinement.NativeModel (Worlds plan.snapshot.language)).toCwf)
      ⟨carrierNativeType (eventScope diagram projectionSymbol.index).1
        (NativeModalSignature.projectionCarrier plan modal projectionSymbol),
        projectionSection diagram projectionSymbol⟩ (𝟙 _)) at read
  exact read.trans (congrArg some (Value.substitute_identity _))

theorem projection_section_read (projectionSymbol : NativeModalSignature.Projection plan modal) :
    (carrierSectionEquiv (eventScope diagram projectionSymbol.index).1
      (NativeModalSignature.projectionCarrier plan modal projectionSymbol))
      (projectionSection diagram projectionSymbol) =
      (eventIso diagram projectionSymbol.index).hom ≫ diagram.projection projectionSymbol :=
  Equiv.apply_symm_apply _ _

theorem projection_readout (projectionSymbol : NativeModalSignature.Projection plan modal)
    (X : Base (algebra plan.snapshot.language))
    (value : (eventScope diagram projectionSymbol.index).1.obj X) :
    ((carrierSectionEquiv (eventScope diagram projectionSymbol.index).1
      (NativeModalSignature.projectionCarrier plan modal projectionSymbol))
      (projectionSection diagram projectionSymbol)).app X value =
      (diagram.projection projectionSymbol).app X
        ((eventIso diagram projectionSymbol.index).hom.app X value) := by
  rw [projection_section_read]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem input_square (index : Fin modal.length) :
    (eventIso diagram index).hom ≫ diagram.observe index =
      totalProjection (eventNative diagram index).decoded ≫ (inputIso diagram index).hom := by
  have base := observationTotalIso_projection (nativeObservation diagram index)
  change (eventIso diagram index).hom ≫ nativeObservation diagram index =
    totalProjection (eventNative diagram index).decoded at base
  have post := congrArg (fun arrow => arrow ≫ (inputIso diagram index).hom) base
  simpa [nativeObservation] using post

/-- The displayed native fibre is conditioned on the independently chosen
input, while retaining the entire event and its input agreement. -/
abbrev nativeEventFibre (index : Fin modal.length)
    (X : Base (algebra plan.snapshot.language)) (input : (diagram.input index).obj X) :=
  (eventNative diagram index).decoded.obj
    ⟨X, (inputIso diagram index).inv.app X input⟩

noncomputable def eventFibreEquiv (index : Fin modal.length)
    (X : Base (algebra plan.snapshot.language)) (input : (diagram.input index).obj X) :
    nativeEventFibre diagram index X input ≃
      {event : (diagram.events index).obj X | (diagram.observe index).app X event = input} where
  toFun value := by
    refine ⟨value.val, ?_⟩
    have read := value.property
    change (inputIso diagram index).inv.app X ((diagram.observe index).app X value.val) =
      (inputIso diagram index).inv.app X input at read
    exact ((inputIso diagram index).app X).toEquiv.symm.injective read
  invFun value := ⟨value.val, congrArg ((inputIso diagram index).inv.app X) value.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

set_option backward.isDefEq.respectTransparency false in
theorem event_fibre_projection_readout
    (projectionSymbol : NativeModalSignature.Projection plan modal)
    (X : Base (algebra plan.snapshot.language))
    (input : (diagram.input projectionSymbol.index).obj X)
    (value : nativeEventFibre diagram projectionSymbol.index X input) :
    ((carrierSectionEquiv (eventScope diagram projectionSymbol.index).1
      (NativeModalSignature.projectionCarrier plan modal projectionSymbol))
      (projectionSection diagram projectionSymbol)).app X
        ⟨(inputIso diagram projectionSymbol.index).inv.app X input, value⟩ =
      (diagram.projection projectionSymbol).app X
        (eventFibreEquiv diagram projectionSymbol.index X input value).val := by
  rw [projection_readout]
  rfl

/-- Distinct complete events remain distinct points of native comprehension,
even if a selected output projection agrees. -/
theorem complete_events_distinct (index : Fin modal.length)
    (X : Base (algebra plan.snapshot.language))
    {first second : (eventScope diagram index).1.obj X}
    (different : (eventIso diagram index).hom.app X first ≠
      (eventIso diagram index).hom.app X second) : first ≠ second :=
  fun same => different (congrArg ((eventIso diagram index).hom.app X) same)

/-- A checked derivation receives the common constructor-and-event meaning;
declaration agreement is established by the evaluator above. -/
theorem checked_native_sound
    (certificate : Certificates.Refinement.Certificate
      (NativeModalSignature.signature plan installed modal))
    (judgment : Refinement.Judgment (NativeModalSignature.symbols plan installed modal))
    (checked : Certificates.Refinement.check certificate judgment = true) :
    Refinement.Interprets (model installed admitted diagram) judgment :=
  (Certificates.Refinement.reconstruct certificate judgment checked).sound
    (model installed admitted diagram) (realization installed admitted diagram)
    (NativeLocalTypeOperations.products_substitution (Worlds plan.snapshot.language))
    (NativeLocalTypeOperations.products_beta (Worlds plan.snapshot.language))
    (NativeLocalPiEta.products_eta (Worlds plan.snapshot.language))

end Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeModalModel
