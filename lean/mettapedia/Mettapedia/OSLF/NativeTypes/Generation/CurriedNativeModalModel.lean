import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeConstructorModel
import Mettapedia.OSLF.NativeTypes.Generation.NativeModalSignature

/-!
# Constructor and operational families in one native source model

The source category is the original language's binding clone. A natural
operational observation determines its actual dependent receipt family.
Comprehension recovers the complete event presheaf, and every operational
projection is interpreted through the same native carriers as constructors.
The declaration evaluator's agreement is proved from these constructions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeModalModel

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.NativeDependent
open NativeLocalTypeFormers ContextualLocalUniverses
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafParameterFamilies NativeNondependentFunctionComparison
open CurriedBindingLanguage BindingSemanticAdmission

variable {plan : Plan} {installed : NativeSignature.Installation plan.snapshot.language}
    {modal : List (NativeModalHeaders.Header plan)}

/-- Semantic data, without an assumed declaration-realization theorem.
Operational instances supply their independently constructed event maps. -/
structure Diagram (plan : Plan) (modal : List (NativeModalHeaders.Header plan)) where
  input : Fin modal.length → Base (algebra plan.snapshot.language) ⥤ Type
  events : Fin modal.length → Base (algebra plan.snapshot.language) ⥤ Type
  observe : ∀ index, events index ⟶ input index
  projection : ∀ projection : NativeModalSignature.Projection plan modal,
    events projection.index ⟶ meaning (NativeModalSignature.projectionCarrier plan modal projection)

noncomputable def inputNative (diagram : Diagram plan modal) (index : Fin modal.length) :
    NativeType (emptyNativeScope plan.snapshot.language).1 :=
  LocalType.present (parameterFamily (emptyNativeScope plan.snapshot.language).1
    (diagram.input index))

noncomputable def inputScope (diagram : Diagram plan modal) (index : Fin modal.length) :
    Refinement.Scope (Worlds plan.snapshot.language) 1 :=
  (emptyNativeScope plan.snapshot.language).snoc (inputNative diagram index)

noncomputable def inputIso (diagram : Diagram plan modal) (index : Fin modal.length) :
    (inputScope diagram index).1 ≅ diagram.input index :=
  totalFamilyIso (Iso.refl _) ≪≫ ρ_ (diagram.input index)

noncomputable def nativeObservation (diagram : Diagram plan modal) (index : Fin modal.length) :
    diagram.events index ⟶ (inputScope diagram index).1 :=
  diagram.observe index ≫ (inputIso diagram index).inv

noncomputable def eventNative (diagram : Diagram plan modal) (index : Fin modal.length) :
    NativeType (inputScope diagram index).1 :=
  LocalType.present (observationFibreFamily (nativeObservation diagram index))

noncomputable def eventScope (diagram : Diagram plan modal) (index : Fin modal.length) :
    Refinement.Scope (Worlds plan.snapshot.language) 2 :=
  (inputScope diagram index).snoc (eventNative diagram index)

noncomputable def eventIso (diagram : Diagram plan modal) (index : Fin modal.length) :
    (eventScope diagram index).1 ≅ diagram.events index :=
  observationTotalIso (nativeObservation diagram index)

noncomputable def projectionMap (diagram : Diagram plan modal)
    (projection : NativeModalSignature.Projection plan modal) :
    (eventScope diagram projection.index).1 ⟶
      meaning (NativeModalSignature.projectionCarrier plan modal projection) :=
  (eventIso diagram projection.index).hom ≫ diagram.projection projection

noncomputable def projectionSection (diagram : Diagram plan modal)
    (projection : NativeModalSignature.Projection plan modal) :
    (carrierNativeType (eventScope diagram projection.index).1
      (NativeModalSignature.projectionCarrier plan modal projection)).decoded.sections :=
  (carrierSectionEquiv (eventScope diagram projection.index).1
    (NativeModalSignature.projectionCarrier plan modal projection)).symm
      (projectionMap diagram projection)

/-- The left constructor interpretation is retained; the right declaration
families and sections use actual dependent observations in that same model. -/
noncomputable def model (installed : NativeSignature.Installation plan.snapshot.language)
    (admitted : Admitted plan.snapshot.language) (diagram : Diagram plan modal) :
    Refinement.ModelData (NativeModalSignature.symbols plan installed modal)
      (Worlds plan.snapshot.language) where
  typeParameters := fun symbol => match symbol with
    | .inl _ => emptyNativeScope plan.snapshot.language
    | .inr (.input _) => emptyNativeScope plan.snapshot.language
    | .inr (.event index) => inputScope diagram index
  typeFamily := fun symbol => match symbol with
    | .inl position => sortNativeType position
    | .inr (.input index) => inputNative diagram index
    | .inr (.event index) => eventNative diagram index
  termParameters := fun symbol => match symbol with
    | .inl constructor => carrierScope installed.headers[constructor].parameters
    | .inr projectionSymbol => eventScope diagram projectionSymbol.index
  termType := fun symbol => match symbol with
    | .inl constructor => carrierNativeType (carrierScope installed.headers[constructor].parameters).1
        (.sort installed.headers[constructor].result)
    | .inr projectionSymbol => carrierNativeType (eventScope diagram projectionSymbol.index).1
        (NativeModalSignature.projectionCarrier plan modal projectionSymbol)
  termValue := fun symbol => match symbol with
    | .inl constructor => constructorSection admitted installed.headers[constructor]
        (installed_header_correct installed constructor)
    | .inr projectionSymbol => projectionSection diagram projectionSymbol
  predicateParameters := fun symbol => match symbol with
    | .inl symbol => nomatch symbol
    | .inr symbol => nomatch symbol
  predicateValue := fun symbol => match symbol with
    | .inl symbol => nomatch symbol
    | .inr symbol => nomatch symbol

variable (installed : NativeSignature.Installation plan.snapshot.language)
    (admitted : Admitted plan.snapshot.language) (diagram : Diagram plan modal)

theorem carrier_read {n : Nat} (scope : Refinement.Scope (Worlds plan.snapshot.language) n)
    (carrier : NativeSignature.Carrier plan.snapshot.language) :
    (model installed admitted diagram).evaluateType scope
      (NativeModalSignature.authoredType plan installed modal carrier n) =
      some (carrierNativeType scope.1 carrier) := by
  induction carrier generalizing n with
  | sort position =>
      exact (model installed admitted diagram).evaluate_family scope (.inl position) Fin.elim0
        ((Refinement.NativeModel (Worlds plan.snapshot.language)).toEmpty scope.1)
        (fun index => Fin.elim0 index)
  | function domain body domainIH bodyIH =>
      exact (model installed admitted diagram).evaluate_pi scope
        (NativeModalSignature.authoredType plan installed modal domain n)
        (NativeModalSignature.authoredType plan installed modal body (n + 1))
        (carrierNativeType scope.1 domain)
        (carrierNativeType (scope.snoc (carrierNativeType scope.1 domain)).1 body)
        (domainIH scope) (bodyIH (scope.snoc (carrierNativeType scope.1 domain)))

theorem telescope_read (parameters : List (NativeSignature.Carrier plan.snapshot.language)) :
    (model installed admitted diagram).evaluateContext
      (Refinement.SignatureSum.contextLeft (NativeSignature.telescope parameters)) =
      some (carrierScope parameters) := by
  induction parameters with
  | nil => rfl
  | cons parameter parameters ih =>
      exact (model installed admitted diagram).evaluateContext_snoc
        (Refinement.SignatureSum.contextLeft (NativeSignature.telescope parameters))
        (NativeModalSignature.authoredType plan installed modal parameter parameters.length)
        (carrierScope parameters)
        (carrierNativeType (carrierScope parameters).1 parameter) ih
        (carrier_read installed admitted diagram (carrierScope parameters) parameter)

theorem input_read (index : Fin modal.length) {n : Nat}
    (scope : Refinement.Scope (Worlds plan.snapshot.language) n) :
    (model installed admitted diagram).evaluateType scope
      (NativeModalSignature.inputType plan installed modal index n) =
      some ((inputNative diagram index).reindex
        ((Refinement.NativeModel (Worlds plan.snapshot.language)).toEmpty scope.1)) :=
  (model installed admitted diagram).evaluate_family scope (.inr (.input index)) Fin.elim0
    ((Refinement.NativeModel (Worlds plan.snapshot.language)).toEmpty scope.1)
    (fun position => Fin.elim0 position)

set_option backward.isDefEq.respectTransparency false in
theorem input_empty_read (index : Fin modal.length) :
    (model installed admitted diagram).evaluateType (emptyNativeScope plan.snapshot.language)
      (NativeModalSignature.inputType plan installed modal index 0) =
      some (inputNative diagram index) := by
  have read := input_read installed admitted diagram index (emptyNativeScope plan.snapshot.language)
  have identity : (Refinement.NativeModel (Worlds plan.snapshot.language)).toEmpty
      (emptyNativeScope plan.snapshot.language).1 =
      (Refinement.NativeModel (Worlds plan.snapshot.language)).toCwf.idS
        (emptyNativeScope plan.snapshot.language).1 :=
    ((Refinement.NativeModel (Worlds plan.snapshot.language)).toEmpty_unique _ _).symm
  change (model installed admitted diagram).evaluateType _ _ =
    some ((Refinement.NativeModel (Worlds plan.snapshot.language)).toCwf.tySub
      (inputNative diagram index) ((Refinement.NativeModel (Worlds plan.snapshot.language)).toEmpty _)) at read
  rw [identity, (Refinement.NativeModel (Worlds plan.snapshot.language)).toCwf.tySub_id] at read
  exact read

theorem input_context_read (index : Fin modal.length) :
    (model installed admitted diagram).evaluateContext
      (NativeModalSignature.inputContext plan installed modal index) =
      some (inputScope diagram index) :=
  (model installed admitted diagram).evaluateContext_snoc .nil
    (NativeModalSignature.inputType plan installed modal index 0)
    (emptyNativeScope plan.snapshot.language) (inputNative diagram index) rfl
    (input_empty_read installed admitted diagram index)

set_option backward.isDefEq.respectTransparency false in
theorem event_type_read (index : Fin modal.length) :
    (model installed admitted diagram).evaluateType (inputScope diagram index)
      (NativeModalSignature.eventType plan installed modal index (.var 0)) =
      some (eventNative diagram index) := by
  have read := (model installed admitted diagram).evaluate_family (inputScope diagram index)
    (.inr (.event index)) (NativeModalSignature.singletonArgument plan installed modal (.var 0))
    (𝟙 (inputScope diagram index).1) (by
      intro position
      cases position using Fin.cases with
      | zero =>
          change (model installed admitted diagram).evaluateTerm (inputScope diagram index) (.var 0) =
            some (((inputScope diagram index).2.lookup 0).substitute
              ((Refinement.NativeModel (Worlds plan.snapshot.language)).toCwf.idS _))
          rw [Mettapedia.TypeTheory.ContextualModelTelescopes.Value.substitute_identity]
          rfl
      | succ impossible => exact Fin.elim0 impossible)
  change (model installed admitted diagram).evaluateType _ _ =
    some ((Refinement.NativeModel (Worlds plan.snapshot.language)).toCwf.tySub
      (eventNative diagram index) ((Refinement.NativeModel (Worlds plan.snapshot.language)).toCwf.idS _)) at read
  rw [(Refinement.NativeModel (Worlds plan.snapshot.language)).toCwf.tySub_id] at read
  exact read

theorem event_context_read (index : Fin modal.length) :
    (model installed admitted diagram).evaluateContext
      (NativeModalSignature.eventContext plan installed modal index) =
      some (eventScope diagram index) :=
  (model installed admitted diagram).evaluateContext_snoc
    (NativeModalSignature.inputContext plan installed modal index)
    (NativeModalSignature.eventType plan installed modal index (.var 0))
    (inputScope diagram index) (eventNative diagram index)
    (input_context_read installed admitted diagram index)
    (event_type_read installed admitted diagram index)

theorem realization :
    Refinement.SignatureRealization (model installed admitted diagram)
      (NativeModalSignature.signature plan installed modal) where
  typeHeader := by
    intro symbol
    cases symbol with
    | inl position => rfl
    | inr symbol =>
        cases symbol with
        | input index => rfl
        | event index => exact input_context_read installed admitted diagram index
  termHeader := by
    intro symbol
    cases symbol with
    | inl constructor => exact telescope_read installed admitted diagram _
    | inr projectionSymbol => exact event_context_read installed admitted diagram _
  predicateHeader := by
    intro symbol
    cases symbol with
    | inl symbol => nomatch symbol
    | inr symbol => nomatch symbol
  termResult := by
    intro symbol
    cases symbol with
    | inl constructor =>
        exact carrier_read installed admitted diagram
          (carrierScope installed.headers[constructor].parameters) (.sort installed.headers[constructor].result)
    | inr projectionSymbol =>
        exact carrier_read installed admitted diagram
          (eventScope diagram projectionSymbol.index)
          (NativeModalSignature.projectionCarrier plan modal projectionSymbol)

end Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeModalModel
