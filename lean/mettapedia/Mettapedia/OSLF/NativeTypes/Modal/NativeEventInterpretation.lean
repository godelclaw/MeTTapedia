import Mettapedia.OSLF.NativeTypes.Modal.NativeEventDeclarations
import Mettapedia.OSLF.NativeTypes.Modal.NativeEventFibre

/-!
# Actual receipt fibres interpret finite generated native declarations

The finite event declaration model is built from actual scoped receipt
projections. Its source and target primitives read the complete event, and its
raw parser is proved to evaluate the authored headers to those meanings.
Every native judgment then receives the original dependent interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeEventInterpretation

open _root_.CategoryTheory Opposite
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.NativeLocalTypeFormers
open Mettapedia.TypeTheory
open NativeEventDeclarations

universe u
variable {plan : Plan} {W : Type u} [Category.{u} W]

noncomputable section

abbrev Base := RepresentableIndexedDeclarations.PresheafReadout.Base W

abbrev patternPresheaf : Wᵒᵖ ⥤ Type u :=
  (Functor.const Wᵒᵖ).obj (ULift.{u} Pattern)

def carrierObject (carrier : Carrier) : Base (W := W) :=
  match carrier with
  | .input => ⟨NativeEventFibre.inputPresheaf⟩
  | .pattern => ⟨patternPresheaf⟩

abbrev eventArrow (index : Index plan) :=
  NativeEventFibre.indexed (W := W) (schema plan index)

abbrev inputScope : Scope (Base (W := W)) 1 :=
  RepresentableIndexedDeclarations.objectScope (carrierObject (W := W) .input)

abbrev eventScope (index : Index plan) : Scope (Base (W := W)) 2 :=
  RepresentableIndexedDeclarations.fibreScope (eventArrow (W := W) index)

/-- Projection is computed from the whole original receipt-backed event. -/
def observation (index : Index plan) (target : Bool) :
    (NativeEventFibre.eventPresheaf (schema plan index)) ⟶ (patternPresheaf (W := W)) where
  app _ := TypeCat.ofHom fun event => ⟨if target then event.down.target else event.down.source⟩
  naturality _ _ _ := rfl

abbrev termScope (symbol : TermSymbol plan) : Scope (Base (W := W)) 2 :=
  match symbol with
  | .source index | .target index => eventScope index

abbrev patternMeaning := RepresentableIndexedDeclarations.objectMeaning
  (carrierObject (W := W) .pattern)

abbrev readoutType (symbol : TermSymbol plan) :
    NativeType (termScope (W := W) symbol).1 :=
  (patternMeaning (W := W)).reindex
    ((NativeModel (Base (W := W))).toEmpty (termScope symbol).1)

/-- The represented output arrow retains the underlying event before reading
its source or specified contractum. -/
def readoutName (symbol : TermSymbol plan) :
    (termScope (W := W) symbol).1 ⟶ yoneda.obj (carrierObject (W := W) .pattern) :=
  match symbol with
  | .source index =>
      RepresentableIndexedDeclarations.fibreName (eventArrow index) ≫
        yoneda.map (show (eventArrow (W := W) index).source ⟶ carrierObject .pattern from
          ⟨observation index false⟩)
  | .target index =>
      RepresentableIndexedDeclarations.fibreName (eventArrow index) ≫
        yoneda.map (show (eventArrow (W := W) index).source ⟶ carrierObject .pattern from
          ⟨observation index true⟩)

abbrev readoutValue (symbol : TermSymbol plan) :
    (readoutType (W := W) symbol).decoded.sections :=
  RepresentableDeclarations.representedSection (readoutName symbol)

def model : ModelData (symbols plan) (Base (W := W)) where
  typeParameters := fun symbol => match symbol with
    | .carrier _ => RepresentableIndexedDeclarations.emptyScope
    | .event _ => inputScope
  typeFamily := fun symbol => match symbol with
    | .carrier carrier => RepresentableIndexedDeclarations.objectMeaning (carrierObject carrier)
    | .event index => RepresentableIndexedDeclarations.fibreMeaning (eventArrow index)
  termParameters := termScope
  termType := readoutType
  termValue := readoutValue
  predicateParameters symbol := nomatch symbol
  predicateValue symbol := nomatch symbol

theorem carrier_read (carrier : Carrier) {n : Nat} (scope : Scope (Base (W := W)) n) :
    (model (plan := plan) (W := W)).evaluateType scope (carrierType carrier n) =
      some ((RepresentableIndexedDeclarations.objectMeaning (carrierObject carrier)).reindex
        ((NativeModel (Base (W := W))).toEmpty scope.1)) :=
  (model (plan := plan) (W := W)).evaluate_family scope (.carrier carrier) Fin.elim0
    ((NativeModel (Base (W := W))).toEmpty scope.1) (fun position => Fin.elim0 position)

set_option backward.isDefEq.respectTransparency false in
theorem carrier_empty_read (carrier : Carrier) :
    (model (plan := plan) (W := W)).evaluateType
      RepresentableIndexedDeclarations.emptyScope (carrierType carrier 0) =
      some (RepresentableIndexedDeclarations.objectMeaning (carrierObject carrier)) := by
  have read := carrier_read (plan := plan) (W := W) carrier
    RepresentableIndexedDeclarations.emptyScope
  have identity : (NativeModel (Base (W := W))).toEmpty
      (RepresentableIndexedDeclarations.emptyScope (C := Base (W := W))).1 =
      (NativeModel (Base (W := W))).toCwf.idS
        (RepresentableIndexedDeclarations.emptyScope (C := Base (W := W))).1 :=
    ((NativeModel (Base (W := W))).toEmpty_unique _ _).symm
  change (model (plan := plan) (W := W)).evaluateType _ (carrierType carrier 0) =
    some ((NativeModel (Base (W := W))).toCwf.tySub
      (RepresentableIndexedDeclarations.objectMeaning (carrierObject carrier))
      ((NativeModel (Base (W := W))).toEmpty _)) at read
  rw [identity, (NativeModel (Base (W := W))).toCwf.tySub_id] at read
  exact read

theorem input_context_read :
    (model (plan := plan) (W := W)).evaluateContext NativeEventDeclarations.inputContext =
      some (inputScope (W := W)) :=
  (model (plan := plan) (W := W)).evaluateContext_snoc .nil (carrierType .input 0)
    RepresentableIndexedDeclarations.emptyScope
    (RepresentableIndexedDeclarations.objectMeaning (carrierObject .input)) rfl
    (carrier_empty_read .input)

theorem input_variable_identity :
    (model (plan := plan) (W := W)).evaluateTerm inputScope (.var 0) =
      some (((inputScope (W := W)).2.lookup 0).substitute
        ((NativeModel (Base (W := W))).toCwf.idS inputScope.1)) := by
  rw [Value.substitute_identity]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem event_type_read (index : Index plan) :
    (model (W := W)).evaluateType inputScope (eventType index (.var 0)) =
      some (RepresentableIndexedDeclarations.fibreMeaning (eventArrow index)) := by
  have read := (model (W := W)).evaluate_family inputScope (.event index)
    (singletonArgument (.var 0)) (𝟙 (inputScope (W := W)).1) (by
      intro position
      cases position using Fin.cases with
      | zero => exact input_variable_identity (plan := plan) (W := W)
      | succ impossible => exact Fin.elim0 impossible)
  change (model (W := W)).evaluateType inputScope (eventType index (.var 0)) =
    some ((NativeModel (Base (W := W))).toCwf.tySub
      (RepresentableIndexedDeclarations.fibreMeaning (eventArrow index))
      ((NativeModel (Base (W := W))).toCwf.idS _)) at read
  rw [(NativeModel (Base (W := W))).toCwf.tySub_id] at read
  exact read

theorem event_context_read (index : Index plan) :
    (model (W := W)).evaluateContext (eventContext index) = some (eventScope (W := W) index) :=
  (model (W := W)).evaluateContext_snoc NativeEventDeclarations.inputContext
    (eventType index (.var 0)) inputScope
    (RepresentableIndexedDeclarations.fibreMeaning (eventArrow index))
    input_context_read (event_type_read index)

theorem realization :
    SignatureRealization (model (plan := plan) (W := W)) (signature plan) where
  typeHeader := by
    intro symbol
    cases symbol with
    | carrier => rfl
    | event => exact input_context_read
  termHeader := by
    intro symbol
    cases symbol <;> exact event_context_read _
  termResult := by
    intro symbol
    cases symbol <;> exact carrier_read .pattern (eventScope _)
  predicateHeader symbol := nomatch symbol

def projection (symbol : TermSymbol plan) : TermExpr (symbols plan) 2 :=
  .primitive symbol TermExpr.var

def projectionFormation (symbol : TermSymbol plan) :
    Derivation (signature plan) (.term ((signature plan).termParameters symbol)
      (projection symbol) (carrierType .pattern 2)) := by
  have tree := deriveList (.primitive ((signature plan).termParameters symbol) symbol TermExpr.var)
    (.cons ((headers plan).termHeader symbol) (.cons ((headers plan).termHeader symbol)
      (.cons ((headers plan).termResult symbol)
        (.cons (deriveList (.substitutionIdentity ((signature plan).termParameters symbol))
          (.cons ((headers plan).termHeader symbol) .nil)) .nil))))
  change Derivation (signature plan) (.term ((signature plan).termParameters symbol)
    (projection symbol) ((carrierType .pattern 2).substitute TermExpr.var)) at tree
  rw [carrierType_substitute] at tree
  exact tree

set_option backward.isDefEq.respectTransparency false in
theorem projection_read (symbol : TermSymbol plan) :
    (model (W := W)).evaluateTerm (termScope symbol) (projection symbol) =
      some ⟨readoutType symbol, readoutValue (W := W) symbol⟩ := by
  have read := (model (W := W)).evaluate_primitive (termScope symbol) symbol
    TermExpr.var (𝟙 (termScope (W := W) symbol).1) (by
      intro position
      change (model (W := W)).evaluateTerm (termScope symbol) (.var position) =
        some (((termScope (W := W) symbol).2.lookup position).substitute
          ((NativeModel (Base (W := W))).toCwf.idS (termScope symbol).1))
      rw [Value.substitute_identity]
      rfl)
  change (model (W := W)).evaluateTerm (termScope symbol) (projection symbol) =
    some (Value.substitute (K := (NativeModel (Base (W := W))).toCwf)
      (⟨readoutType symbol, readoutValue symbol⟩ : NativeValue (termScope (W := W) symbol).1)
      (𝟙 (termScope symbol).1)) at read
  exact read.trans (congrArg some
    (Value.substitute_identity (K := (NativeModel (Base (W := W))).toCwf)
      ⟨readoutType symbol, readoutValue symbol⟩))

abbrev nativeFibre (index : Index plan) (world : W) (input : NativeEventFibre.Input) :=
  NativeEventFibre.NativeFibre (schema plan index) world input

/-- The family computed in the finite alphabet decodes to the complete actual
occurrence fibre, retaining full receipts rather than just targets. -/
noncomputable def nativeEventEquiv (index : Index plan) (world : W)
    (input : NativeEventFibre.Input) :
    nativeFibre index world input ≃
      {event : NativeEventFibre.Event (schema plan index) | event.input _ = input} :=
  NativeEventFibre.eventEquiv (schema plan index) world input

abbrev eventArgument (index : Index plan) (world : W) (input : NativeEventFibre.Input) :=
  RepresentableIndexedDeclarations.PresheafReadout.argument
    (NativeEventFibre.inputProjection (W := W) (schema plan index)) world (ULift.up input)

def targetOutput (index : Index plan) (world : W) (input : NativeEventFibre.Input)
    (value : nativeFibre index world input) : Pattern :=
  (yonedaEquiv ((readoutValue (W := W) (.target index)).val
    ⟨op (RepresentableIndexedDeclarations.PresheafReadout.worldObject world),
      ⟨eventArgument index world input, value⟩⟩).down).down

theorem target_output_exact (index : Index plan) (world : W) (input : NativeEventFibre.Input)
    (value : nativeFibre index world input) :
    targetOutput index world input value = (nativeEventEquiv index world input value).val.target := by
  have read := yonedaEquiv_comp value.val.down (observation (W := W) index true)
  exact congrArg ULift.down read

theorem target_output_is_specified (index : Index plan) (world : W)
    (input : NativeEventFibre.Input) (value : nativeFibre index world input) :
    (schema plan index).rhs? input.2 = some (targetOutput index world input value) := by
  rw [target_output_exact]
  exact (NativeEventFibre.complete_event_readout (schema plan index) world input value).2.1

theorem checked_native_sound (certificate : Certificates.Refinement.Certificate (signature plan))
    (judgment : Judgment (symbols plan))
    (checked : Certificates.Refinement.check certificate judgment = true) :
    Interprets (model (W := W)) judgment :=
  (Certificates.Refinement.reconstruct certificate judgment checked).sound
    (model (W := W)) realization
    (NativeLocalTypeOperations.products_substitution (Base (W := W)))
    (NativeLocalTypeOperations.products_beta (Base (W := W)))
    (NativeLocalPiEta.products_eta (Base (W := W)))

end

end Mettapedia.OSLF.NativeTypes.Modal.NativeEventInterpretation
