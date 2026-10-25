import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLImpredicativeDenotation
import Mettapedia.Logic.HOL.Semantics.StandardTransport

/-!
# Model comparison for actual native HOL denotations

A comparison of full Henkin carriers that agrees on the declared constants
transports the existing constructorwise native denotation judgment. It keeps
the native term fixed and compares its actual values, including application
and context extension. The result applies to arbitrary admitted native
semantic derivations, not only to terms reconstructed from a source proof.

The semantic interface is a displayed judgment on a declared signature. This
comparison does not assert that arbitrary conflicting declarations define a
single-valued interpretation, nor that arbitrary native conversion is sound.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLModelTransport

open Mettapedia.Logic
open FormationSensitiveHOLInterface NativeHOLSignatureDenotation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

universe u v w w'
variable {Base : Type u} {Const : HOL.Ty Base → Type v}
variable (source : HOL.HenkinModel.{u, v, w} Base Const)
  (target : HOL.HenkinModel.{u, v, w'} Base Const)
  (base : ∀ b, source.Carrier b ≃ target.Carrier b)

def valueTransport {gamma : HOL.Ctx Base} {type : HOL.Ty Base}
    (value : source.Valuation gamma → HOL.Ty.denote source.Carrier type) :
    target.Valuation gamma → HOL.Ty.denote target.Carrier type :=
  fun valuation => HOL.StandardTransport.liftEquiv base type
    (value ((HOL.StandardTransport.valuationEquiv source target base gamma).symm valuation))

private theorem inverse_extend {gamma : HOL.Ctx Base} {type : HOL.Ty Base}
    (valuation : target.Valuation gamma) (value : HOL.Ty.denote target.Carrier type) :
    ((HOL.StandardTransport.valuationEquiv source target base (type :: gamma)).symm
      (target.extend valuation value) : source.Valuation (type :: gamma)) =
      (source.extend ((HOL.StandardTransport.valuationEquiv source target base gamma).symm valuation)
        ((HOL.StandardTransport.liftEquiv base type).symm value) : source.Valuation (type :: gamma)) := by
  funext a index
  cases index <;> rfl

variable (sourceFull : source.FullDomains) (targetFull : target.FullDomains)
  (constants : ∀ {type : HOL.Ty Base} (constant : Const type),
    HOL.StandardTransport.liftEquiv base type (source.constDen constant) = target.constDen constant)

include sourceFull targetFull constants

/-- The actual native constructor semantics commutes with the carrier comparison. -/
theorem denotes_transport {signature : LogicalSignature Base Const}
    {gamma : HOL.Ctx Base} {type : HOL.Ty Base}
    {raw : Tower.Tm gamma.length}
    {value : source.Valuation gamma → HOL.Ty.denote source.Carrier type}
    (meaning : Denotes signature source raw value) :
    Denotes signature target raw (valueTransport source target base value) := by
  induction meaning with
  | index index =>
      convert (Denotes.index (signature := signature) (model := target) index) using 1
      funext valuation
      exact (HOL.StandardTransport.liftEquiv base _).apply_symm_apply (valuation index)
  | constant symbol =>
      convert (Denotes.constant (signature := signature) (model := target) symbol) using 1
      funext valuation
      exact constants symbol
  | implication => exact .implication
  | @universal gamma type =>
      have values : valueTransport source target base (gamma := gamma)
          (type := .arr (.arr type .prop) .prop)
          (fun _ predicate => ULift.up (∀ x, source.adm type x → (predicate x).down)) =
          (fun _ predicate => ULift.up (∀ x, target.adm type x → (predicate x).down)) := by
        funext valuation predicate
        apply ULift.ext
        change (∀ x, source.adm type x →
          (predicate (HOL.StandardTransport.liftEquiv base type x)).down) =
          (∀ x, target.adm type x → (predicate x).down)
        apply propext
        constructor
        · intro holds value _
          obtain ⟨original, rfl⟩ := (HOL.StandardTransport.liftEquiv base type).surjective value
          exact holds original (sourceFull _ _)
        · intro holds value _
          exact holds _ (targetFull _ _)
      rw [values]
      exact .universal type
  | @equality gamma type =>
      have values : valueTransport source target base (gamma := gamma)
          (type := .arr type (.arr type .prop))
          (fun _ left right => ULift.up (source.Eqv type left right)) =
          (fun _ left right => ULift.up (target.Eqv type left right)) := by
        funext valuation left right
        apply ULift.ext
        apply propext
        change source.Eqv type ((HOL.StandardTransport.liftEquiv base type).symm left)
          ((HOL.StandardTransport.liftEquiv base type).symm right) ↔ target.Eqv type left right
        simpa only [Equiv.apply_symm_apply] using
          (HOL.StandardTransport.eqv_transport source target sourceFull targetFull base type
            ((HOL.StandardTransport.liftEquiv base type).symm left)
            ((HOL.StandardTransport.liftEquiv base type).symm right)).symm
      rw [values]
      exact .equality type
  | @application gamma domain codomain function argument functionMeaning argumentMeaning _ _ functionInduction argumentInduction =>
      have interpreted := Denotes.application functionInduction argumentInduction
      have values :
          (fun valuation => valueTransport source target base (type := .arr domain codomain) functionMeaning valuation
            (valueTransport source target base (type := domain) argumentMeaning valuation)) =
          valueTransport source target base (type := codomain)
            (fun valuation => functionMeaning valuation (argumentMeaning valuation)) := by
        funext valuation
        exact HOL.StandardTransport.liftEquiv_arr_apply base _ _
      rw [values] at interpreted
      exact interpreted
  | @abstraction gamma domain codomain body bodyMeaning _ inductionHypothesis =>
      have interpreted := Denotes.abstraction inductionHypothesis
      have values :
          (fun valuation x => valueTransport source target base (type := codomain) bodyMeaning (target.extend valuation x)) =
          valueTransport source target base (type := .arr domain codomain)
            (fun valuation x => bodyMeaning (source.extend valuation x)) := by
        funext valuation x
        change HOL.StandardTransport.liftEquiv base codomain
          (bodyMeaning ((HOL.StandardTransport.valuationEquiv source target base (domain :: gamma)).symm
            (target.extend valuation x))) = _
        rw [inverse_extend]
        rfl
      rw [values] at interpreted
      exact interpreted

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLModelTransport
