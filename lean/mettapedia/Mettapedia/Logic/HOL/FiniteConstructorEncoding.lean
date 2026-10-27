import Mettapedia.TypeTheory.FiniteConstructorEncoding
import Mettapedia.Logic.HOL.Soundness

/-!
# Typed function encodings of constructor data

Each constructor selects one predicate handler and applies it to the original
typed data terms. The construction uses lambda and application only. Weakening
under handlers is shared across all fields; no constructor-specific de Bruijn
offsets are supplied by a client.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.FiniteConstructorEncoding

open Mettapedia.TypeTheory.IndexedPolynomial.Description

universe u v w
variable {Base : Type u} {Const : Ty Base → Type v}
variable {Γ : Ctx Base}

def handlerType : List (Ty Base) → Ty Base
  | [] => .prop
  | type :: rest => type ⇒ handlerType rest

def payloadType : List (List (Ty Base)) → Ty Base
  | [] => .prop
  | fields :: rest => handlerType fields ⇒ payloadType rest

abbrev Arguments (Const : Ty Base → Type v) (Γ : Ctx Base) (fields : List (Ty Base)) :=
  Env (Term Const Γ) fields

def weakenArguments (type : Ty Base) : (fields : List (Ty Base)) →
    Arguments Const Γ fields → Arguments Const (type :: Γ) fields
  | [], _ => PUnit.unit
  | _ :: rest, arguments => (weaken arguments.1, weakenArguments type rest arguments.2)

def applyArguments : (fields : List (Ty Base)) →
    Term Const Γ (handlerType fields) → Arguments Const Γ fields → Formula Const Γ
  | [], function, _ => function
  | _ :: rest, function, arguments => applyArguments rest (.app function arguments.1) arguments.2

def ignoreHandlers : {Γ : Ctx Base} → (signature : List (List (Ty Base))) →
    Formula Const Γ → Term Const Γ (payloadType signature)
  | _, [], body => body
  | _, _ :: rest, body => .lam (ignoreHandlers rest (weaken body))

def encode : {Γ : Ctx Base} → (signature : List (List (Ty Base))) →
    (occurrence : Fin signature.length) → Arguments Const Γ (signature.get occurrence) →
      Term Const Γ (payloadType signature)
  | _, [], occurrence, _ => Fin.elim0 occurrence
  | _, fields :: rest, ⟨0, _⟩, arguments =>
      .lam (ignoreHandlers rest (applyArguments fields (.var .vz)
        (weakenArguments (handlerType fields) fields arguments)))
  | _, fields :: rest, ⟨n + 1, bound⟩, arguments =>
      .lam (encode rest ⟨n, Nat.lt_of_succ_lt_succ bound⟩
        (weakenArguments (handlerType fields) _ arguments))

variable (model : HenkinModel.{u,v,w} Base Const)

def handlerEquivalence : (fields : List (Ty Base)) →
    Ty.denote model.Carrier (handlerType fields) ≃
      Mettapedia.TypeTheory.FiniteConstructorEncoding.Handler (Ty.denote model.Carrier) fields
  | [] => Equiv.refl _
  | _ :: rest => Equiv.arrowCongr (Equiv.refl _) (handlerEquivalence rest)

def payloadEquivalence : (signature : List (List (Ty Base))) →
    Ty.denote model.Carrier (payloadType signature) ≃
      Mettapedia.TypeTheory.FiniteConstructorEncoding.Payload (Ty.denote model.Carrier) signature
  | [] => Equiv.refl _
  | fields :: rest => Equiv.arrowCongr (handlerEquivalence model fields) (payloadEquivalence rest)

def denoteArguments : (fields : List (Ty Base)) → Arguments Const Γ fields →
    model.Valuation Γ → Env (Ty.denote model.Carrier) fields
  | [], _, _ => PUnit.unit
  | _ :: rest, arguments, values =>
      (model.denote arguments.1 values, denoteArguments rest arguments.2 values)

theorem denoteArguments_weaken (fields : List (Ty Base)) (arguments : Arguments Const Γ fields)
    (values : model.Valuation Γ) {type : Ty Base} (value : Ty.denote model.Carrier type) :
    denoteArguments model fields (weakenArguments type fields arguments) (model.extend values value) =
      denoteArguments model fields arguments values := by
  induction fields with
  | nil => rfl
  | cons first rest hypotheses =>
      change (model.denote (weaken arguments.1) (model.extend values value), _) = _
      rw [Soundness.denote_weaken]
      exact congrArg (Prod.mk _) (hypotheses arguments.2)

theorem applyArguments_denote (fields : List (Ty Base))
    (function : Term Const Γ (handlerType fields)) (arguments : Arguments Const Γ fields)
    (values : model.Valuation Γ) :
    model.denote (applyArguments fields function arguments) values =
      Mettapedia.TypeTheory.FiniteConstructorEncoding.apply (Ty.denote model.Carrier) fields
        (handlerEquivalence model fields (model.denote function values))
        (denoteArguments model fields arguments values) := by
  induction fields with
  | nil => rfl
  | cons first rest hypotheses => exact hypotheses (.app function arguments.1) arguments.2

theorem ignoreHandlers_denote (signature : List (List (Ty Base)))
    (body : Formula Const Γ) (values : model.Valuation Γ) :
    payloadEquivalence model signature (model.denote (ignoreHandlers signature body) values) =
      Mettapedia.TypeTheory.FiniteConstructorEncoding.curry (Mettapedia.TypeTheory.FiniteConstructorEncoding.Handler (Ty.denote model.Carrier)) signature
        (fun _ => model.denote body values) := by
  induction signature generalizing Γ with
  | nil => rfl
  | cons fields rest hypotheses =>
      funext handler
      change payloadEquivalence model rest
        (model.denote (ignoreHandlers rest (weaken body))
          (model.extend values ((handlerEquivalence model fields).symm handler))) = _
      rw [hypotheses, Soundness.denote_weaken]
      rfl

theorem encode_denote (signature : List (List (Ty Base)))
    (occurrence : Fin signature.length) (arguments : Arguments Const Γ (signature.get occurrence))
    (values : model.Valuation Γ) :
    payloadEquivalence model signature (model.denote (encode signature occurrence arguments) values) =
      Mettapedia.TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) signature
        ⟨occurrence, denoteArguments model _ arguments values⟩ := by
  induction signature generalizing Γ with
  | nil => exact Fin.elim0 occurrence
  | cons fields rest hypotheses =>
      rcases occurrence with ⟨n, bound⟩
      cases n with
      | zero =>
          funext handler
          change payloadEquivalence model rest
            (model.denote (ignoreHandlers rest (applyArguments fields (.var .vz)
              (weakenArguments (handlerType fields) fields arguments)))
              (model.extend values ((handlerEquivalence model fields).symm handler))) = _
          rw [ignoreHandlers_denote, applyArguments_denote, denoteArguments_weaken]
          simp only [HenkinModel.denote, PreModel.denote, PreModel.extend, Equiv.apply_symm_apply]
          rfl
      | succ n =>
          funext handler
          change payloadEquivalence model rest
            (model.denote (encode rest ⟨n, Nat.lt_of_succ_lt_succ bound⟩
              (weakenArguments (handlerType fields) _ arguments))
              (model.extend values ((handlerEquivalence model fields).symm handler))) = _
          rw [hypotheses, denoteArguments_weaken]
          rfl

#print axioms encode_denote

end Mettapedia.Logic.HOL.FiniteConstructorEncoding
