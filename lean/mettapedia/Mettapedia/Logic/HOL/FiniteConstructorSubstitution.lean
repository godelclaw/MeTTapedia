import Mettapedia.Logic.HOL.FiniteConstructorEncoding

/-!
# Substitution for typed constructor payloads

Substitution acts on every data field and commutes with handler application,
unused-handler abstraction and constructor encoding. These laws apply under
arbitrary typed contexts and support retained beta proofs for generated guards.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.FiniteConstructorEncoding

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {Γ Δ Ξ : Ctx Base}

def substituteArguments (substitution : Subst Const Γ Δ) : (fields : List (Ty Base)) →
    Arguments Const Γ fields → Arguments Const Δ fields
  | [], _ => PUnit.unit
  | _ :: rest, arguments =>
      (subst substitution arguments.1, substituteArguments substitution rest arguments.2)

theorem substituteArguments_id (fields : List (Ty Base)) (arguments : Arguments Const Γ fields) :
    substituteArguments (fun index => .var index) fields arguments = arguments := by
  induction fields with
  | nil => cases arguments; rfl
  | cons type rest hypotheses =>
      exact congrArg₂ Prod.mk (subst_id arguments.1) (hypotheses arguments.2)

theorem substituteArguments_comp (later : Subst Const Δ Ξ) (earlier : Subst Const Γ Δ)
    (fields : List (Ty Base)) (arguments : Arguments Const Γ fields) :
    substituteArguments later fields (substituteArguments earlier fields arguments) =
      substituteArguments (fun index => subst later (earlier index)) fields arguments := by
  induction fields with
  | nil => rfl
  | cons type rest hypotheses =>
      change (subst later (subst earlier arguments.1), _) = _
      rw [subst_comp]
      exact congrArg (Prod.mk _) (hypotheses arguments.2)

theorem substituteArguments_weaken (substitution : Subst Const Γ Δ) (type : Ty Base)
    (fields : List (Ty Base)) (arguments : Arguments Const Γ fields) :
    substituteArguments (Subst.lift substitution) fields (weakenArguments type fields arguments) =
      weakenArguments type fields (substituteArguments substitution fields arguments) := by
  induction fields with
  | nil => rfl
  | cons first rest hypotheses =>
      change (subst (Subst.lift substitution) (weaken arguments.1), _) = _
      rw [subst_weaken]
      exact congrArg (Prod.mk _) (hypotheses arguments.2)

theorem applyArguments_subst (substitution : Subst Const Γ Δ)
    (fields : List (Ty Base)) (function : Term Const Γ (handlerType fields))
    (arguments : Arguments Const Γ fields) :
    subst substitution (applyArguments fields function arguments) =
      applyArguments fields (subst substitution function) (substituteArguments substitution fields arguments) := by
  induction fields with
  | nil => rfl
  | cons type rest hypotheses => exact hypotheses (.app function arguments.1) arguments.2

theorem ignoreHandlers_subst (substitution : Subst Const Γ Δ)
    (signature : List (List (Ty Base))) (body : Formula Const Γ) :
    subst substitution (ignoreHandlers signature body) =
      ignoreHandlers signature (subst substitution body) := by
  induction signature generalizing Γ Δ with
  | nil => rfl
  | cons fields rest hypotheses =>
      change Term.lam (subst (Subst.lift substitution) (ignoreHandlers rest (weaken body))) = _
      rw [hypotheses, subst_weaken]
      rfl

theorem encode_subst (substitution : Subst Const Γ Δ)
    (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (arguments : Arguments Const Γ (signature.get occurrence)) :
    subst substitution (encode signature occurrence arguments) =
      encode signature occurrence (substituteArguments substitution _ arguments) := by
  induction signature generalizing Γ Δ with
  | nil => exact Fin.elim0 occurrence
  | cons fields rest hypotheses =>
      rcases occurrence with ⟨n, bound⟩
      cases n with
      | zero =>
          change Term.lam (subst (Subst.lift substitution)
            (ignoreHandlers rest (applyArguments fields (.var .vz)
              (weakenArguments (handlerType fields) fields arguments)))) = _
          rw [ignoreHandlers_subst, applyArguments_subst, substituteArguments_weaken]
          rfl
      | succ n =>
          change Term.lam (subst (Subst.lift substitution)
            (encode rest ⟨n, Nat.lt_of_succ_lt_succ bound⟩
              (weakenArguments (handlerType fields) _ arguments))) = _
          rw [hypotheses, substituteArguments_weaken]
          rfl

#print axioms encode_subst

end Mettapedia.Logic.HOL.FiniteConstructorEncoding
