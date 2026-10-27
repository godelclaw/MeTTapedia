import Mettapedia.Logic.HOL.ConstructorDataPredicates

/-!
# Predicates built from curried field programs

Application retains the ordered typed field telescope. Constant predicates,
equality with a curried result, conjunction and finite choice share the
substitution-aware argument abstraction. Their denotation laws expose the
original field values rather than a decoded or chosen representative.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.CurriedPredicates

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open FiniteConstructorEncoding
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Δ : Ctx Base}

abbrev FunctionType (fields : List (Ty Base)) (result : Ty Base) := fields.foldr Ty.arr result

def applyFields {result : Ty Base} : (fields : List (Ty Base)) →
    Term Const Γ (FunctionType fields result) → Arguments Const Γ fields → Term Const Γ result
  | [], function, _ => function
  | _ :: rest, function, arguments => applyFields rest (.app function arguments.1) arguments.2

theorem applyFields_subst {result : Ty Base} (rho : Subst Const Γ Δ)
    (fields : List (Ty Base)) (function : Term Const Γ (FunctionType fields result))
    (arguments : Arguments Const Γ fields) :
    subst rho (applyFields fields function arguments) =
      applyFields fields (subst rho function) (substituteArguments rho fields arguments) := by
  induction fields with
  | nil => rfl
  | cons first rest hypotheses => exact hypotheses (.app function arguments.1) arguments.2

variable (model : HenkinModel.{u,v,w} Base Const)

def applyValues {result : Ty Base} : (fields : List (Ty Base)) →
    Ty.denote model.Carrier (FunctionType fields result) → Env (Ty.denote model.Carrier) fields →
      Ty.denote model.Carrier result
  | [], function, _ => function
  | _ :: rest, function, data => applyValues rest (function data.1) data.2

theorem applyFields_denote {result : Ty Base} (fields : List (Ty Base))
    (function : Term Const Γ (FunctionType fields result)) (arguments : Arguments Const Γ fields)
    (values : model.Valuation Γ) :
    model.denote (applyFields fields function arguments) values =
      applyValues model fields (model.denote function values) (denoteArguments model fields arguments values) := by
  induction fields with
  | nil => rfl
  | cons first rest hypotheses => exact hypotheses (.app function arguments.1) arguments.2

def holds (fields : List (Ty Base)) (condition : Term Const Γ (handlerType fields))
    (values : model.Valuation Γ) (data : Env (Ty.denote model.Carrier) fields) : Prop :=
  (TypeTheory.FiniteConstructorEncoding.apply (Ty.denote model.Carrier) fields
    (handlerEquivalence model fields (model.denote condition values)) data).down

def constant (fields : List (Ty Base)) (formula : Formula Const Γ) : Term Const Γ (handlerType fields) :=
  abstractArguments fields (fun rho _ => subst rho formula)

theorem constant_holds (fields : List (Ty Base)) (formula : Formula Const Γ)
    (values : model.Valuation Γ) (data : Env (Ty.denote model.Carrier) fields) :
    holds model fields (constant fields formula) values data ↔ (model.denote formula values).down := by
  have law := abstractArguments_denote model fields (fun rho _ => subst rho formula)
    (fun values _ => model.denote formula values)
    (fun rho _ later => Soundness.denote_subst model rho formula later) values data
  exact Iff.of_eq (congrArg ULift.down law)

def equalTo {result : Ty Base} (fields : List (Ty Base))
    (function : Term Const Γ (FunctionType fields result)) (expected : Term Const Γ result) :
    Term Const Γ (handlerType fields) :=
  abstractArguments fields (fun rho arguments =>
    .eq (applyFields fields (subst rho function) arguments) (subst rho expected))

theorem equalTo_holds (full : model.FullDomains) {result : Ty Base} (fields : List (Ty Base))
    (function : Term Const Γ (FunctionType fields result)) (expected : Term Const Γ result)
    (values : model.Valuation Γ) (data : Env (Ty.denote model.Carrier) fields) :
    holds model fields (equalTo fields function expected) values data ↔
      applyValues model fields (model.denote function values) data = model.denote expected values := by
  have law := abstractArguments_denote model fields
    (fun rho arguments => Term.eq (applyFields fields (subst rho function) arguments) (subst rho expected))
    (fun values data => ULift.up (applyValues model fields (model.denote function values) data =
      model.denote expected values))
    (by
      intro Ξ rho arguments later
      apply congrArg ULift.up
      apply propext
      change model.Eqv _ (model.denote (applyFields fields (subst rho function) arguments) later)
        (model.denote (subst rho expected) later) ↔ _
      rw [model.eqv_iff_eq_of_fullDomains full, applyFields_denote,
        Soundness.denote_subst, Soundness.denote_subst]
      rfl) values data
  exact Iff.of_eq (congrArg ULift.down law)

def conjoin (fields : List (Ty Base))
    (first second : Term Const Γ (handlerType fields)) : Term Const Γ (handlerType fields) :=
  abstractArguments fields (fun rho arguments =>
    .and (applyArguments fields (subst rho first) arguments)
      (applyArguments fields (subst rho second) arguments))

theorem conjoin_holds (fields : List (Ty Base))
    (first second : Term Const Γ (handlerType fields))
    (values : model.Valuation Γ) (data : Env (Ty.denote model.Carrier) fields) :
    holds model fields (conjoin fields first second) values data ↔
      holds model fields first values data ∧ holds model fields second values data := by
  have law := abstractArguments_denote model fields
    (fun rho arguments => Term.and (applyArguments fields (subst rho first) arguments)
      (applyArguments fields (subst rho second) arguments))
    (fun values data => ULift.up (holds model fields first values data ∧ holds model fields second values data))
    (by
      intro Ξ rho arguments later
      change ULift.up ((model.denote (applyArguments fields (subst rho first) arguments) later).down ∧
        (model.denote (applyArguments fields (subst rho second) arguments) later).down) = _
      rw [applyArguments_denote, applyArguments_denote, Soundness.denote_subst, Soundness.denote_subst]
      rfl) values data
  exact Iff.of_eq (congrArg ULift.down law)

def choose (fields : List (Ty Base)) {count : Nat}
    (conditions : Fin count → Term Const Γ (handlerType fields)) : Term Const Γ (handlerType fields) :=
  abstractArguments fields (fun rho arguments => any
    (List.ofFn (fun position => applyArguments fields (subst rho (conditions position)) arguments)))

theorem choose_holds (fields : List (Ty Base)) {count : Nat}
    (conditions : Fin count → Term Const Γ (handlerType fields))
    (values : model.Valuation Γ) (data : Env (Ty.denote model.Carrier) fields) :
    holds model fields (choose fields conditions) values data ↔
      ∃ position, holds model fields (conditions position) values data := by
  have law := abstractArguments_denote model fields
    (fun rho arguments => any (List.ofFn
      (fun position => applyArguments fields (subst rho (conditions position)) arguments)))
    (fun values data => ULift.up (∃ position, holds model fields (conditions position) values data))
    (by
      intro Ξ rho arguments later
      apply ULift.ext
      apply propext
      rw [any_denote]
      constructor
      · rintro ⟨formula, member, valid⟩
        obtain ⟨position, rfl⟩ := List.mem_ofFn.mp member
        rw [applyArguments_denote, Soundness.denote_subst] at valid
        exact ⟨position, valid⟩
      · rintro ⟨position, valid⟩
        refine ⟨_, List.mem_ofFn.mpr ⟨position, rfl⟩, ?_⟩
        rw [applyArguments_denote, Soundness.denote_subst]
        exact valid) values data
  exact Iff.of_eq (congrArg ULift.down law)

def existsValue {bound : Ty Base} (fields : List (Ty Base))
    (predicate : Term Const Γ (bound ⇒ handlerType fields)) : Term Const Γ (handlerType fields) :=
  abstractArguments fields (fun rho arguments =>
    .ex (applyArguments fields (.app (weaken (subst rho predicate)) (.var .vz))
      (weakenArguments bound fields arguments)))

theorem existsValue_holds (full : model.FullDomains) {bound : Ty Base}
    (fields : List (Ty Base)) (predicate : Term Const Γ (bound ⇒ handlerType fields))
    (values : model.Valuation Γ) (data : Env (Ty.denote model.Carrier) fields) :
    holds model fields (existsValue fields predicate) values data ↔
      ∃ value : Ty.denote model.Carrier bound,
        (TypeTheory.FiniteConstructorEncoding.apply (Ty.denote model.Carrier) fields
          (handlerEquivalence model fields (model.denote predicate values value)) data).down := by
  have law := abstractArguments_denote model fields
    (fun rho arguments => Term.ex (applyArguments fields
      (.app (weaken (subst rho predicate)) (.var .vz)) (weakenArguments bound fields arguments)))
    (fun values data => ULift.up (∃ value : Ty.denote model.Carrier bound,
      (TypeTheory.FiniteConstructorEncoding.apply (Ty.denote model.Carrier) fields
        (handlerEquivalence model fields (model.denote predicate values value)) data).down))
    (by
      intro Ξ rho arguments later
      have admitted : ∀ type value, model.adm type value := full
      apply ULift.ext
      apply propext
      change (∃ value, model.adm bound value ∧
        (model.denote (applyArguments fields (.app (weaken (subst rho predicate)) (.var .vz))
          (weakenArguments bound fields arguments)) (model.extend later value)).down) ↔ _
      simp only [admitted, true_and, applyArguments_denote, denoteArguments_weaken]
      apply exists_congr
      intro value
      change (TypeTheory.FiniteConstructorEncoding.apply _ fields
        (handlerEquivalence model fields
          (model.denote (weaken (subst rho predicate)) (model.extend later value) value))
        (denoteArguments model fields arguments later)).down ↔ _
      rw [Soundness.denote_weaken, Soundness.denote_subst]
      rfl) values data
  exact Iff.of_eq (congrArg ULift.down law)

#print axioms applyFields_denote
#print axioms equalTo_holds
#print axioms choose_holds
#print axioms existsValue_holds

end Mettapedia.Logic.HOL.CurriedPredicates
