import Mettapedia.Logic.HOL.FiniteConstructorEncoding
import Mettapedia.Logic.HOL.TypeSubstitutionSemantics

/-!
# Source predicates recognizing encoded constructor data

Typed argument abstraction and existential application follow a finite field
telescope. A constructor guard quantifies over those fields and compares the
payload with the emitted constructor encoding. Its interpretation is proved
against the actual encoding; full domains are explicit where function equality
and quantification are read as ordinary equality and unrestricted existence.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.FiniteConstructorEncoding

open Mettapedia.TypeTheory.IndexedPolynomial.Description
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v}

def abstractArguments : {Γ : Ctx Base} → (fields : List (Ty Base)) →
    (∀ {Δ : Ctx Base}, Subst Const Γ Δ → Arguments Const Δ fields → Formula Const Δ) →
    Term Const Γ (handlerType fields)
  | _, [], body => body (fun index => .var index) PUnit.unit
  | _, _type :: rest, body => .lam (abstractArguments rest
      (fun rho arguments => body (fun index => rho (.vs index))
        (rho .vz, arguments)))

def existsArguments : {Γ : Ctx Base} → (fields : List (Ty Base)) →
    Term Const Γ (handlerType fields) → Formula Const Γ
  | _, [], predicate => predicate
  | _, _ :: rest, predicate =>
      .ex (existsArguments rest (.app (weaken predicate) (.var .vz)))

def constructorPredicate {Γ : Ctx Base} (signature : List (List (Ty Base)))
    (occurrence : Fin signature.length) (payload : Term Const Γ (payloadType signature)) :
    Term Const Γ (handlerType (signature.get occurrence)) :=
  abstractArguments (signature.get occurrence)
    (fun rho arguments => .eq (subst rho payload) (encode signature occurrence arguments))

def constructorGuard {Γ : Ctx Base} (signature : List (List (Ty Base)))
    (occurrence : Fin signature.length) (payload : Term Const Γ (payloadType signature)) : Formula Const Γ :=
  existsArguments (signature.get occurrence) (constructorPredicate signature occurrence payload)

variable (model : HenkinModel.{u,v,w} Base Const)

theorem abstractArguments_denote {Γ : Ctx Base} (fields : List (Ty Base))
    (body : ∀ {Δ : Ctx Base}, Subst Const Γ Δ → Arguments Const Δ fields → Formula Const Δ)
    (meaning : model.Valuation Γ → Env (Ty.denote model.Carrier) fields → Ty.denote model.Carrier .prop)
    (bodyMeaning : ∀ {Δ : Ctx Base} (rho : Subst Const Γ Δ)
      (arguments : Arguments Const Δ fields) (values : model.Valuation Δ),
      model.denote (body rho arguments) values =
        meaning (fun index => model.denote (rho index) values) (denoteArguments model fields arguments values))
    (values : model.Valuation Γ) (data : Env (Ty.denote model.Carrier) fields) :
    TypeTheory.FiniteConstructorEncoding.apply (Ty.denote model.Carrier) fields
      (handlerEquivalence model fields (model.denote (abstractArguments fields body) values)) data =
      meaning values data := by
  induction fields generalizing Γ with
  | nil =>
      cases data
      exact bodyMeaning (fun index => .var index) PUnit.unit values
  | cons type rest hypotheses =>
      change TypeTheory.FiniteConstructorEncoding.apply (Ty.denote model.Carrier) rest
        (handlerEquivalence model rest
          (model.denote (abstractArguments rest
            (fun rho arguments => body (fun index => rho (.vs index))
              (rho .vz, arguments))) (model.extend values data.1))) data.2 = _
      exact hypotheses _
        (fun later rest => meaning (fun index => later (.vs index)) (later .vz, rest))
        (fun rho arguments later => bodyMeaning (fun index => rho (.vs index))
          (rho .vz, arguments) later)
        (model.extend values data.1) data.2

theorem existsArguments_denote (full : model.FullDomains) {Γ : Ctx Base}
    (fields : List (Ty Base)) (predicate : Term Const Γ (handlerType fields))
    (values : model.Valuation Γ) :
    (model.denote (existsArguments fields predicate) values).down ↔
      ∃ data : Env (Ty.denote model.Carrier) fields,
        (TypeTheory.FiniteConstructorEncoding.apply (Ty.denote model.Carrier) fields
          (handlerEquivalence model fields (model.denote predicate values)) data).down := by
  induction fields generalizing Γ with
  | nil => exact ⟨fun present => ⟨PUnit.unit, present⟩, fun ⟨_, present⟩ => present⟩
  | cons type rest hypotheses =>
      change (∃ first, model.adm type first ∧
        (model.denote (existsArguments rest (.app (weaken predicate) (.var .vz)))
          (model.extend values first)).down) ↔ _
      constructor
      · rintro ⟨first, _, tailPresent⟩
        obtain ⟨tail, present⟩ := (hypotheses _ _).mp tailPresent
        refine ⟨(first, tail), ?_⟩
        change (TypeTheory.FiniteConstructorEncoding.apply (Ty.denote model.Carrier) rest
          (handlerEquivalence model rest (model.denote predicate values first)) tail).down
        change (TypeTheory.FiniteConstructorEncoding.apply (Ty.denote model.Carrier) rest
          (handlerEquivalence model rest
            (model.denote (weaken predicate) (model.extend values first) first)) tail).down at present
        rw [Soundness.denote_weaken] at present
        exact present
      · rintro ⟨⟨first, tail⟩, present⟩
        refine ⟨first, full _ _, (hypotheses _ _).mpr ⟨tail, ?_⟩⟩
        change (TypeTheory.FiniteConstructorEncoding.apply (Ty.denote model.Carrier) rest
          (handlerEquivalence model rest
            (model.denote (weaken predicate) (model.extend values first) first)) tail).down
        rw [Soundness.denote_weaken]
        exact present

theorem constructorPredicate_denote (full : model.FullDomains) {Γ : Ctx Base}
    (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (payload : Term Const Γ (payloadType signature)) (values : model.Valuation Γ)
    (data : Env (Ty.denote model.Carrier) (signature.get occurrence)) :
    (TypeTheory.FiniteConstructorEncoding.apply (Ty.denote model.Carrier) (signature.get occurrence)
      (handlerEquivalence model _ (model.denote (constructorPredicate signature occurrence payload) values)) data).down ↔
      payloadEquivalence model signature (model.denote payload values) =
        TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) signature ⟨occurrence, data⟩ := by
  have generated := abstractArguments_denote model (signature.get occurrence)
    (fun rho arguments => .eq (subst rho payload) (encode signature occurrence arguments))
    (fun values data => ULift.up (payloadEquivalence model signature (model.denote payload values) =
      TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) signature ⟨occurrence, data⟩))
    (by
      intro Δ rho arguments later
      apply congrArg ULift.up
      apply propext
      change model.Eqv _ (model.denote (subst rho payload) later)
        (model.denote (encode signature occurrence arguments) later) ↔ _
      rw [model.eqv_iff_eq_of_fullDomains full, Soundness.denote_subst]
      rw [← (payloadEquivalence model signature).injective.eq_iff]
      rw [encode_denote]
      rfl) values data
  exact Iff.of_eq (congrArg ULift.down generated)

theorem constructorGuard_denote (full : model.FullDomains) {Γ : Ctx Base}
    (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (payload : Term Const Γ (payloadType signature)) (values : model.Valuation Γ) :
    (model.denote (constructorGuard signature occurrence payload) values).down ↔
      ∃ data : Env (Ty.denote model.Carrier) (signature.get occurrence),
        payloadEquivalence model signature (model.denote payload values) =
          TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) signature ⟨occurrence, data⟩ := by
  rw [constructorGuard, existsArguments_denote model full]
  exact exists_congr (fun data => constructorPredicate_denote model full signature occurrence payload values data)

def any {Γ : Ctx Base} (formulas : List (Formula Const Γ)) : Formula Const Γ :=
  formulas.foldr Term.or .bot

def validGuard {Γ : Ctx Base} (signature : List (List (Ty Base)))
    (payload : Term Const Γ (payloadType signature)) : Formula Const Γ :=
  any (List.ofFn (fun occurrence => constructorGuard signature occurrence payload))

theorem any_denote {Γ : Ctx Base} (formulas : List (Formula Const Γ))
    (values : model.Valuation Γ) :
    (model.denote (any formulas) values).down ↔
      ∃ formula ∈ formulas, (model.denote formula values).down := by
  induction formulas with
  | nil => simp [any, HenkinModel.denote, PreModel.denote]
  | cons first rest hypotheses =>
      change (model.denote first values).down ∨ (model.denote (any rest) values).down ↔ _
      rw [hypotheses]
      simp only [List.mem_cons, exists_eq_or_imp]

theorem validGuard_denote (full : model.FullDomains) {Γ : Ctx Base}
    (signature : List (List (Ty Base))) (payload : Term Const Γ (payloadType signature))
    (values : model.Valuation Γ) :
    (model.denote (validGuard signature payload) values).down ↔
      TypeTheory.FiniteConstructorEncoding.Valid (Ty.denote model.Carrier) signature
        (payloadEquivalence model signature (model.denote payload values)) := by
  rw [validGuard, any_denote]
  constructor
  · rintro ⟨formula, present, holds⟩
    obtain ⟨occurrence, rfl⟩ := List.mem_ofFn.mp present
    obtain ⟨data, same⟩ := (constructorGuard_denote model full signature occurrence payload values).mp holds
    exact ⟨⟨occurrence, data⟩, same.symm⟩
  · rintro ⟨⟨occurrence, data⟩, same⟩
    refine ⟨constructorGuard signature occurrence payload, List.mem_ofFn.mpr ⟨occurrence, rfl⟩, ?_⟩
    exact (constructorGuard_denote model full signature occurrence payload values).mpr ⟨data, same.symm⟩

#print axioms abstractArguments_denote
#print axioms constructorGuard_denote
#print axioms validGuard_denote

end Mettapedia.Logic.HOL.FiniteConstructorEncoding
