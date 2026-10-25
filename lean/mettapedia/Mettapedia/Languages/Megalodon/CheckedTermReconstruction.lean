import Mettapedia.Languages.Megalodon.HenkinTermInterpretation

/-!
# Computed reconstruction of checked monomorphic Megalodon terms

Successful native inference supplies an intrinsic HOL term as data, with the
exact native erasure and type annotation. Type and variable reconstruction
compute from the supplied syntax; they do not choose witnesses from an
existence theorem. The constructorwise native term traversal retains the
actual environment lookup in each constant.

This is the data-bearing counterpart of the existing interpretation theorem.
Its admitted fragment and local plain-lookup conditions are unchanged. Prefix
polymorphism has no monomorphic reconstruction in this interface.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.CheckedTermReconstruction

open MathdataKernel HenkinTermInterpretation
open Mettapedia.Logic.HOL

/-- Decode the actual successful type computation. -/
def reconstructType {depth : Nat} {type : Tp} (plain : type.plainWellFormed depth = true) :
    {value : Ty Base // reifyType value = type} :=
  let present : (HenkinTypeFragment.schematicType type).isSome = true :=
    HenkinTypeFragment.instantiate_isSome_of_plain
      (fun index : Nat => (Ty.base (.inl index) : Ty Base)) (Sum.inr : Nat → Base) type plain
  let value := (HenkinTypeFragment.schematicType type).get present
  ⟨value, reifyType_of_schematicType (Option.some_get present).symm⟩

/-- Recover the precise typed variable position, including repeated types. -/
def reconstructVariable {context : Ctx Base} (index : Nat) (type : Tp)
    (lookup : (context.map reifyType)[index]? = some type) :
    Σ value : Ty Base, {index' : Var context value //
      reifyType value = type ∧ variableIndex index' = index} :=
  match context, index with
  | [], _ => by simp at lookup
  | head :: _, 0 => by
      simp only [List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at lookup
      exact ⟨head, .vz, lookup, rfl⟩
  | _ :: tail, index + 1 => by
      simp only [List.map_cons, List.getElem?_cons_succ] at lookup
      obtain ⟨value, v, typed, indexed⟩ := reconstructVariable (context := tail) index type lookup
      exact ⟨value, .vs v, typed, congrArg Nat.succ indexed⟩

/-- Reconstruct the supplied native term without proof search. -/
def reconstruct {environment : Environment} {depth : Nat}
    {context : Ctx Base} (term : Tm) {type : Tp}
    (plainLookups : PlainLookups environment depth term)
    (fragment : supported term = true)
    (accepted : inferTerm environment depth (context.map reifyType) term = some type) :
    Σ value : Ty Base, {interpreted : Term (Constant environment) context value //
      reifyType value = type ∧ erase interpreted = some term} :=
  match term with
  | .db index => by
      obtain ⟨value, v, typed, indexed⟩ := reconstructVariable _ _ accepted
      exact ⟨value, .var v, typed, by simp [erase, indexed]⟩
  | .prim index => by
      obtain ⟨value, typed⟩ := reconstructType
        (plainLookups type accepted)
      exact ⟨value, .const (.primitive index (typed ▸ accepted)), typed, rfl⟩
  | .named name => by
      cases lookup : environment.lookupTerm? name with
      | none => simp [inferTerm, lookup] at accepted
      | some declaration =>
          simp only [inferTerm, lookup, Option.map_some, Option.some.injEq] at accepted
          obtain ⟨value, typed⟩ := reconstructType
            (plainLookups declaration lookup)
          exact ⟨value, .const (.named name declaration lookup typed.symm),
            typed.trans accepted, rfl⟩
  | .app function argument => by
      simp only [supported, Bool.and_eq_true] at fragment
      cases hf : inferTerm environment depth (context.map reifyType) function with
      | none => simp [inferTerm, hf] at accepted
      | some functionType =>
        cases functionType <;> try simp [inferTerm, hf] at accepted
        case arr domain codomain =>
          cases ha : inferTerm environment depth (context.map reifyType) argument with
          | none => simp [ha] at accepted
          | some argumentType =>
              by_cases same : argumentType = domain
              · subst argumentType
                simp only [ha, Option.bind_some, ite_true,
                  Option.some.injEq] at accepted
                obtain ⟨functionValue, f, ftyped, ferased⟩ := reconstruct function plainLookups.1 fragment.1 hf
                obtain ⟨argumentValue, a, atyped, aerased⟩ := reconstruct argument plainLookups.2 fragment.2 ha
                cases functionValue with
                | prop => cases ftyped
                | base index => cases index <;> cases ftyped
                | arr d c =>
                    simp only [reifyType, Tp.arr.injEq] at ftyped
                    have equal : argumentValue = d := reifyType_injective
                      (atyped.trans ftyped.1.symm)
                    subst argumentValue
                    exact ⟨c, .app f a, ftyped.2.trans accepted,
                      by simp [erase, ferased, aerased]⟩
              · simp [ha, same] at accepted
  | .lam domain body => by
      by_cases plain : domain.plainWellFormed depth = true
      · obtain ⟨d, hd⟩ := reconstructType plain
        cases hb : inferTerm environment depth (domain :: context.map reifyType) body with
        | none => simp [inferTerm, plain, hb] at accepted
        | some codomain =>
            simp [inferTerm, plain, hb] at accepted
            obtain ⟨c, b, hc, eb⟩ := reconstruct body plainLookups fragment
              (context := d :: context) (by simpa [hd] using hb)
            exact ⟨.arr d c, .lam b, by simp [reifyType, hd, hc, accepted],
              by simp [erase, hd, eb]⟩
      · simp [inferTerm, plain] at accepted
  | .imp antecedent consequent => by
      simp only [supported, Bool.and_eq_true] at fragment
      cases ha : inferTerm environment depth (context.map reifyType) antecedent with
      | none => simp [inferTerm, ha] at accepted
      | some a =>
        cases a <;> try simp [inferTerm, ha] at accepted
        case prop =>
          cases hc : inferTerm environment depth (context.map reifyType) consequent with
          | none => simp [hc] at accepted
          | some c =>
            cases c <;> try simp [hc] at accepted
            case prop =>
              obtain ⟨av, antecedentTerm, hat, eat⟩ := reconstruct antecedent plainLookups.1 fragment.1 ha
              obtain ⟨cv, ct, hct, ect⟩ := reconstruct consequent plainLookups.2 fragment.2 hc
              have avp : av = .prop := reifyType_injective hat
              have cvp : cv = .prop := reifyType_injective hct
              subst av; subst cv
              exact ⟨.prop, .imp antecedentTerm ct, accepted, by simp [erase, eat, ect]⟩
  | .all domain body => by
      by_cases plain : domain.plainWellFormed depth = true
      · obtain ⟨d, hd⟩ := reconstructType plain
        cases hb : inferTerm environment depth (domain :: context.map reifyType) body with
        | none => simp [inferTerm, plain, hb] at accepted
        | some b =>
          cases b <;> try simp [inferTerm, plain, hb] at accepted
          case prop =>
            obtain ⟨bv, bt, hbt, ebt⟩ := reconstruct body plainLookups fragment
              (context := d :: context) (by simpa [hd] using hb)
            have bvp : bv = .prop := reifyType_injective hbt
            subst bv
            exact ⟨.prop, .all bt, accepted, by simp [erase, hd, ebt]⟩
      · simp [inferTerm, plain] at accepted
  | .typeApp _ _ | .typeLam _ | .typeAll _ => by simp [supported] at fragment

/-- Reconstruction at a specified intrinsic type uses its proved unique
native type annotation. -/
def atType {environment : Environment} {depth : Nat} {context : Ctx Base}
    {type : Ty Base} (raw : Tm) (lookups : PlainLookups environment depth raw)
    (fragment : supported raw = true)
    (accepted : inferTerm environment depth (context.map reifyType) raw = some (reifyType type)) :
    {term : Term (Constant environment) context type // erase term = some raw} := by
  let result := reconstruct raw lookups fragment accepted
  have same : result.1 = type := reifyType_injective result.2.property.1
  exact same ▸ (⟨result.2.val, result.2.property.2⟩ :
    {term : Term (Constant environment) context result.1 // erase term = some raw})

/-- The existing proposition-valued adequacy statement follows from the
computed result, with no stronger admission conditions. -/
theorem reconstruct_exact {environment : Environment} {depth : Nat}
    {context : Ctx Base} (term : Tm) {type : Tp}
    (plainLookups : PlainLookups environment depth term)
    (fragment : supported term = true)
    (accepted : inferTerm environment depth (context.map reifyType) term = some type) :
    reifyType (reconstruct term plainLookups fragment accepted).1 = type ∧
      erase (reconstruct term plainLookups fragment accepted).2.val = some term :=
  (reconstruct term plainLookups fragment accepted).2.property

end Mettapedia.Languages.Megalodon.CheckedTermReconstruction
