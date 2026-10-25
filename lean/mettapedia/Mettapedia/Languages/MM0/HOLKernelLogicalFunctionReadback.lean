import Mettapedia.Languages.MM0.HOLKernelLogicalOperations
import Mettapedia.Languages.MM0.HOLKernelTermReadbackCoherence

/-!
# Curried logical functions in the maintained native HOL profile

The checked operation profile identifies the seven native function constants
and the stored constructor definitions relating their applications to the
primitive Boolean forms. Their intrinsic readings are ordinary typed HOL
lambdas. Primitive constructors retain their existing reading; the two
presentations agree through explicit beta-conversion evidence.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelLogicalFunctionReadback
open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelTermReadback HOLKernelLogicalOperations
universe u
variable {Const : Ty Unit → Type u} {gamma : Ctx Unit}

def value (operator : Operator) (domain : Ty Unit) : Decoded Const gamma :=
  match operator with
  | .equality => ⟨domain ⇒ domain ⇒ .prop,
      .lam (.lam (.eq (.var (.vs .vz)) (.var .vz)))⟩
  | .conjunction => ⟨.prop ⇒ .prop ⇒ .prop,
      .lam (.lam (.and (.var (.vs .vz)) (.var .vz)))⟩
  | .disjunction => ⟨.prop ⇒ .prop ⇒ .prop,
      .lam (.lam (.or (.var (.vs .vz)) (.var .vz)))⟩
  | .implication => ⟨.prop ⇒ .prop ⇒ .prop,
      .lam (.lam (.imp (.var (.vs .vz)) (.var .vz)))⟩
  | .negation => ⟨.prop ⇒ .prop, .lam (.not (.var .vz))⟩
  | .universal => ⟨(domain ⇒ .prop) ⇒ .prop,
      .lam (.all (.app (.var (.vs .vz)) (.var .vz)))⟩
  | .existential => ⟨(domain ⇒ .prop) ⇒ .prop,
      .lam (.ex (.app (.var (.vs .vz)) (.var .vz)))⟩

variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {signature : Signature sorts terms}

def atoms (profile : Profile sorts terms definitions theorems signature) :
    {gamma : Ctx Unit} → Preterm → Option (Decoded Const gamma)
  | _, .term index =>
      if index = profile.reference .conjunction then some (value .conjunction .prop)
      else if index = profile.reference .disjunction then some (value .disjunction .prop)
      else if index = profile.reference .implication then some (value .implication .prop)
      else if index = profile.reference .negation then some (value .negation .prop)
      else none
  | _, .app (.term index) typeCode =>
      match readType signature.symbol typeCode with
      | none => none
      | some domain =>
          if index = profile.reference .equality then some (value .equality domain)
          else if index = profile.reference .universal then some (value .universal domain)
          else if index = profile.reference .existential then some (value .existential domain)
          else none
  | _, _ => none

def reader (profile : Profile sorts terms definitions theorems signature)
    (constants : Nat → Option (NamedElaboration.SomeConst Const)) (parameters : Nat) : TermReader Const :=
  readTermWith (atoms profile) signature.symbol constants parameters


theorem reader_encode (profile : Profile sorts terms definitions theorems signature)
    (constants : Nat → Option (NamedElaboration.SomeConst Const))
    (indices : ∀ {type}, Const type → Nat) (parameters : Nat)
    (lookup : ∀ {type} (constant : Const type), constants (indices constant) = some ⟨type, constant⟩)
    (bounded : ∀ {type} (constant : Const type), indices constant < parameters)
    {type : Ty Unit} (source : Term Const gamma type)
    (names : Names gamma) (depth : Nat) (scope : InScope parameters names depth) :
    reader profile constants parameters names
      (encodeTerm signature.symbol (fun _ : Unit => Preterm.var 0)
        (fun {_} symbol => Preterm.var (indices symbol)) (fun value => parameters + value)
        names.nameOf depth source) = some ⟨type, source⟩ :=
  readTermWith_encode (atoms profile) signature.symbol signature.symbol_injective constants indices parameters
    lookup bounded source names depth scope

#print axioms reader
end Mettapedia.Languages.MM0.HOLKernelLogicalFunctionReadback
