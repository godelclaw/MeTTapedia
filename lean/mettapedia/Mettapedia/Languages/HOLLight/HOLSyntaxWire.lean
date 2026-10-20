import Mettapedia.Logic.HOL.Syntax.Names
import Mettapedia.GSLT.LanguageDef.CettaWireTerm

/-!
# Intrinsic HOL syntax in the native HOL Light term format

The existing intrinsic type and variable indices determine every annotation.
The producer chooses names and interpretations for base types and constants;
the native service remains responsible for checking declarations and proofs.
Printing supplies neither theorem authority nor freshness automatically.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.HOLSyntaxWire

open Mettapedia.Logic.HOL
abbrev Wire := Mettapedia.GSLT.LanguageDef.CettaWire.Term

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

def encodeType (base : Base → Wire) : Ty Base → Wire
  | .prop => .application "T" [.string "bool"]
  | .base index => base index
  | .arr domain result => .application "T"
      [.string "fun", encodeType base domain, encodeType base result]

def constant (name : String) (type : Wire) : Wire := .application "c" [.string name, type]
def apply (function argument : Wire) : Wire := .application "A" [function, argument]
def lambda (name : String) (domain body : Wire) : Wire :=
  .application "L" [.application "v" [.string name, domain], body]

def encodeTerm (base : Base → Wire) (interpret : ∀ {type}, Const type → Wire)
    (fresh : Nat → String) : {context : Ctx Base} → {type : Ty Base} →
      Names context → Nat → Term Const context type → Wire
  | _, type, names, _, .var index => .application "v" [.string (names index), encodeType base type]
  | _, _, _, _, .const name => interpret name
  | _, _, names, depth, .app function argument => apply
      (encodeTerm base interpret fresh names depth function)
      (encodeTerm base interpret fresh names depth argument)
  | _, _, names, depth, .lam (σ := domain) body => lambda (fresh depth) (encodeType base domain)
      (encodeTerm base interpret fresh (Names.lift (fresh depth) names) (depth + 1) body)
  | _, _, _, _, .top => constant "T" (encodeType base .prop)
  | _, _, _, _, .bot => constant "F" (encodeType base .prop)
  | _, _, names, depth, .and first second =>
      apply (apply (constant "/\\" (encodeType base (.prop ⇒ .prop ⇒ .prop)))
        (encodeTerm base interpret fresh names depth first))
        (encodeTerm base interpret fresh names depth second)
  | _, _, names, depth, .or first second =>
      apply (apply (constant "\\/" (encodeType base (.prop ⇒ .prop ⇒ .prop)))
        (encodeTerm base interpret fresh names depth first))
        (encodeTerm base interpret fresh names depth second)
  | _, _, names, depth, .imp first second =>
      apply (apply (constant "==>" (encodeType base (.prop ⇒ .prop ⇒ .prop)))
        (encodeTerm base interpret fresh names depth first))
        (encodeTerm base interpret fresh names depth second)
  | _, _, names, depth, .not formula =>
      apply (constant "~" (encodeType base (.prop ⇒ .prop)))
        (encodeTerm base interpret fresh names depth formula)
  | _, _, names, depth, .eq (τ := type) first second =>
      apply (apply (constant "=" (encodeType base (type ⇒ type ⇒ .prop)))
        (encodeTerm base interpret fresh names depth first))
        (encodeTerm base interpret fresh names depth second)
  | _, _, names, depth, .all (σ := domain) body =>
      apply (constant "!" (encodeType base ((domain ⇒ .prop) ⇒ .prop)))
        (lambda (fresh depth) (encodeType base domain)
          (encodeTerm base interpret fresh (Names.lift (fresh depth) names) (depth + 1) body))
  | _, _, names, depth, .ex (σ := domain) body =>
      apply (constant "?" (encodeType base ((domain ⇒ .prop) ⇒ .prop)))
        (lambda (fresh depth) (encodeType base domain)
          (encodeTerm base interpret fresh (Names.lift (fresh depth) names) (depth + 1) body))

theorem encodeTerm_rename (base : Base → Wire) (interpret : ∀ {type}, Const type → Wire)
    (fresh : Nat → String) {source : Ctx Base} {type : Ty Base} (term : Term Const source type) :
    ∀ {target : Ctx Base} (ρ : Rename Base source target) (names : Names target) (depth : Nat),
      encodeTerm base interpret fresh names depth (rename ρ term) =
        encodeTerm base interpret fresh (fun index => names (ρ index)) depth term := by
  induction term <;> intros <;>
    simp_all only [rename, encodeTerm, Names.lift_comp]

end Mettapedia.Languages.HOLLight.HOLSyntaxWire
