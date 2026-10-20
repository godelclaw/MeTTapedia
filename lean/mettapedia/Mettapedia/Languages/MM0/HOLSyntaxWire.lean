import Mettapedia.Logic.HOL.Syntax.Names
import Mettapedia.GSLT.LanguageDef.CettaWireTerm

/-!
# Intrinsic HOL syntax in the native MM0 HOL presentation

This is a syntax producer for the existing `hol.mm0` constructors. Binding
names and constant/type interpretations are explicit parameters. The native
checker still checks the resulting declarations, dependencies and proofs;
printing a term grants no typing or theorem authority.

Renaming commutes with printing through the supplied variable naming map.
Freshness of the chosen names is a separate requirement of a concrete export.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLSyntaxWire

open Mettapedia.Logic.HOL
abbrev Wire := Mettapedia.GSLT.LanguageDef.CettaWire.Term

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

def encodeType (base : Base → Wire) : Ty Base → Wire
  | .prop => .application "bool" []
  | .base index => base index
  | .arr domain result => .application "fun" [encodeType base domain, encodeType base result]

def encodeTerm (base : Base → Wire) (constant : ∀ {type}, Const type → Wire)
    (fresh : Nat → String) : {context : Ctx Base} → {type : Ty Base} →
      (names : Names context) → (depth : Nat) → Term Const context type → Wire
  | _, _, names, _, .var index => .symbol (names index)
  | _, _, _, _, .const name => constant name
  | _, _, names, depth, .app function argument => .application "app"
      [encodeTerm base constant fresh names depth function,
       encodeTerm base constant fresh names depth argument]
  | _, _, names, depth, .lam (σ := domain) body => .application "lam"
      [.symbol (fresh depth), encodeType base domain,
       encodeTerm base constant fresh (Names.lift (fresh depth) names) (depth + 1) body]
  | _, _, _, _, .top => .application "T" []
  | _, _, _, _, .bot => .application "F" []
  | _, _, names, depth, .and first second => .application "andc"
      [encodeTerm base constant fresh names depth first,
       encodeTerm base constant fresh names depth second]
  | _, _, names, depth, .or first second => .application "orc"
      [encodeTerm base constant fresh names depth first,
       encodeTerm base constant fresh names depth second]
  | _, _, names, depth, .imp first second => .application "impc"
      [encodeTerm base constant fresh names depth first,
       encodeTerm base constant fresh names depth second]
  | _, _, names, depth, .not formula => .application "notc"
      [encodeTerm base constant fresh names depth formula]
  | _, _, names, depth, .eq (τ := type) first second => .application "eqc"
      [encodeType base type, encodeTerm base constant fresh names depth first,
       encodeTerm base constant fresh names depth second]
  | _, _, names, depth, .all (σ := domain) body => .application "allc"
      [.symbol (fresh depth), encodeType base domain,
       encodeTerm base constant fresh (Names.lift (fresh depth) names) (depth + 1) body]
  | _, _, names, depth, .ex (σ := domain) body => .application "exc"
      [.symbol (fresh depth), encodeType base domain,
       encodeTerm base constant fresh (Names.lift (fresh depth) names) (depth + 1) body]

theorem encodeTerm_rename (base : Base → Wire) (constant : ∀ {type}, Const type → Wire)
    (fresh : Nat → String) {source : Ctx Base} {type : Ty Base}
    (term : Term Const source type) :
    ∀ {target : Ctx Base} (ρ : Rename Base source target)
      (names : Names target) (depth : Nat),
      encodeTerm base constant fresh names depth (rename ρ term) =
        encodeTerm base constant fresh (fun index => names (ρ index)) depth term := by
  induction term <;> intros <;>
    simp_all only [rename, encodeTerm, Names.lift_comp]

end Mettapedia.Languages.MM0.HOLSyntaxWire
