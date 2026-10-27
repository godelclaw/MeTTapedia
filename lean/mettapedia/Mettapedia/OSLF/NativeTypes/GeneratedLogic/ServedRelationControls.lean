import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ServedRelations

/-!
# Controls: a rule that queries a served relation

Unary numerals and a rule `Double(x) ⇒ y if double(x, y)`. No row lists `double`; a dynamic service serves it,
answering a request `double(n, y)` with `double(n, 2n)`.

- With the service registered, `Double(S(Z))` steps to `S(S(Z))` (`served_doubles`) and not to `S(Z)`
  (`served_not_identity`).
- With the relation not registered as dynamic, the service is not consulted and the rule does not fire
  (`unregistered_stuck`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.ServedRelations.Controls

open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax

def zeroRule : GrammarRule := { label := "Z", category := "Nat", params := [], syntaxPattern := [] }
def succRule : GrammarRule := { label := "S", category := "Nat", params := [.simple "n" (.base "Nat")], syntaxPattern := [] }
def doubleRule : GrammarRule :=
  { label := "Double", category := "Nat", params := [.simple "n" (.base "Nat")], syntaxPattern := [] }

/-- `Double(x) ⇒ y if double(x, y)`. -/
def doubling : RewriteRule :=
  { name := "Doubling", typeContext := [("x", .base "Nat"), ("y", .base "Nat")],
    premises := [.relationQuery "double" [.fvar "x", .fvar "y"]],
    left := .apply "Double" [.fvar "x"], right := .fvar "y" }

def numerals : LanguageDef :=
  { name := "Doubling", types := ["Nat"], terms := [zeroRule, succRule, doubleRule], equations := [],
    rewrites := [doubling] }

def zero : Pattern := .apply "Z" []
def succ (n : Pattern) : Pattern := .apply "S" [n]

def value : Pattern → Option ℕ
  | .apply "Z" [] => some 0
  | .apply "S" [n] => (value n).map (· + 1)
  | _ => none

def numeral : ℕ → Pattern
  | 0 => zero
  | n + 1 => succ (numeral n)

/-- What the service serves: `double(n, 2n)` for a numeral `n`. -/
def serve : String → List Pattern → Option (List (List Pattern))
  | "double", [n, _] => (value n).map fun count => [[n, numeral (2 * count)]]
  | _, _ => none

/-- **The doubling service.** -/
def service : GeneralPremise.DynamicProvider where
  Source relation request rows := serve relation request = some rows
  rows? := serve
  rows_exact _ _ _ := Iff.rfl

/-- A provider that registers `double` as served dynamically, and one that does not. -/
def registered : GeneralPremise.ProviderSnapshot := { signatures := [], rows := [], dynamicRelations := ["double"] }
def unregistered : GeneralPremise.ProviderSnapshot := { signatures := [], rows := [] }

def reaches (target : Pattern) : Formula 0 := .possibly .any (.is target)
def steps : Formula 0 := .possibly .any .top

theorem served_doubles :
    ask (servedRelEnv registered service) [] numerals 1 (reaches (succ (succ zero))) (.apply "Double" [succ zero]) none 2 =
      .proved (.exploration 2) := by
  decide +kernel

theorem served_not_identity :
    ask (servedRelEnv registered service) [] numerals 1 (reaches (succ zero)) (.apply "Double" [succ zero]) none 2 =
      .refuted (.closedRegion 2) := by
  decide +kernel

theorem unregistered_stuck :
    ask (servedRelEnv unregistered service) [] numerals 1 steps (.apply "Double" [succ zero]) none 2 =
      .refuted (.closedRegion 2) := by
  decide +kernel

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.ServedRelations.Controls
