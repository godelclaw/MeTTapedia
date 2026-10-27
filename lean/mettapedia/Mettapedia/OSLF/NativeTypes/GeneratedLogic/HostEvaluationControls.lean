import Mettapedia.OSLF.NativeTypes.GeneratedLogic.HostEvaluation
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search

/-!
# Controls: a constructor its host evaluates, at the front door

Unary numerals `Z`, `S(n)` and an addition `Plus(m, n)` that the host evaluates natively (`fold`). The language has no
rule for `Plus`; its host rule asks the relation `host:Plus`. A host that adds numerals answers
`host:Plus(m, n, y)` with `y = m + n`.

- With that host, `Plus(S(Z), S(Z))` steps to `S(S(Z))` (`one_plus_one`) and not to `S(Z)` (`one_plus_one_not_one`).
- Without a host it does not step at all (`no_host_no_step`): nothing says what `Plus` evaluates to.
- The language is the one written: its host rule comes after its own rules, and with no host-evaluated constructor a
  language is unchanged (`HostEvaluation.withHost_of_none`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.HostEvaluationControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open HostEvaluation

def zeroRule : GrammarRule := { label := "Z", category := "Nat", params := [], syntaxPattern := [] }
def succRule : GrammarRule := { label := "S", category := "Nat", params := [.simple "n" (.base "Nat")], syntaxPattern := [] }
def plusRule : GrammarRule :=
  { label := "Plus", category := "Nat", params := [.simple "m" (.base "Nat"), .simple "n" (.base "Nat")],
    syntaxPattern := [], evalPolicy? := some .fold }

/-- **Numerals with a host-evaluated addition.** -/
def numerals : LanguageDef :=
  { name := "Numerals", types := ["Nat"], terms := [zeroRule, succRule, plusRule], equations := [], rewrites := [] }

def zero : Pattern := .apply "Z" []
def succ (n : Pattern) : Pattern := .apply "S" [n]

/-- The value of a numeral. -/
def value : Pattern → Option ℕ
  | .apply "Z" [] => some 0
  | .apply "S" [n] => (value n).map (· + 1)
  | _ => none

/-- The numeral of a value. -/
def numeral : ℕ → Pattern
  | 0 => zero
  | n + 1 => succ (numeral n)

/-- **A host that adds numerals.** -/
def adder : RelationEnv where
  tuples relation request :=
    match relation, request with
    | "host:Plus", [m, n, _] =>
      match value m, value n with
      | some first, some second => [[m, n, numeral (first + second)]]
      | _, _ => []
    | _, _ => []

def steps : Formula 0 := .possibly .any .top
def reaches (target : Pattern) : Formula 0 := .possibly .any (.is target)

def onePlusOne : Pattern := .apply "Plus" [succ zero, succ zero]

theorem one_plus_one :
    ask adder [] (withHost numerals) 1 (reaches (succ (succ zero))) onePlusOne none 2 = .proved (.exploration 2) := by
  decide +kernel

theorem one_plus_one_not_one :
    ask adder [] (withHost numerals) 1 (reaches (succ zero)) onePlusOne none 2 = .refuted (.closedRegion 2) := by
  decide +kernel

theorem no_host_no_step :
    ask RelationEnv.empty [] (withHost numerals) 1 steps onePlusOne none 2 = .refuted (.closedRegion 2) := by
  decide +kernel

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.HostEvaluationControls
