import Mettapedia.OSLF.NativeTypes.GeneratedLogic.StaticDecider
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RegexControls

/-!
# Controls: the typing former reads the declared carriers

A small arithmetic language declares `Int` with the builtin integers, `Name` with the builtin strings and `Expr` with
its own syntax: `Lit` takes an integer, `Var` a name, `Add` two expressions. The regex language declares `Scalar` with
the builtin strings. The static decider answers typing exactly:

| formula | term | answer | checked by |
|---|---|---|---|
| `: Name` | `x` | yes | kernel |
| `: Expr` | `x` | no | kernel |
| `: Expr` | `Var(x)` | yes | kernel |
| `: Expr` | `Var(Var(x))` | no | kernel |
| `: Expr` | `Add(Var(x), Var(y))` | yes | kernel |
| `: Regex` | `rx:literal a` | yes | kernel |
| `: Int` | `42` | yes | `#guard` |
| `: Int` | `x` | no | `#guard` |
| `: Expr` | `Lit(7)` | yes | `#guard` |
| `: Expr` | `Lit(x)` | no | `#guard` |

The integer carrier reads atoms with `String.toInt?`, which recurses on string positions and is not evaluated by the
kernel, so its rows are checked by evaluation. Before the typing former read the carriers, `rx:literal a` had no type:
its argument is an atom of `Scalar`, which the declaration-derived typing does not know.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.CarrierControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)

/-- **A language with the builtin integers and strings.** -/
def arith : LanguageDef :=
  { «name» := "Arith",
    «types» := [⟨"Int", .builtinInt⟩, ⟨"Name", .builtinString⟩, ⟨"Expr", .ast⟩],
    «terms» := [
      { label := "Lit", category := "Expr", params := [.simple "n" (.base "Int")],
        syntaxPattern := [.terminal "Lit", .nonTerminal "n"] },
      { label := "Var", category := "Expr", params := [.simple "x" (.base "Name")],
        syntaxPattern := [.terminal "Var", .nonTerminal "x"] },
      { label := "Add", category := "Expr", params := [.simple "a" (.base "Expr"), .simple "b" (.base "Expr")],
        syntaxPattern := [.terminal "Add", .nonTerminal "a", .nonTerminal "b"] }],
    equations := [],
    «rewrites» := [] }

theorem arith_free : arith.isEquationFree = true := by decide

/-- The static decider of the arithmetic language. -/
def decider : Decider RelationEnv.empty arith := staticDecider arith_free

abbrev atom (text : String) : Pattern := .apply text []

theorem name_typed : (referenceStructure RelationEnv.empty arith).sat Env.closed (.typed (.base "Name")) (atom "x") :=
  (decider.exact (by decide +kernel)).mpr rfl

theorem name_not_expr :
    ¬ (referenceStructure RelationEnv.empty arith).sat Env.closed (.typed (.base "Expr")) (atom "x") := fun holds =>
  Bool.false_ne_true ((decider.exact (answer := false) (by decide +kernel)).mp holds)

theorem variable_typed :
    (referenceStructure RelationEnv.empty arith).sat Env.closed (.typed (.base "Expr")) (.apply "Var" [atom "x"]) :=
  (decider.exact (by decide +kernel)).mpr rfl

theorem nested_variable_untyped :
    ¬ (referenceStructure RelationEnv.empty arith).sat Env.closed (.typed (.base "Expr"))
      (.apply "Var" [.apply "Var" [atom "x"]]) :=
  fun holds => Bool.false_ne_true ((decider.exact (answer := false) (by decide +kernel)).mp holds)

theorem sum_typed :
    (referenceStructure RelationEnv.empty arith).sat Env.closed (.typed (.base "Expr"))
      (.apply "Add" [.apply "Var" [atom "x"], .apply "Var" [atom "y"]]) :=
  (decider.exact (by decide +kernel)).mpr rfl

#guard decider.decide (.typed (.base "Int")) (atom "42") == some true
#guard decider.decide (.typed (.base "Int")) (atom "x") == some false
#guard decider.decide (.typed (.base "Expr")) (.apply "Lit" [atom "7"]) == some true
#guard decider.decide (.typed (.base "Expr")) (.apply "Lit" [atom "x"]) == some false

theorem regex_free : RegexControls.regex.isEquationFree = true := by decide

/-- **A regex literal over a string atom is a regex.** -/
theorem regex_literal_typed :
    (referenceStructure RelationEnv.empty RegexControls.regex).sat Env.closed (.typed (.base "Regex"))
      (.apply "rx:literal" [atom "a"]) :=
  ((staticDecider (relEnv := RelationEnv.empty) regex_free).exact (by decide +kernel)).mpr rfl

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.CarrierControls
