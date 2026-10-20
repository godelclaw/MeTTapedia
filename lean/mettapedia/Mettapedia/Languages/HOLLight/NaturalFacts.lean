import Mettapedia.Logic.HOL.NaturalFacts
import Mettapedia.Languages.HOLLight.HOLSyntaxWire

/-!
# The typed natural statements at the retained HOL Light boundary

The formulas are the shared intrinsic HOL terms. This module supplies source
type/constant names and binder decorations for their native presentation.
The native proof closure, declaration inventory and axiom policy are checked
separately. These strings are claims to compare, never accepted theorems.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.NaturalFacts

open Mettapedia.Logic.HOL
open HOLSyntaxWire
open Mettapedia.Logic.HOL.NaturalFacts (number)

inductive Fact where
  | recursion
  | induction
  | zeroNotSuccessor
  | successorInjective
  | infinity
  deriving DecidableEq, Repr

def facts : List Fact := [.recursion, .induction, .zeroNotSuccessor, .successorInjective, .infinity]

def name : Fact → String
  | .recursion => "num_RECURSION"
  | .induction => "num_INDUCTION"
  | .zeroNotSuccessor => "NOT_SUC"
  | .successorInjective => "SUC_INJ"
  | .infinity => "NAT_CARRIER_INFINITY"

def formula : Fact → ClosedFormula Mettapedia.Logic.HOL.NaturalFacts.Const
  | .recursion => Mettapedia.Logic.HOL.NaturalFacts.recursion
  | .induction => Mettapedia.Logic.HOL.NaturalFacts.induction
  | .zeroNotSuccessor => Mettapedia.Logic.HOL.NaturalFacts.noConfusion
  | .successorInjective => Mettapedia.Logic.HOL.NaturalFacts.successorInjective
  | .infinity => Mettapedia.Logic.HOL.NaturalFacts.infinity

def baseType : Mettapedia.Logic.HOL.NaturalFacts.Base → Wire
  | .natural => .application "T" [.string "num"]
  | .result => .application "V" [.string "A"]

def sourceConstant : {type : Ty Mettapedia.Logic.HOL.NaturalFacts.Base} →
    Mettapedia.Logic.HOL.NaturalFacts.Const type → Wire
  | _, .zero => constant "_0" (encodeType baseType number)
  | _, .successor => constant "SUC" (encodeType baseType (number ⇒ number))
  | _, .numeral => constant "NUMERAL" (encodeType baseType (number ⇒ number))

def binderName : Fact → Nat → String
  | .recursion, 0 => "e"
  | .recursion, 1 => "f"
  | .recursion, 2 => "fn"
  | .recursion, 3 => "n"
  | .induction, 0 => "P"
  | .induction, 1 => "n"
  | .zeroNotSuccessor, 0 => "n"
  | .successorInjective, 0 => "m"
  | .successorInjective, 1 => "n"
  | .infinity, 0 => "s"
  | .infinity, 1 => "m"
  | .infinity, 2 => "n"
  | _, depth => "v" ++ toString depth

def closedNames : Names ([] : Ctx Mettapedia.Logic.HOL.NaturalFacts.Base) :=
  fun {_type} index => nomatch index

def statement (fact : Fact) : Wire :=
  encodeTerm baseType sourceConstant (binderName fact) closedNames 0 (formula fact)

def sequent (fact : Fact) : String := "(thm () " ++ (statement fact).render ++ ")"

theorem names_distinct : (facts.map name).Nodup := by decide +kernel

theorem binder_names_distinct (fact : Fact) : ((List.range 4).map (binderName fact)).Nodup := by
  cases fact <;> decide +kernel

/-- The source statement retains the numeral wrapper even though its
constructed arithmetic interpretation gives that wrapper identity meaning. -/
def bareZeroFormula : ClosedFormula Mettapedia.Logic.HOL.NaturalFacts.Const :=
  .all (σ := number) (.not (.eq (.app (.const .successor) (.var .vz)) (.const .zero)))

theorem bare_zero_statement_distinct :
    statement .zeroNotSuccessor ≠
      encodeTerm baseType sourceConstant (binderName .zeroNotSuccessor) closedNames 0 bareZeroFormula := by
  intro same
  have separated := congrArg (fun wire : Wire => match wire with
    | .application _ [_, .application _ [_, .application _ [_,
        .application _ [_, .application head _]]]] => head
    | _ => "unrecognized") same
  change "A" = "c" at separated
  exact (by decide +kernel : "A" ≠ "c") separated

/-- Finite producer controls. Native proof acceptance and the generic
renaming theorem remain separate from these compiled printing checks. -/
def verdicts : List (String × Bool) :=
  [("native natural facts retain all five named obligations",
      decide (facts.map name = ["num_RECURSION", "num_INDUCTION", "NOT_SUC", "SUC_INJ", "NAT_CARRIER_INFINITY"])),
   ("native fact binder names are distinct through the used nesting depths",
      facts.all fun fact => decide (((List.range 4).map (binderName fact)).Nodup)),
   ("native printing retains the source numeral wrapper",
      (statement .zeroNotSuccessor).render !=
        (encodeTerm baseType sourceConstant (binderName .zeroNotSuccessor) closedNames 0 bareZeroFormula).render)]

end Mettapedia.Languages.HOLLight.NaturalFacts
