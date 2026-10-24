import Mettapedia.Logic.HOL.BooleanFacts
import Mettapedia.Languages.HOLLight.HOLSyntaxWire

/-!
# Native HOL Light presentation of the typed Boolean facts

These are typed claims for independent replay. Their source-data meaning is
qualified by the selected Boolean reading; printing a claim is not a proof.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.BooleanFacts

open Mettapedia.Logic.HOL
open HOLSyntaxWire

abbrev Fact := Mettapedia.Logic.HOL.BooleanFacts.Fact

def facts : List Fact := [.recursion, .induction, .separation, .cases, .finite]

def name : Fact → String
  | .recursion => "BOOL_DATA_RECURSION"
  | .induction => "BOOL_DATA_INDUCTION"
  | .separation => "BOOL_DATA_DISTINCT"
  | .cases => "BOOL_DATA_CASES"
  | .finite => "BOOL_DATA_FINITE"

def baseType : Mettapedia.Logic.HOL.BooleanFacts.Base → Wire
  | .result => .application "V" [.string "A"]

def sourceConstant : {type : Ty Mettapedia.Logic.HOL.BooleanFacts.Base} →
    Mettapedia.Logic.HOL.BooleanFacts.Const type → Wire
  | _, impossible => impossible.elim

def binderName : Fact → Nat → String
  | .recursion, 0 => "e0"
  | .recursion, 1 => "e1"
  | .recursion, 2 => "fn"
  | .induction, 0 => "P"
  | .induction, 1 => "b"
  | .cases, 0 => "b"
  | .finite, 0 => "f"
  | .finite, 1 => "x"
  | .finite, 2 => "y"
  | _, depth => "v" ++ toString depth

def closedNames : Names ([] : Ctx Mettapedia.Logic.HOL.BooleanFacts.Base) :=
  fun {_type} impossible => nomatch impossible

def statement (fact : Fact) : Wire :=
  encodeTerm baseType sourceConstant (binderName fact) closedNames 0
    (Mettapedia.Logic.HOL.BooleanFacts.formula fact)

def sequent (fact : Fact) : String := "(thm () " ++ (statement fact).render ++ ")"

theorem names_distinct : (facts.map name).Nodup := by decide +kernel

end Mettapedia.Languages.HOLLight.BooleanFacts
