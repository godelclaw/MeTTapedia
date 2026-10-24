import Mettapedia.Logic.HOL.GuardedQuantifierTransport
import Mettapedia.Languages.HOLLight.HOLSyntaxWire

/-! # Native statements for typed guarded quantifier transport -/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.GuardedQuantifierTransport

open Mettapedia.Logic.HOL HOLSyntaxWire

abbrev Fact := Mettapedia.Logic.HOL.GuardedQuantifierTransport.Fact

def facts : List Fact := [.universal, .existential]

def name : Fact → String
  | .universal => "GUARDED_FORALL_TRANSPORT"
  | .existential => "GUARDED_EXISTS_TRANSPORT"

def baseType : Mettapedia.Logic.HOL.GuardedQuantifierTransport.Base → Wire
  | .source => .application "V" [.string "A"]
  | .target => .application "V" [.string "B"]

def sourceConstant : {type : Ty Mettapedia.Logic.HOL.GuardedQuantifierTransport.Base} →
    Mettapedia.Logic.HOL.GuardedQuantifierTransport.Const type → Wire
  | _, impossible => impossible.elim

def binderName (_fact : Fact) : Nat → String
  | 0 => "G"
  | 1 => "H"
  | 2 => "f"
  | 3 => "g"
  | 4 => "P"
  | _ => "x"

def closedNames : Names ([] : Ctx Mettapedia.Logic.HOL.GuardedQuantifierTransport.Base) :=
  fun {_type} impossible => nomatch impossible

def statement (fact : Fact) : Wire :=
  encodeTerm baseType sourceConstant (binderName fact) closedNames 0
    (Mettapedia.Logic.HOL.GuardedQuantifierTransport.formula fact)

def sequent (fact : Fact) : String := "(thm () " ++ (statement fact).render ++ ")"

def erasedSequent : String :=
  "(thm () " ++ (encodeTerm baseType sourceConstant (binderName .universal) closedNames 0
    Mettapedia.Logic.HOL.GuardedQuantifierTransport.erasedUniversal).render ++ ")"

theorem names_distinct : (facts.map name).Nodup := by decide +kernel

end Mettapedia.Languages.HOLLight.GuardedQuantifierTransport
