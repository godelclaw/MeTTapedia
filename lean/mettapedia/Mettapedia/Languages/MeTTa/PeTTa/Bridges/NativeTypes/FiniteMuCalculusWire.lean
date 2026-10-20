import Mettapedia.Logic.ModalMuCalculus
import Mettapedia.GSLT.LanguageDef.CettaWireTerm

/-!
# Wire representation of the existing modal fixed-point formulas

This representation serializes `ModalMuCalculus.Formula`. It introduces no
second formula datatype. Free predicate variables are finite environment
entries; the existing de Bruijn indices shift beneath each fixed-point binder.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.FiniteMuCalculusWire

open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.GSLT.LanguageDef.CettaWire

universe u
variable {Action : Type u}

def formulaTerm (action : Action → Term) : {n : Nat} → Formula Action n → Term
  | _, .tt => .symbol "NativeTop"
  | _, .ff => .symbol "NativeBottom"
  | _, .var index => .application "NativeVar" [.natural index.val]
  | _, .neg inner => .application "NativeNeg" [formulaTerm action inner]
  | _, .conj left right => .application "NativeConj" [formulaTerm action left, formulaTerm action right]
  | _, .disj left right => .application "NativeDisj" [formulaTerm action left, formulaTerm action right]
  | _, .diamond label inner => .application "NativeDiamond" [action label, formulaTerm action inner]
  | _, .box label inner => .application "NativeBox" [action label, formulaTerm action inner]
  | _, .mu body => .application "NativeMu" [formulaTerm action body]
  | _, .nu body => .application "NativeNu" [formulaTerm action body]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.FiniteMuCalculusWire
