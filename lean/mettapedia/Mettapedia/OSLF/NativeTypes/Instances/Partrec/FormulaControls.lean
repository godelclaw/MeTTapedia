import Mettapedia.OSLF.NativeTypes.Instances.Partrec.FormulaComparison
import Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls

open Mettapedia.OSLF.Framework

/-!
# Independent shared-fragment execution controls

These controls invoke both the original finite-depth machine checker and the
generated occurrence checker. Unsupported translations remain absent and
paused native queries remain unknown, independently of negative verdicts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Partrec.FormulaControls

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.Formula
open Mettapedia.OSLF.SatisfactionUndecidable
open Mettapedia.OSLF.NativeTypes.Instances.Partrec.FormulaComparison

def source : Pattern := Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source
def stopped : Pattern := Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.stopped

def sharedAnswer (formula : OSLFFormula) (program : Pattern) (budget : Nat) : Option (Option Bool) := do
  let generated ← fromLegacy? formula
  return run [] generated program budget

def sharedComplete (formula : OSLFFormula) (program : Pattern) : Option (Option Bool) := do
  let generated ← fromLegacy? formula
  return run [] generated program (effectiveBound [] generated program)

#guard (fromLegacy? (.box .top)).isNone
#guard (fromLegacy? (.mu (.dia (.var 0)))).isNone
#guard (fromLegacy? (.imp .top .bot)).isNone
#guard (fromLegacy? (.atom "arbitrary")).isNone
#guard (fromLegacy? (.dia (.and .top (.or .bot .top)))).isSome
#guard sharedAnswer (.dia .top) source 0 == some none
#guard sharedAnswer (.dia .top) source 300 == some (some true)
#guard sharedComplete (.dia .top) stopped == some (some false)
#guard sharedComplete (.dia (.dia .top)) source == some (some true)
#guard sharedComplete (.dia (.dia (.dia .top))) source == some (some false)
#guard sharedComplete (.and (.dia .top) (.dia (.dia .top))) source ==
  some (some (decideModalSearch (.and (.dia .top) (.dia (.dia .top))) source))
#guard sharedComplete (.or .bot (.dia .top)) stopped ==
  some (some (decideModalSearch (.or .bot (.dia .top)) stopped))
#guard sharedComplete (.and .top (.dia (.dia (.dia .top)))) source ==
  some (some (decideModalSearch (.and .top (.dia (.dia (.dia .top)))) source))

end Mettapedia.OSLF.NativeTypes.Instances.Partrec.FormulaControls
