import Mettapedia.OSLF.NativeTypes.Instances.Partrec.MachineFormulaComparison
import Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls

open Mettapedia.OSLF.Framework

/-!
# Retained shared-fragment native execution controls

The original finite-depth procedure and the new total-work native machine
are both invoked. A paused query is unknown, normal-form possibility is
refuted, and nested formulas have the same positive and negative answers
as the independently specified machine procedure.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Partrec.MachineFormulaControls

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.Formula
open Mettapedia.OSLF.SatisfactionUndecidable
open Mettapedia.OSLF.NativeTypes.Instances.Partrec.MachineFormulaComparison
open Mettapedia.OSLF.NativeTypes.Instances.Partrec.FormulaComparison (fromLegacy?)
open Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls (source source_admitted stopped stopped_admitted)

def shared (formula : OSLFFormula) (program : Pattern)
    (typed : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.Source [] program) (budget : Nat) : Option (Option Bool) := do
  let generated ← fromLegacy? formula
  return run {} [] generated program typed budget

def completeShared (formula : OSLFFormula) (program : Pattern)
    (typed : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.Source [] program) : Option (Option Bool) := do
  let generated ← fromLegacy? formula
  return run {} [] generated program typed (totalBound {} [] generated program typed)

#guard shared (.dia .top) source source_admitted 0 == some none
#guard shared (.dia .top) source source_admitted 300 == some (some true)
#guard completeShared (.dia .top) stopped stopped_admitted == some (some false)
#guard completeShared (.dia (.dia .top)) source source_admitted == some (some true)
#guard completeShared (.dia (.dia (.dia .top))) source source_admitted == some (some false)
#guard completeShared (.and (.dia .top) (.dia (.dia .top))) source source_admitted ==
  some (some (decideModalSearch (.and (.dia .top) (.dia (.dia .top))) source))
#guard completeShared (.or .bot (.dia .top)) stopped stopped_admitted ==
  some (some (decideModalSearch (.or .bot (.dia .top)) stopped))
#guard shared (.box .top) source source_admitted 300 == none
#guard shared (.mu (.dia (.var 0))) source source_admitted 300 == none

end Mettapedia.OSLF.NativeTypes.Instances.Partrec.MachineFormulaControls
