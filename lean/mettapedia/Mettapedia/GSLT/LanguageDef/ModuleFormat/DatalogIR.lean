import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews
import Mettapedia.Languages.Datalog.Syntax

/-! Source-independent Datalog program signatures. Symbols and identifiers
use declared string carriers; numbers, unsigned values and IEEE words use
integer carriers with their semantic width checks kept explicit. Qualified
names are vectors of identifiers. No source grammar is imported. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat

namespace DatalogAuthoring
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
#module_file "../../../../../../metta/gslt/module/DatalogIR.module"
#module_roundtrip DatalogIR
end DatalogAuthoring

namespace DatalogIR

open Mettapedia.OSLF.MeTTaIL.Syntax
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

private instance : DecidableEq LanguageDef := fun first second => by
  cases first
  cases second
  exact decidable_of_iff' _ (Iff.of_eq (LanguageDef.mk.injEq _ _ _ _ _ _ _ _ _ _))

def language? : Option LanguageDef := DatalogAuthoring.DatalogIR.language.toOption
def language : LanguageDef := module_language_view% language?

theorem language_exact : language? = some language := by decide +kernel

theorem payload_sorts_declared : ∀ name ∈
    ["DlSymbol","DlInteger","DlUnsigned","DlFloat","DlIdentifier","DlQualifiedName"],
    name ∈ language.types := by decide +kernel

theorem no_source_constructors : language.terms.all
    (fun declaration => !declaration.label.startsWith "dl-src:" && !declaration.label.startsWith "dl-scalar:") = true := by
  decide +kernel

#guard language.types.length == 20
#guard language.terms.length == 33
#guard language.validate.isEmpty

#print axioms language_exact
#print axioms no_source_constructors

end DatalogIR
end Mettapedia.GSLT.LanguageDef.ModuleFormat
