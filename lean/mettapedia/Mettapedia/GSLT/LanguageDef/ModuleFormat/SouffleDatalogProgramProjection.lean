import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogScalars
import Mettapedia.OSLF.MeTTaIL.ReferenceStep

/-! The pure authored source-to-ProgramData compiler language. Its operators
retain source literals and identifiers as subtrees. Recursive work is carried
by step premises, and tail accumulators preserve source order. Native compiler
execution requires its own correspondence; this module grants no admission. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog

namespace CompilerSource

open ScalarSource
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.Commands

#module_file "../../../../../../metta/gslt/module/gold/SouffleDatalog/ProgramProjection.module"
#module_roundtrip ProgramProjection

end CompilerSource

namespace ProgramProjection

open Mettapedia.OSLF.MeTTaIL.Syntax
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

private instance : DecidableEq LanguageDef := fun first second => by
  cases first
  cases second
  exact decidable_of_iff' _ (Iff.of_eq (LanguageDef.mk.injEq _ _ _ _ _ _ _ _ _ _))

def language? : Option LanguageDef := CompilerSource.ProgramProjection.language.toOption
def language : LanguageDef := module_language_view% language?

theorem language_exact : language? = some language := by decide +kernel

theorem scalar_rows : ScalarCore.language.terms ⊆ language.terms := by decide +kernel
theorem authored_rule_count : language.rewrites.length = 48 := by decide +kernel

#print axioms language_exact
#print axioms scalar_rows
#print axioms authored_rule_count

end ProgramProjection
end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog
