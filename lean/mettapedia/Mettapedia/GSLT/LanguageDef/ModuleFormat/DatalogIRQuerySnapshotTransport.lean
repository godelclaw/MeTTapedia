import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRQueryNative

/-! The compiled query code is independent of a round's fact rows. Reusing
that code does not discharge row admission: each replacement snapshot must
still pass the typed provider check. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Query.Native

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

theorem compiled_rules_rows_independent (known : List Pattern) :
    (plan known).rules = (plan []).rules := by rfl

theorem compiled_equations_rows_independent (known : List Pattern) :
    (plan known).equations = (plan []).equations := by rfl

theorem free_context_rows_independent (known : List Pattern) :
    (snapshot known).freeTypes = (snapshot []).freeTypes := rfl

theorem signatures_rows_independent (known : List Pattern) :
    (snapshot known).provider.signatures = (snapshot []).provider.signatures := rfl

theorem replacement_snapshot_admitted (before after : List Pattern) (name : String)
    (closed : GeneralPremise.checkProviderClosed compiledLanguage (snapshot after).free (provider after) = true)
    (names : CompleteEmissionSupport.entryChecks name = true) :
    (plan after).rules = (plan before).rules ∧
      CompleteEmission.Emitted (spec after) name .classes := by
  constructor
  · rw [compiled_rules_rows_independent after,compiled_rules_rows_independent before]
  · exact emission_admitted after name closed names

#print axioms compiled_rules_rows_independent
#print axioms replacement_snapshot_admitted

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Query.Native
