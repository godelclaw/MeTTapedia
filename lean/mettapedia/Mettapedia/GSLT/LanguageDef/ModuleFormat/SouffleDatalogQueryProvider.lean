import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogQueryKernel
import Mettapedia.OSLF.Framework.GeneralCanonicalQueryAgreement

/-! The finite provider consumed by typed premise execution is the same
ordered snapshot used by the lowered reference relation. Tuple-list equality
retains duplicate validation rows as well as relation membership. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.QueryKernel

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement

theorem provider_tuples_exact (known : List Pattern) (requested : String) (arguments : List Pattern) :
    (providerRelEnv (provider known)).tuples requested arguments =
      (environment known).tuples requested arguments := by
  by_cases same : requested = relation
  · subst requested
    simp [providerRelEnv, provider, environment, List.filterMap_map]
  · have reverse : relation ≠ requested := Ne.symm same
    simp [providerRelEnv, provider, environment, same, reverse, List.filterMap_map]

theorem provider_reads (known : List Pattern) : ReadsProvider (environment known) (provider known) := by
  intro signature present arguments tuple
  rw [← provider_tuples_exact known signature.relation arguments]
  exact providerRelEnv_reads (provider known) signature present arguments tuple

theorem provider_row_positions (known : List Pattern) :
    (provider known).rows.map (·.values) = known.map (fun fact => [fact]) := by
  simp [provider, List.map_map, Function.comp_def]

#print axioms provider_tuples_exact
#print axioms provider_reads
#print axioms provider_row_positions

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.QueryKernel
