import Mathlib.Tactic.Sat.FromLRAT

/-! Prototype kernel replay for the global reduced-collapse support cover. -/

namespace Krenn.CollapseSupportCover.GlobalLRATTest

lrat_proof unsatisfiable
  (include_str "LRAT/GlobalSupportCover.cnf")
  (include_str "LRAT/GlobalSupportCover.lrat")

#check unsatisfiable
#print axioms unsatisfiable

end Krenn.CollapseSupportCover.GlobalLRATTest
