import Mathlib.Tactic.Sat.FromLRAT

/-! Prototype kernel replay for the first reduced-collapse support mask. -/

namespace Krenn.CollapseSupportCover.LRATMask000Test

lrat_proof unsatisfiable
  (include_str "LRAT/Mask000.cnf")
  (include_str "LRAT/Mask000.lrat")

#check unsatisfiable
#check unsatisfiable.ctx_1
#check unsatisfiable.proof_1
#print axioms unsatisfiable

end Krenn.CollapseSupportCover.LRATMask000Test
