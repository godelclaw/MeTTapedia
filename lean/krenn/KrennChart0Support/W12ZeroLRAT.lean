import KrennRawLRAT

/-!
# Kernel replay of the chart-0 `w_12_00 = 0` support contradiction

The DIMACS formula is a necessary Boolean shadow of the frozen chart-0
polynomial equations, augmented by exact support assignments excluded by
strict polynomial unit certificates.  Its last unit clause assumes that
`w_12_00` is zero.  The accompanying LRAT file proves the resulting formula
unsatisfiable.

This module deliberately exposes the proof at `Sat.Fmla.proof` level.  The
separate semantic connector must prove that any chart-0 solution induces a
valuation satisfying this exact formula; the LRAT result alone does not claim
that connection.
-/

namespace Krenn.Chart0Support.W12ZeroLRAT

raw_lrat_proof contradiction
  (include_str "LRAT/W12Zero.cnf")
  (include_str "LRAT/W12Zero.lrat")

#check contradiction
#print axioms contradiction

end Krenn.Chart0Support.W12ZeroLRAT
