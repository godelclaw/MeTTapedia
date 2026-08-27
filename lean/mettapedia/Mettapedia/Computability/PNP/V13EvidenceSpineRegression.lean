import Mettapedia.Computability.PNP.V13EvidenceSpine

/-!
# Regression checks for the v13 finite evidence spine
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

#check Gap_eq_half_abs_conditional
#check static_pairwise_capture
#check DerivativeTelescoping.derivative_telescoping
#check phaseA_gap_le_half_derivative_sum
#check toyV13_gap_eq_half
#check toyV13_phaseA_gap_le_half_derivative_sum

#print axioms Gap_eq_half_abs_conditional
#print axioms static_pairwise_capture
#print axioms DerivativeTelescoping.derivative_telescoping
#print axioms phaseA_gap_le_half_derivative_sum
#print axioms toyV13_gap_eq_half
#print axioms toyV13_phaseA_gap_le_half_derivative_sum

end Mettapedia.Computability.PNP
