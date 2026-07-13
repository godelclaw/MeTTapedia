import Mettapedia.Computability.PNP.V13CDENF

/-!
# Regression checks for CD-ENF normalization
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

#check CDENF_semantics
#check observerToEvidence_sat
#check observerToCDENF_sat
#check V13ExecutionTracePrimitiveExpansionTarget
#check toyCDENF_semantics
#check toy_observerToCDENF_sat

#print axioms CDENF_semantics
#print axioms observerToEvidence_sat
#print axioms observerToCDENF_sat
#print axioms V13ExecutionTracePrimitiveExpansionTarget
#print axioms toyCDENF_semantics
#print axioms toy_observerToCDENF_sat

end Mettapedia.Computability.PNP
