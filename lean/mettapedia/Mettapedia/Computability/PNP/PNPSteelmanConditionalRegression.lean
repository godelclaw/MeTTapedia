import Mettapedia.Computability.PNP.PNPSteelmanConditional

/-!
# Regression checks for the PNP steelman conditional
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

#check kernelFlip_exactNeutrality_card
#check toyKernelFlip_exactNeutrality_card
#check noThreadingLemma
#check noThreading_neutral_sufficient_blocks_nontrivial_bit
#check pnp_steelman_conditional
#check toy_pnp_steelman_conditional_nonvacuous

#print axioms kernelFlip_exactNeutrality_card
#print axioms toyKernelFlip_exactNeutrality_card
#print axioms noThreadingLemma
#print axioms noThreading_neutral_sufficient_blocks_nontrivial_bit
#print axioms pnp_steelman_conditional
#print axioms toy_pnp_steelman_conditional_nonvacuous

end Mettapedia.Computability.PNP
