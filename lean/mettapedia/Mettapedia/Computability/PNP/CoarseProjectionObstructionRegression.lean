import Mettapedia.Computability.PNP.CoarseProjectionObstruction

/-!
# Regression checks for the coarse-projection obstruction
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

#check uCoarse_comp_T
#check uFull_T_moves_at
#check bestLocalSuccess_eq_half_of_neutral
#check dominates_iff_half_bound_of_neutral
#check coarseDominationAll_iff_starSW_of_neutral
#check coarseProjectionToy_neutral
#check coarseProjectionToy_not_dominates
#check coarseProjectionToy_not_sufficient
#check coarseProjectionRepair_obstruction_conditional

#print axioms uCoarse_comp_T
#print axioms uFull_T_moves_at
#print axioms bestLocalSuccess_eq_half_of_neutral
#print axioms dominates_iff_half_bound_of_neutral
#print axioms coarseDominationAll_iff_starSW_of_neutral
#print axioms coarseProjectionToy_neutral
#print axioms coarseProjectionToy_not_dominates
#print axioms coarseProjectionToy_not_sufficient
#print axioms coarseProjectionRepair_obstruction_conditional

end Mettapedia.Computability.PNP
