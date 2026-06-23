import Mettapedia.Computability.PNP.PNPv13BoolPairRepeatedFielded

/-!
# PNP v13 Bool-pair: product obstruction corollaries

Concrete, fielded, and same-cell matching blockers obtained from the repeated Bool-pair product violation.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

universe u

/-- Therefore no concrete-cell v13 instantiation can exist for the repeated
two-step Boolean-square model either. -/
theorem not_v13ConcreteSwitchingInstantiated_boolPairRepeatedTwoSteps_by_product_bound :
    ¬ V13ConcreteSwitchingInstantiated
      [v13BoolPairRepeatedStep, v13BoolPairRepeatedStep] := by
  exact not_v13ConcreteSwitchingInstantiated_of_product_bound_violation
    v13BoolPairRepeatedTwoSteps_product_bound_violation

/-- Even the non-revealing one-cell fixed field cannot instantiate both
repeated cuts: the fielded product bound already fails. -/
theorem not_v13FieldSwitchingInstantiated_unitField_repeatedTwoSteps_by_product_bound :
    ¬ V13FieldSwitchingInstantiated
      [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep] := by
  exact not_v13FieldSwitchingInstantiated_of_product_bound_violation
    v13BoolPairUnitFieldedRepeatedTwoSteps_product_bound_violation

/-- The same fielded product failure blocks the operational same-cell matching
obligation itself. -/
theorem not_v13FieldSwitchingFailureMatching_unitField_repeatedTwoSteps_by_product_bound :
    ¬ V13FieldSwitchingFailureMatching
      [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep] := by
  exact not_v13FieldSwitchingFailureMatching_of_product_bound_violation
    v13BoolPairUnitFieldedRepeatedTwoSteps_product_bound_violation

end Mettapedia.Computability.PNP
