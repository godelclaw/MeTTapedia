import Mettapedia.Computability.PNP.PNPv13BoolPairPrefixObstructions

/-!
# PNP v13 Bool-pair: repeated abstract obstruction

Repeated-success counts, prefix-half failure, and abstract v13 product-bound obstruction for two identical cuts.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

universe u

/-- Repeating the same success event does not cut the already-successful
history class at all. -/
theorem v13BoolPairRepeatedStep_success_success_count :
    finiteHistoryCount (Bool × Bool)
      ([v13BoolPairRepeatedStep.successEvent] ++
        [v13BoolPairRepeatedStep.successEvent]) = 2 := by
  decide

/-- The second occurrence of an identical success event fails the positive-mass
prefix half-step: inside the first success event, the same event has conditional
mass `1`, not `1/2`. -/
theorem not_prefixHalfStep_v13BoolPairRepeatedStep_after_success :
    ¬ PrefixHalfStep [v13BoolPairRepeatedStep.successEvent]
      v13BoolPairRepeatedStep.successEvent := by
  rw [PrefixHalfStep, v13BoolPairRepeatedStep_success_count,
    v13BoolPairRepeatedStep_success_success_count]
  decide

/-- Consequently, the v13 atom-ledger certificate cannot be instantiated for
the second repeated switched step. -/
theorem not_v13PrefixInstantiated_boolPairRepeatedStep_second :
    ¬ V13PrefixInstantiated [v13BoolPairRepeatedStep.successEvent]
      v13BoolPairRepeatedStep := by
  exact not_v13PrefixInstantiated_of_not_prefixHalfStep
    not_prefixHalfStep_v13BoolPairRepeatedStep_after_success

/-- The repeated two-step Boolean-square model already violates the global
tower product bound: two identical half-mass events still have half-mass
intersection, not quarter-mass intersection. -/
theorem v13BoolPairRepeatedTwoSteps_product_bound_violation :
    ¬ 2 ^ [v13BoolPairRepeatedStep, v13BoolPairRepeatedStep].length *
        finiteHistoryCount (Bool × Bool)
          (v13SuccessEvents
            [v13BoolPairRepeatedStep, v13BoolPairRepeatedStep]) ≤
      finiteHistoryCount (Bool × Bool) ([] : List (FiniteEvent (Bool × Bool))) := by
  decide

/-- The same product-bound violation appears at the fixed-field layer even if
both repeated cuts use the non-revealing one-cell field. -/
theorem v13BoolPairUnitFieldedRepeatedTwoSteps_product_bound_violation :
    ¬ 2 ^ [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep].length *
        finiteHistoryCount (Bool × Bool)
          (v13FieldedSuccessEvents
            [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep]) ≤
      finiteHistoryCount (Bool × Bool) ([] : List (FiniteEvent (Bool × Bool))) := by
  decide

/-- The whole two-step repeated-coordinate switching claim is therefore not
instantiable in the v13 atom-ledger interface. -/
theorem not_v13SwitchingInstantiated_boolPairRepeatedTwoSteps :
    ¬ V13SwitchingInstantiated
      [v13BoolPairRepeatedStep, v13BoolPairRepeatedStep] := by
  intro h
  exact not_v13PrefixInstantiated_boolPairRepeatedStep_second h.2.1

/-- The same repeated-coordinate switching claim is also blocked at the global
product-bound level, before looking for the first failed prefix. -/
theorem not_v13SwitchingInstantiated_boolPairRepeatedTwoSteps_by_product_bound :
    ¬ V13SwitchingInstantiated
      [v13BoolPairRepeatedStep, v13BoolPairRepeatedStep] := by
  exact not_v13SwitchingInstantiated_of_product_bound_violation
    v13BoolPairRepeatedTwoSteps_product_bound_violation

end Mettapedia.Computability.PNP
