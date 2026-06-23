import Mettapedia.Computability.PNP.PNPv13BoolPairRepeatedAbstract

/-!
# PNP v13 Bool-pair: repeated fielded obstruction

One-cell fixed-field failure and localized bad-cell witnesses for repeated Boolean-square cuts.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

universe u

/-- After the first repeated success event, the one-cell field has no failed
point for the second repeated success test: every point in the accumulated
history is already successful for the repeated event. -/
theorem v13BoolPairUnitField_repeatedSuccess_cell_has_no_failure :
    ∀ ⦃ω' : Bool × Bool⦄,
      allEvents [v13BoolPairRepeatedStep.successEvent] ω' →
        v13BoolPairUnitField.cellOf ω' =
          v13BoolPairUnitField.cellOf (true, true) →
            v13BoolPairRepeatedStep.successEvent.pred ω' := by
  intro ω' hhist _hcell
  exact hhist.1

/-- After conditioning on the first repeated success event, the one-cell field
has two successful points for the same repeated success test. -/
theorem v13BoolPairUnitField_repeatedSuccess_success_count :
    v13ConcreteSuccessCount (Ω := Bool × Bool)
      [v13BoolPairRepeatedStep.successEvent] v13BoolPairRepeatedStep
      v13BoolPairUnitField.cellOf PUnit.unit = 2 := by
  decide

/-- After conditioning on the first repeated success event, the one-cell field
has no failed point for the same repeated success test. -/
theorem v13BoolPairUnitField_repeatedSuccess_failure_count :
    v13ConcreteFailureCount (Ω := Bool × Bool)
      [v13BoolPairRepeatedStep.successEvent] v13BoolPairRepeatedStep
      v13BoolPairUnitField.cellOf PUnit.unit = 0 := by
  decide

/-- The second repeated one-cell cut has an explicit bad cell: failures are
strictly fewer than successes in the only supplied field cell. -/
theorem v13BoolPairUnitField_repeatedSuccess_bad_cell :
    v13ConcreteFailureCount (Ω := Bool × Bool)
        [v13BoolPairRepeatedStep.successEvent] v13BoolPairRepeatedStep
        v13BoolPairUnitField.cellOf PUnit.unit <
      v13ConcreteSuccessCount (Ω := Bool × Bool)
        [v13BoolPairRepeatedStep.successEvent] v13BoolPairRepeatedStep
        v13BoolPairUnitField.cellOf PUnit.unit := by
  rw [v13BoolPairUnitField_repeatedSuccess_failure_count,
    v13BoolPairUnitField_repeatedSuccess_success_count]
  decide

/-- The exact second fixed-field matching obligation fails for two repeated
one-cell cuts. -/
theorem not_v13FieldFailureMatching_unitField_after_repeatedSuccess :
    ¬ V13FieldFailureMatching v13BoolPairUnitField
      [v13BoolPairRepeatedStep.successEvent] v13BoolPairRepeatedStep := by
  exact
    not_v13FieldFailureMatching_of_success_without_sameCell_failure
      (field := v13BoolPairUnitField)
      (hist := [v13BoolPairRepeatedStep.successEvent])
      (step := v13BoolPairRepeatedStep)
      (ω := (true, true))
      (by
        decide)
      (by
        decide)
      v13BoolPairUnitField_repeatedSuccess_cell_has_no_failure

/-- Therefore the exact second fixed-field prefix certificate fails for two
repeated one-cell cuts. -/
theorem not_v13FieldPrefixInstantiation_unitField_after_repeatedSuccess :
    ¬ V13FieldPrefixInstantiation v13BoolPairUnitField
      [v13BoolPairRepeatedStep.successEvent] v13BoolPairRepeatedStep := by
  exact
    not_v13FieldPrefixInstantiation_of_not_failureMatching
      not_v13FieldFailureMatching_unitField_after_repeatedSuccess

/-- The one-cell field certifies the first repeated cut, but the exact second
one-cell field obligation fails after conditioning on the first success. -/
theorem unitField_repeatedTwoSteps_second_step_blocked :
    V13FieldPrefixInstantiation v13BoolPairUnitField
        ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep ∧
      ¬ V13FieldSwitchingInstantiated
        [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep] := by
  refine ⟨v13FieldPrefixInstantiation_unitField_empty, ?_⟩
  exact
    not_v13FieldSwitchingInstantiatedFrom_append_cons_of_not_fieldPrefixInstantiation
      (hist := ([] : List (FiniteEvent (Bool × Bool))))
      (pre := [v13BoolPairUnitFieldedStep])
      (item := v13BoolPairUnitFieldedStep)
      (suffix := [])
      not_v13FieldPrefixInstantiation_unitField_after_repeatedSuccess

/-- In the two-step repeated one-cell fielded model, the localized bad cell is
the unique cell of the second cut. -/
theorem v13BoolPairUnitFieldedRepeatedTwoSteps_second_step_bad_cell :
    ∃ cell : v13BoolPairUnitFieldedStep.field.Cell,
      v13ConcreteFailureCount (Ω := Bool × Bool)
          (([] : List (FiniteEvent (Bool × Bool))) ++
            v13FieldedSuccessEvents [v13BoolPairUnitFieldedStep])
          v13BoolPairUnitFieldedStep.step
          v13BoolPairUnitFieldedStep.field.cellOf cell <
        v13ConcreteSuccessCount (Ω := Bool × Bool)
          (([] : List (FiniteEvent (Bool × Bool))) ++
            v13FieldedSuccessEvents [v13BoolPairUnitFieldedStep])
          v13BoolPairUnitFieldedStep.step
          v13BoolPairUnitFieldedStep.field.cellOf cell := by
  refine ⟨PUnit.unit, ?_⟩
  simpa [v13FieldedSuccessEvents, v13BoolPairUnitFieldedStep] using
    v13BoolPairUnitField_repeatedSuccess_bad_cell

/-- The fielded product failure for two repeated one-cell cuts localizes
exactly to the second step and its unique bad cell. -/
theorem v13BoolPairUnitFieldedRepeatedTwoSteps_product_failure_bad_cell_position :
    ∃ pre item suffix,
      [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep] =
        pre ++ item :: suffix ∧
        ∃ cell : item.field.Cell,
          v13ConcreteFailureCount (Ω := Bool × Bool)
              (([] : List (FiniteEvent (Bool × Bool))) ++
                v13FieldedSuccessEvents pre)
              item.step item.field.cellOf cell <
            v13ConcreteSuccessCount (Ω := Bool × Bool)
              (([] : List (FiniteEvent (Bool × Bool))) ++
                v13FieldedSuccessEvents pre)
              item.step item.field.cellOf cell := by
  refine
    ⟨[v13BoolPairUnitFieldedStep], v13BoolPairUnitFieldedStep, [],
      rfl, ?_⟩
  exact v13BoolPairUnitFieldedRepeatedTwoSteps_second_step_bad_cell

end Mettapedia.Computability.PNP
