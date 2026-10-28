import Mettapedia.Computability.PNP.PNPv13SwitchingInstantiationRegressionSequential

/-!
# Regression checks for the PNP v13 switching instantiation interface

This module contains the Bool-pair counterexample regression checks.
-/

namespace Mettapedia.Computability.PNP.PNPv13SwitchingInstantiationRegression

open Mettapedia.Computability.PNP

universe u

theorem first_step_global_half_regression :
    PrefixHalfStep ([] : List (FiniteEvent (Bool × Bool)))
      v13BoolPairRepeatedStep.successEvent := by
  exact prefixHalfStep_v13BoolPairRepeatedStep_empty

theorem unit_field_first_step_certificate_regression :
    V13FieldPrefixInstantiation v13BoolPairUnitField
      ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep := by
  exact v13FieldPrefixInstantiation_unitField_empty

theorem unit_field_first_step_failure_matching_regression :
    V13FieldFailureMatching v13BoolPairUnitField
      ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep := by
  exact
    v13FieldPrefixInstantiation_iff_failureMatching.mp
      v13FieldPrefixInstantiation_unitField_empty

theorem first_coordinate_field_prefix_true_count_regression :
    v13ConcretePrefixCount (Ω := Bool × Bool)
      ([] : List (FiniteEvent (Bool × Bool)))
      v13BoolPairFirstCoordinateField.cellOf true = 2 := by
  exact v13BoolPairFirstCoordinateField_prefix_true_count

theorem first_coordinate_field_success_true_count_regression :
    v13ConcreteSuccessCount (Ω := Bool × Bool)
      ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep
      v13BoolPairFirstCoordinateField.cellOf true = 2 := by
  exact v13BoolPairFirstCoordinateField_success_true_count

theorem first_coordinate_field_failure_true_count_regression :
    v13ConcreteFailureCount (Ω := Bool × Bool)
      ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep
      v13BoolPairFirstCoordinateField.cellOf true = 0 := by
  decide

theorem first_coordinate_field_determines_success_regression :
    V13HistoryFieldDeterminesSuccess v13BoolPairFirstCoordinateField
      v13BoolPairRepeatedStep := by
  exact v13BoolPairFirstCoordinateField_determinesSuccess

theorem second_coordinate_field_not_globally_determines_success_regression :
    ¬ V13HistoryFieldDeterminesSuccess v13BoolPairSecondCoordinateField
      v13BoolPairRepeatedStep := by
  exact not_v13BoolPairSecondCoordinateField_determinesSuccess

theorem second_coordinate_field_determines_success_on_diagonal_regression :
    V13HistoryFieldDeterminesSuccessOn v13BoolPairSecondCoordinateField
      [v13BoolPairDiagonalEvent] v13BoolPairRepeatedStep := by
  exact v13BoolPairSecondCoordinateField_determinesSuccessOn_diagonal

theorem diagonal_repeated_step_success_count_regression :
    finiteHistoryCount (Bool × Bool)
      ([v13BoolPairDiagonalEvent] ++ [v13BoolPairRepeatedStep.successEvent]) = 1 := by
  exact v13BoolPairDiagonal_repeatedStep_success_count

theorem second_coordinate_diagonal_true_cell_has_no_failure_regression :
    ∀ ⦃ω' : Bool × Bool⦄,
      allEvents [v13BoolPairDiagonalEvent] ω' →
        v13BoolPairSecondCoordinateField.cellOf ω' =
          v13BoolPairSecondCoordinateField.cellOf (true, true) →
            v13BoolPairRepeatedStep.successEvent.pred ω' := by
  intro ω' hhist hcell
  cases ω' with
  | mk a b =>
      cases a <;> cases b <;>
        simp [allEvents, v13BoolPairDiagonalEvent,
          v13BoolPairSecondCoordinateField, v13BoolPairRepeatedStep,
          V13SwitchedStep.successEvent] at hhist hcell ⊢

theorem no_fixed_first_coordinate_field_certificate_regression :
    ¬ V13FieldPrefixInstantiation v13BoolPairFirstCoordinateField
      ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep := by
  exact not_v13FieldPrefixInstantiation_firstCoordinateField_empty

theorem no_fixed_first_coordinate_field_certificate_by_determined_success_regression :
    ¬ V13FieldPrefixInstantiation v13BoolPairFirstCoordinateField
      ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep := by
  exact
    not_v13FieldPrefixInstantiation_firstCoordinateField_empty_by_determined_success

theorem no_second_coordinate_field_certificate_on_diagonal_regression :
    ¬ V13FieldPrefixInstantiation v13BoolPairSecondCoordinateField
      [v13BoolPairDiagonalEvent] v13BoolPairRepeatedStep := by
  exact
    not_v13FieldPrefixInstantiation_secondCoordinateField_diagonal_by_determines_success_on

theorem no_second_coordinate_field_certificate_on_diagonal_by_pointwise_regression :
    ¬ V13FieldPrefixInstantiation v13BoolPairSecondCoordinateField
      [v13BoolPairDiagonalEvent] v13BoolPairRepeatedStep := by
  exact
    not_v13FieldPrefixInstantiation_of_success_without_sameCell_failure
      (field := v13BoolPairSecondCoordinateField)
      (hist := [v13BoolPairDiagonalEvent])
      (step := v13BoolPairRepeatedStep)
      (ω := (true, true))
      (by
        simp [allEvents, v13BoolPairDiagonalEvent])
      (by
        decide)
      second_coordinate_diagonal_true_cell_has_no_failure_regression

theorem no_second_coordinate_failure_matching_on_diagonal_regression :
    ¬ V13FieldFailureMatching v13BoolPairSecondCoordinateField
      [v13BoolPairDiagonalEvent] v13BoolPairRepeatedStep := by
  exact
    not_v13FieldFailureMatching_secondCoordinateField_diagonal_by_determines_success_on

theorem no_second_coordinate_failure_matching_on_diagonal_by_pointwise_regression :
    ¬ V13FieldFailureMatching v13BoolPairSecondCoordinateField
      [v13BoolPairDiagonalEvent] v13BoolPairRepeatedStep := by
  exact
    not_v13FieldFailureMatching_of_success_without_sameCell_failure
      (field := v13BoolPairSecondCoordinateField)
      (hist := [v13BoolPairDiagonalEvent])
      (step := v13BoolPairRepeatedStep)
      (ω := (true, true))
      (by
        simp [allEvents, v13BoolPairDiagonalEvent])
      (by
        decide)
      second_coordinate_diagonal_true_cell_has_no_failure_regression

theorem no_first_coordinate_field_failure_matching_regression :
    ¬ V13FieldFailureMatching v13BoolPairFirstCoordinateField
      ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep := by
  intro hmatch
  exact not_v13FieldPrefixInstantiation_firstCoordinateField_empty
    (v13FieldPrefixInstantiation_of_failureMatching hmatch)

theorem prefix_half_without_fixed_first_coordinate_certificate_regression :
    PrefixHalfStep ([] : List (FiniteEvent (Bool × Bool)))
        v13BoolPairRepeatedStep.successEvent ∧
      ¬ V13FieldPrefixInstantiation v13BoolPairFirstCoordinateField
        ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep := by
  exact prefixHalfStep_without_firstCoordinateFieldInstantiation

theorem no_field_instantiation_for_first_coordinate_one_step_regression :
    ¬ V13FieldSwitchingInstantiated
      [v13BoolPairFirstCoordinateFieldedStep] := by
  exact not_v13FieldSwitchingInstantiated_firstCoordinateOneStep

theorem unit_field_then_first_coordinate_field_second_blocked_regression :
    V13FieldPrefixInstantiation v13BoolPairUnitField
        ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep ∧
      ¬ V13FieldSwitchingInstantiated
        [v13BoolPairUnitFieldedStep, v13BoolPairFirstCoordinateFieldedStep] := by
  exact unitField_first_step_then_firstCoordinateField_second_blocked

theorem no_failure_matching_for_unit_then_first_coordinate_regression :
    ¬ V13FieldSwitchingFailureMatching
      [v13BoolPairUnitFieldedStep, v13BoolPairFirstCoordinateFieldedStep] := by
  intro hmatch
  exact unitField_first_step_then_firstCoordinateField_second_blocked.2
    (v13FieldSwitchingInstantiated_iff_failureMatching.mpr hmatch)

theorem no_failure_matching_for_unit_then_first_coordinate_by_determined_success_regression :
    ¬ V13FieldSwitchingFailureMatching
      [v13BoolPairUnitFieldedStep, v13BoolPairFirstCoordinateFieldedStep] := by
  exact
    not_v13FieldSwitchingFailureMatchingFrom_append_cons_of_fieldDeterminesSuccess_positive_success
      (hist := ([] : List (FiniteEvent (Bool × Bool))))
      (pre := [v13BoolPairUnitFieldedStep])
      (item := v13BoolPairFirstCoordinateFieldedStep)
      (suffix := [])
      v13BoolPairFirstCoordinateField_determinesSuccess
      (by
        decide)

theorem no_success_revealing_field_certificate_bool_pair_regression :
    ¬ V13FieldPrefixInstantiation
      (v13SuccessHistoryField v13BoolPairRepeatedStep)
      ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep := by
  exact
    not_v13FieldPrefixInstantiation_successHistoryField_of_positive_success
      (by
        decide)

theorem no_success_revealing_fielded_step_bool_pair_regression :
    ¬ V13FieldSwitchingInstantiated
      [v13SuccessFieldedStep v13BoolPairRepeatedStep] := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_successField_cons_of_positive_success
      (by
        decide)

theorem repeated_step_second_prefix_count_regression :
    finiteHistoryCount (Bool × Bool) [v13BoolPairRepeatedStep.successEvent] = 2 := by
  exact v13BoolPairRepeatedStep_success_count

theorem repeated_step_second_prefix_fails_regression :
    ¬ PrefixHalfStep [v13BoolPairRepeatedStep.successEvent]
      v13BoolPairRepeatedStep.successEvent := by
  exact not_prefixHalfStep_v13BoolPairRepeatedStep_after_success

theorem no_v13_certificate_for_repeated_second_step_regression :
    ¬ V13PrefixInstantiated [v13BoolPairRepeatedStep.successEvent]
      v13BoolPairRepeatedStep := by
  exact not_v13PrefixInstantiated_boolPairRepeatedStep_second

theorem repeated_two_steps_product_bound_violation_regression :
    ¬ 2 ^ [v13BoolPairRepeatedStep, v13BoolPairRepeatedStep].length *
        finiteHistoryCount (Bool × Bool)
          (v13SuccessEvents
            [v13BoolPairRepeatedStep, v13BoolPairRepeatedStep]) ≤
      finiteHistoryCount (Bool × Bool) ([] : List (FiniteEvent (Bool × Bool))) := by
  exact v13BoolPairRepeatedTwoSteps_product_bound_violation

theorem unit_field_repeated_two_steps_product_bound_violation_regression :
    ¬ 2 ^ [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep].length *
        finiteHistoryCount (Bool × Bool)
          (v13FieldedSuccessEvents
            [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep]) ≤
      finiteHistoryCount (Bool × Bool) ([] : List (FiniteEvent (Bool × Bool))) := by
  exact v13BoolPairUnitFieldedRepeatedTwoSteps_product_bound_violation

theorem no_v13_instantiation_for_repeated_two_steps_regression :
    ¬ V13SwitchingInstantiated
      [v13BoolPairRepeatedStep, v13BoolPairRepeatedStep] := by
  exact not_v13SwitchingInstantiated_boolPairRepeatedTwoSteps

theorem no_v13_instantiation_for_repeated_two_steps_by_product_bound_regression :
    ¬ V13SwitchingInstantiated
      [v13BoolPairRepeatedStep, v13BoolPairRepeatedStep] := by
  exact not_v13SwitchingInstantiated_boolPairRepeatedTwoSteps_by_product_bound

theorem unit_field_repeated_success_cell_has_no_failure_regression :
    ∀ ⦃ω' : Bool × Bool⦄,
      allEvents [v13BoolPairRepeatedStep.successEvent] ω' →
        v13BoolPairUnitField.cellOf ω' =
          v13BoolPairUnitField.cellOf (true, true) →
            v13BoolPairRepeatedStep.successEvent.pred ω' := by
  exact v13BoolPairUnitField_repeatedSuccess_cell_has_no_failure

theorem unit_field_repeated_success_success_count_regression :
    v13ConcreteSuccessCount (Ω := Bool × Bool)
      [v13BoolPairRepeatedStep.successEvent] v13BoolPairRepeatedStep
      v13BoolPairUnitField.cellOf PUnit.unit = 2 := by
  exact v13BoolPairUnitField_repeatedSuccess_success_count

theorem unit_field_repeated_success_failure_count_regression :
    v13ConcreteFailureCount (Ω := Bool × Bool)
      [v13BoolPairRepeatedStep.successEvent] v13BoolPairRepeatedStep
      v13BoolPairUnitField.cellOf PUnit.unit = 0 := by
  exact v13BoolPairUnitField_repeatedSuccess_failure_count

theorem unit_field_repeated_success_bad_cell_regression :
    v13ConcreteFailureCount (Ω := Bool × Bool)
        [v13BoolPairRepeatedStep.successEvent] v13BoolPairRepeatedStep
        v13BoolPairUnitField.cellOf PUnit.unit <
      v13ConcreteSuccessCount (Ω := Bool × Bool)
        [v13BoolPairRepeatedStep.successEvent] v13BoolPairRepeatedStep
        v13BoolPairUnitField.cellOf PUnit.unit := by
  exact v13BoolPairUnitField_repeatedSuccess_bad_cell

theorem no_unit_field_failure_matching_after_repeated_success_regression :
    ¬ V13FieldFailureMatching v13BoolPairUnitField
      [v13BoolPairRepeatedStep.successEvent] v13BoolPairRepeatedStep := by
  exact not_v13FieldFailureMatching_unitField_after_repeatedSuccess

theorem no_unit_field_prefix_certificate_after_repeated_success_regression :
    ¬ V13FieldPrefixInstantiation v13BoolPairUnitField
      [v13BoolPairRepeatedStep.successEvent] v13BoolPairRepeatedStep := by
  exact not_v13FieldPrefixInstantiation_unitField_after_repeatedSuccess

theorem unit_field_repeated_two_steps_second_step_blocked_regression :
    V13FieldPrefixInstantiation v13BoolPairUnitField
        ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep ∧
      ¬ V13FieldSwitchingInstantiated
        [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep] := by
  exact unitField_repeatedTwoSteps_second_step_blocked

theorem unit_field_repeated_two_steps_second_step_bad_cell_regression :
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
  exact v13BoolPairUnitFieldedRepeatedTwoSteps_second_step_bad_cell

theorem bad_cell_position_for_unit_field_repeated_two_steps_regression :
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
  exact
    v13BoolPairUnitFieldedRepeatedTwoSteps_product_failure_bad_cell_position

theorem no_concrete_v13_instantiation_for_repeated_two_steps_by_product_bound_regression :
    ¬ V13ConcreteSwitchingInstantiated
      [v13BoolPairRepeatedStep, v13BoolPairRepeatedStep] := by
  exact
    not_v13ConcreteSwitchingInstantiated_boolPairRepeatedTwoSteps_by_product_bound

theorem no_field_instantiation_for_unit_field_repeated_two_steps_by_product_bound_regression :
    ¬ V13FieldSwitchingInstantiated
      [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep] := by
  exact
    not_v13FieldSwitchingInstantiated_unitField_repeatedTwoSteps_by_product_bound

theorem no_failure_matching_for_unit_field_repeated_two_steps_by_product_bound_regression :
    ¬ V13FieldSwitchingFailureMatching
      [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep] := by
  exact
    not_v13FieldSwitchingFailureMatching_unitField_repeatedTwoSteps_by_product_bound

theorem failed_matching_position_for_unit_field_repeated_two_steps_regression :
    ∃ pre item suffix,
      [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep] =
        pre ++ item :: suffix ∧
        ¬ V13FieldFailureMatching item.field
          (([] : List (FiniteEvent (Bool × Bool))) ++
            v13FieldedSuccessEvents pre) item.step := by
  exact
    exists_failed_fieldFailureMatching_at_append_cons_of_product_bound_violation
      v13BoolPairUnitFieldedRepeatedTwoSteps_product_bound_violation

theorem failed_prefix_position_for_unit_field_repeated_two_steps_regression :
    ∃ pre item suffix,
      [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep] =
        pre ++ item :: suffix ∧
        ¬ V13FieldPrefixInstantiation item.field
          (([] : List (FiniteEvent (Bool × Bool))) ++
            v13FieldedSuccessEvents pre) item.step := by
  exact
    exists_failed_fieldPrefixInstantiation_at_append_cons_of_product_bound_violation
      v13BoolPairUnitFieldedRepeatedTwoSteps_product_bound_violation

end Mettapedia.Computability.PNP.PNPv13SwitchingInstantiationRegression
