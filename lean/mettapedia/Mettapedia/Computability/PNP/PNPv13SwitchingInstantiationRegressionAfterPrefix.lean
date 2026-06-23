import Mettapedia.Computability.PNP.PNPv13SwitchingInstantiationRegressionFieldedSwitching

/-!
# Regression checks for the PNP v13 switching instantiation interface

This module contains the after-prefix suffix and success-field blocking regression checks.
-/

namespace Mettapedia.Computability.PNP.PNPv13SwitchingInstantiationRegression

open Mettapedia.Computability.PNP

universe u

theorem extract_failure_matching_after_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hmatch :
      V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix)) :
    V13FieldFailureMatching item.field
      (hist ++ v13FieldedSuccessEvents pre) item.step := by
  exact
    v13FieldFailureMatching_at_append_cons_of_failureMatchingFrom hmatch

theorem same_cell_failure_after_prefix_from_matching_success_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hmatch :
      V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix))
    {ω : Ω}
    (hhist : allEvents (hist ++ v13FieldedSuccessEvents pre) ω)
    (hsucc : item.step.successEvent.pred ω) :
    ∃ ω' : Ω,
      allEvents (hist ++ v13FieldedSuccessEvents pre) ω' ∧
        item.field.cellOf ω' = item.field.cellOf ω ∧
          ¬ item.step.successEvent.pred ω' := by
  exact
    exists_sameCell_failure_at_append_cons_of_failureMatchingFrom_success
      hmatch hhist hsucc

theorem success_without_same_cell_failure_blocks_matching_after_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    {ω : Ω}
    (hhist : allEvents (hist ++ v13FieldedSuccessEvents pre) ω)
    (hsucc : item.step.successEvent.pred ω)
    (hnoFailure :
      ∀ ⦃ω' : Ω⦄,
        allEvents (hist ++ v13FieldedSuccessEvents pre) ω' →
          item.field.cellOf ω' = item.field.cellOf ω →
            item.step.successEvent.pred ω') :
    ¬ V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix) := by
  exact
    not_v13FieldSwitchingFailureMatchingFrom_append_cons_of_success_without_sameCell_failure
      hhist hsucc hnoFailure

theorem failure_matching_after_prefix_blocks_determined_success_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hmatch :
      V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix))
    (hpos :
      0 < finiteHistoryCount Ω
        ((hist ++ v13FieldedSuccessEvents pre) ++ [item.step.successEvent])) :
    ¬ V13HistoryFieldDeterminesSuccess item.field item.step := by
  exact
    not_v13HistoryFieldDeterminesSuccess_at_append_cons_of_failureMatchingFrom_positive_success
      hmatch hpos

theorem failure_matching_after_prefix_blocks_determined_success_on_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hmatch :
      V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix))
    (hpos :
      0 < finiteHistoryCount Ω
        ((hist ++ v13FieldedSuccessEvents pre) ++ [item.step.successEvent])) :
    ¬ V13HistoryFieldDeterminesSuccessOn item.field
      (hist ++ v13FieldedSuccessEvents pre) item.step := by
  exact
    not_v13HistoryFieldDeterminesSuccessOn_at_append_cons_of_failureMatchingFrom_positive_success
      hmatch hpos

theorem determined_success_field_blocks_failure_matching_after_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hdet : V13HistoryFieldDeterminesSuccess item.field item.step)
    (hpos :
      0 < finiteHistoryCount Ω
        ((hist ++ v13FieldedSuccessEvents pre) ++ [item.step.successEvent])) :
    ¬ V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix) := by
  exact
    not_v13FieldSwitchingFailureMatchingFrom_append_cons_of_fieldDeterminesSuccess_positive_success
      hdet hpos

theorem determined_success_on_field_blocks_failure_matching_after_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hdet :
      V13HistoryFieldDeterminesSuccessOn item.field
        (hist ++ v13FieldedSuccessEvents pre) item.step)
    (hpos :
      0 < finiteHistoryCount Ω
        ((hist ++ v13FieldedSuccessEvents pre) ++ [item.step.successEvent])) :
    ¬ V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix) := by
  exact
    not_v13FieldSwitchingFailureMatchingFrom_append_cons_of_fieldDeterminesSuccessOn_positive_success
      hdet hpos

theorem determined_success_field_blocks_field_suffix_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {item : V13FieldedStep Ω}
    {rest : List (V13FieldedStep Ω)}
    (hdet : V13HistoryFieldDeterminesSuccess item.field item.step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [item.step.successEvent])) :
    ¬ V13FieldSwitchingInstantiatedFrom hist (item :: rest) := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_cons_of_fieldDeterminesSuccess_positive_success
      hdet hpos

theorem determined_success_on_field_blocks_field_suffix_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {item : V13FieldedStep Ω}
    {rest : List (V13FieldedStep Ω)}
    (hdet : V13HistoryFieldDeterminesSuccessOn item.field hist item.step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [item.step.successEvent])) :
    ¬ V13FieldSwitchingInstantiatedFrom hist (item :: rest) := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_cons_of_fieldDeterminesSuccessOn_positive_success
      hdet hpos

theorem failed_field_prefix_blocks_field_instantiation_after_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hfail :
      ¬ V13FieldPrefixInstantiation item.field
          (hist ++ v13FieldedSuccessEvents pre) item.step) :
    ¬ V13FieldSwitchingInstantiatedFrom hist (pre ++ item :: suffix) := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_append_cons_of_not_fieldPrefixInstantiation
      hfail

theorem success_without_same_cell_failure_blocks_field_instantiation_after_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    {ω : Ω}
    (hhist : allEvents (hist ++ v13FieldedSuccessEvents pre) ω)
    (hsucc : item.step.successEvent.pred ω)
    (hnoFailure :
      ∀ ⦃ω' : Ω⦄,
        allEvents (hist ++ v13FieldedSuccessEvents pre) ω' →
          item.field.cellOf ω' = item.field.cellOf ω →
            item.step.successEvent.pred ω') :
    ¬ V13FieldSwitchingInstantiatedFrom hist (pre ++ item :: suffix) := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_append_cons_of_success_without_sameCell_failure
      hhist hsucc hnoFailure

theorem determined_success_field_blocks_field_instantiation_after_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hdet : V13HistoryFieldDeterminesSuccess item.field item.step)
    (hpos :
      0 < finiteHistoryCount Ω
        ((hist ++ v13FieldedSuccessEvents pre) ++ [item.step.successEvent])) :
    ¬ V13FieldSwitchingInstantiatedFrom hist (pre ++ item :: suffix) := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_append_cons_of_fieldDeterminesSuccess_positive_success
      hdet hpos

theorem determined_success_on_field_blocks_field_instantiation_after_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hdet :
      V13HistoryFieldDeterminesSuccessOn item.field
        (hist ++ v13FieldedSuccessEvents pre) item.step)
    (hpos :
      0 < finiteHistoryCount Ω
        ((hist ++ v13FieldedSuccessEvents pre) ++ [item.step.successEvent])) :
    ¬ V13FieldSwitchingInstantiatedFrom hist (pre ++ item :: suffix) := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_append_cons_of_fieldDeterminesSuccessOn_positive_success
      hdet hpos

theorem success_revealing_field_blocks_field_suffix_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} {rest : List (V13FieldedStep Ω)}
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13FieldSwitchingInstantiatedFrom hist
      (v13SuccessFieldedStep step :: rest) := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_successField_cons_of_positive_success
      hpos

end Mettapedia.Computability.PNP.PNPv13SwitchingInstantiationRegression
