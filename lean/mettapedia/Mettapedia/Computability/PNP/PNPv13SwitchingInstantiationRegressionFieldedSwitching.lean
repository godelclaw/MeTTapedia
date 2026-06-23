import Mettapedia.Computability.PNP.PNPv13SwitchingInstantiationRegressionFieldPrefix

/-!
# Regression checks for the PNP v13 switching instantiation interface

This module contains the fielded switching and product-bound regression checks.
-/

namespace Mettapedia.Computability.PNP.PNPv13SwitchingInstantiationRegression

open Mettapedia.Computability.PNP

universe u

theorem success_history_field_determines_success_regression
    {Ω : Type u} (step : V13SwitchedStep Ω) :
    V13HistoryFieldDeterminesSuccess (v13SuccessHistoryField step) step := by
  exact v13SuccessHistoryField_determinesSuccess step

theorem success_history_field_true_cell_count_regression
    {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω) :
    v13ConcretePrefixCount (Ω := Ω) hist
        (v13SuccessHistoryField step).cellOf (ULift.up true) =
      finiteHistoryCount Ω (hist ++ [step.successEvent]) := by
  exact v13SuccessHistoryField_prefix_true_count hist step

theorem field_certificate_success_cell_is_mixed_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cert : V13FieldPrefixInstantiation field hist step)
    (cell : field.Cell)
    (hpos :
      0 < v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell) :
    v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell <
      v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell := by
  exact
    v13FieldPrefixInstantiation_successCount_lt_prefixCount_of_success_pos
      cert cell hpos

theorem field_certificate_one_success_requires_two_prefix_points_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cert : V13FieldPrefixInstantiation field hist step)
    (cell : field.Cell)
    (hsucc :
      v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell = 1) :
    2 ≤ v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell := by
  exact
    v13FieldPrefixInstantiation_two_le_prefixCount_of_successCount_eq_one
      cert cell hsucc

theorem no_field_prefix_certificate_from_total_success_cell_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cell : field.Cell)
    (hpos :
      0 < v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell)
    (hall :
      v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell =
        v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact not_v13FieldPrefixInstantiation_of_cell_success_eq_prefix cell hpos hall

theorem no_field_prefix_certificate_from_positive_total_success_cell_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cell : field.Cell)
    (hpos :
      0 < v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell)
    (hall :
      v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell =
        v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact
    not_v13FieldPrefixInstantiation_of_positive_success_eq_prefix
      cell hpos hall

theorem no_field_prefix_certificate_from_singleton_success_cell_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cell : field.Cell)
    (hprefix :
      v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell = 1)
    (hsuccess :
      v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell = 1) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact
    not_v13FieldPrefixInstantiation_of_singleton_success_cell
      cell hprefix hsuccess

theorem no_success_history_field_certificate_from_positive_success_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13FieldPrefixInstantiation (v13SuccessHistoryField step) hist step := by
  exact
    not_v13FieldPrefixInstantiation_successHistoryField_of_positive_success hpos

theorem sequential_half_from_field_instantiation_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (h : V13FieldSwitchingInstantiatedFrom hist items) :
    SequentialHalfAdmissibleFrom hist (v13FieldedSuccessEvents items) := by
  exact sequentialHalfAdmissibleFrom_of_v13FieldSwitchingInstantiatedFrom h

theorem no_field_instantiation_for_repeated_item_positive_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {item : V13FieldedStep Ω}
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [item.step.successEvent])) :
    ¬ V13FieldSwitchingInstantiatedFrom hist [item, item] := by
  exact not_v13FieldSwitchingInstantiatedFrom_repeated_item_of_positive hpos

theorem no_field_instantiation_for_repeated_item_empty_positive_regression
    {Ω : Type u} [Fintype Ω] {item : V13FieldedStep Ω}
    (hpos : 0 < finiteHistoryCount Ω [item.step.successEvent]) :
    ¬ V13FieldSwitchingInstantiated [item, item] := by
  exact not_v13FieldSwitchingInstantiated_repeated_item_of_positive hpos

theorem no_failure_matching_for_repeated_item_positive_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {item : V13FieldedStep Ω}
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [item.step.successEvent])) :
    ¬ V13FieldSwitchingFailureMatchingFrom hist [item, item] := by
  exact not_v13FieldSwitchingFailureMatchingFrom_repeated_item_of_positive hpos

theorem no_failure_matching_for_repeated_item_empty_positive_regression
    {Ω : Type u} [Fintype Ω] {item : V13FieldedStep Ω}
    (hpos : 0 < finiteHistoryCount Ω [item.step.successEvent]) :
    ¬ V13FieldSwitchingFailureMatching [item, item] := by
  exact not_v13FieldSwitchingFailureMatching_repeated_item_of_positive hpos

theorem product_bound_from_field_instantiation_regression
    {Ω : Type u} [Fintype Ω]
    (items : List (V13FieldedStep Ω))
    (h : V13FieldSwitchingInstantiated items) :
    2 ^ items.length * finiteHistoryCount Ω (v13FieldedSuccessEvents items) ≤
      finiteHistoryCount Ω ([] : List (FiniteEvent Ω)) := by
  exact v13_product_bound_of_fieldInstantiated items h

theorem field_instantiation_iff_cell_half_from_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    V13FieldSwitchingInstantiatedFrom hist items ↔
      V13FieldSwitchingCellHalfFrom hist items := by
  exact v13FieldSwitchingInstantiatedFrom_iff_cellHalfFrom

theorem field_instantiation_empty_iff_cell_half_regression
    {Ω : Type u} [Fintype Ω] {items : List (V13FieldedStep Ω)} :
    V13FieldSwitchingInstantiated items ↔
      V13FieldSwitchingCellHalf items := by
  exact v13FieldSwitchingInstantiated_iff_cellHalf

theorem field_instantiation_iff_failure_matching_from_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    V13FieldSwitchingInstantiatedFrom hist items ↔
      V13FieldSwitchingFailureMatchingFrom hist items := by
  exact v13FieldSwitchingInstantiatedFrom_iff_failureMatchingFrom

theorem field_instantiation_empty_iff_failure_matching_regression
    {Ω : Type u} [Fintype Ω] {items : List (V13FieldedStep Ω)} :
    V13FieldSwitchingInstantiated items ↔
      V13FieldSwitchingFailureMatching items := by
  exact v13FieldSwitchingInstantiated_iff_failureMatching

theorem product_bound_from_field_failure_matching_regression
    {Ω : Type u} [Fintype Ω]
    (items : List (V13FieldedStep Ω))
    (h : V13FieldSwitchingFailureMatching items) :
    2 ^ items.length * finiteHistoryCount Ω (v13FieldedSuccessEvents items) ≤
      finiteHistoryCount Ω ([] : List (FiniteEvent Ω)) := by
  exact v13_product_bound_of_fieldFailureMatching items h

theorem product_bound_violation_blocks_field_instantiation_regression
    {Ω : Type u} [Fintype Ω]
    {items : List (V13FieldedStep Ω)}
    (hbad :
      ¬ 2 ^ items.length * finiteHistoryCount Ω (v13FieldedSuccessEvents items) ≤
        finiteHistoryCount Ω ([] : List (FiniteEvent Ω))) :
    ¬ V13FieldSwitchingInstantiated items := by
  exact not_v13FieldSwitchingInstantiated_of_product_bound_violation hbad

theorem product_bound_violation_blocks_field_failure_matching_from_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hbad :
      ¬ 2 ^ items.length *
          finiteHistoryCount Ω (hist ++ v13FieldedSuccessEvents items) ≤
        finiteHistoryCount Ω hist) :
    ¬ V13FieldSwitchingFailureMatchingFrom hist items := by
  exact
    not_v13FieldSwitchingFailureMatchingFrom_of_product_bound_violation hbad

theorem product_bound_violation_blocks_field_failure_matching_regression
    {Ω : Type u} [Fintype Ω]
    {items : List (V13FieldedStep Ω)}
    (hbad :
      ¬ 2 ^ items.length * finiteHistoryCount Ω (v13FieldedSuccessEvents items) ≤
        finiteHistoryCount Ω ([] : List (FiniteEvent Ω))) :
    ¬ V13FieldSwitchingFailureMatching items := by
  exact not_v13FieldSwitchingFailureMatching_of_product_bound_violation hbad

theorem failed_field_failure_matching_position_from_not_matching_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfail : ¬ V13FieldSwitchingFailureMatchingFrom hist items) :
    ∃ pre item suffix,
      items = pre ++ item :: suffix ∧
        ¬ V13FieldFailureMatching item.field
          (hist ++ v13FieldedSuccessEvents pre) item.step := by
  exact
    exists_failed_fieldFailureMatching_at_append_cons_of_not_failureMatchingFrom
      hfail

theorem failed_field_failure_matching_position_from_product_bound_violation_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hbad :
      ¬ 2 ^ items.length *
          finiteHistoryCount Ω (hist ++ v13FieldedSuccessEvents items) ≤
        finiteHistoryCount Ω hist) :
    ∃ pre item suffix,
      items = pre ++ item :: suffix ∧
        ¬ V13FieldFailureMatching item.field
          (hist ++ v13FieldedSuccessEvents pre) item.step := by
  exact
    exists_failed_fieldFailureMatching_at_append_cons_of_product_bound_violation
      hbad

theorem bad_cell_position_from_not_failure_matching_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfail : ¬ V13FieldSwitchingFailureMatchingFrom hist items) :
    ∃ pre item suffix,
      items = pre ++ item :: suffix ∧
        ∃ cell : item.field.Cell,
          v13ConcreteFailureCount (Ω := Ω)
              (hist ++ v13FieldedSuccessEvents pre)
              item.step item.field.cellOf cell <
            v13ConcreteSuccessCount (Ω := Ω)
              (hist ++ v13FieldedSuccessEvents pre)
              item.step item.field.cellOf cell := by
  exact exists_bad_cell_at_append_cons_of_not_failureMatchingFrom hfail

theorem bad_cell_position_from_product_bound_violation_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hbad :
      ¬ 2 ^ items.length *
          finiteHistoryCount Ω (hist ++ v13FieldedSuccessEvents items) ≤
        finiteHistoryCount Ω hist) :
    ∃ pre item suffix,
      items = pre ++ item :: suffix ∧
        ∃ cell : item.field.Cell,
          v13ConcreteFailureCount (Ω := Ω)
              (hist ++ v13FieldedSuccessEvents pre)
              item.step item.field.cellOf cell <
            v13ConcreteSuccessCount (Ω := Ω)
              (hist ++ v13FieldedSuccessEvents pre)
              item.step item.field.cellOf cell := by
  exact exists_bad_cell_at_append_cons_of_product_bound_violation hbad

theorem failed_field_prefix_position_from_product_bound_violation_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hbad :
      ¬ 2 ^ items.length *
          finiteHistoryCount Ω (hist ++ v13FieldedSuccessEvents items) ≤
        finiteHistoryCount Ω hist) :
    ∃ pre item suffix,
      items = pre ++ item :: suffix ∧
        ¬ V13FieldPrefixInstantiation item.field
          (hist ++ v13FieldedSuccessEvents pre) item.step := by
  exact
    exists_failed_fieldPrefixInstantiation_at_append_cons_of_product_bound_violation
      hbad

theorem failed_field_prefix_blocks_field_instantiation_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {item : V13FieldedStep Ω} {rest : List (V13FieldedStep Ω)}
    (hfail : ¬ V13FieldPrefixInstantiation item.field hist item.step) :
    ¬ V13FieldSwitchingInstantiatedFrom hist (item :: rest) := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_cons_of_not_fieldPrefixInstantiation
      hfail

theorem failed_failure_matching_blocks_field_instantiation_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfail : ¬ V13FieldSwitchingFailureMatchingFrom hist items) :
    ¬ V13FieldSwitchingInstantiatedFrom hist items := by
  exact not_v13FieldSwitchingInstantiatedFrom_of_not_failureMatchingFrom hfail

end Mettapedia.Computability.PNP.PNPv13SwitchingInstantiationRegression
