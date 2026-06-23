import Mettapedia.Computability.PNP.PNPv13SwitchingInstantiationRegressionPrefixConcrete

/-!
# Regression checks for the PNP v13 switching instantiation interface

This module contains the field-prefix and failure-matching regression checks.
-/

namespace Mettapedia.Computability.PNP.PNPv13SwitchingInstantiationRegression

open Mettapedia.Computability.PNP

universe u

def concrete_prefix_certificate_from_field_certificate_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cert : V13FieldPrefixInstantiation field hist step) :
    V13ConcretePrefixInstantiation hist step := by
  exact v13ConcretePrefixInstantiation_of_fieldPrefixInstantiation cert

theorem prefix_half_step_from_field_certificate_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cert : V13FieldPrefixInstantiation field hist step) :
    PrefixHalfStep hist step.successEvent := by
  exact prefixHalfStep_of_v13FieldPrefixInstantiation cert

def field_prefix_certificate_from_cell_half_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hhalf : ∀ cell,
      2 * v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell ≤
        v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell) :
    V13FieldPrefixInstantiation field hist step := by
  exact v13FieldPrefixInstantiation_of_cellHalf hhalf

theorem field_prefix_certificate_iff_cell_half_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω} :
    V13FieldPrefixInstantiation field hist step ↔
      ∀ cell,
        2 * v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell ≤
          v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell := by
  exact v13FieldPrefixInstantiation_iff_cellHalf

theorem field_prefix_certificate_iff_success_le_failure_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω} :
    V13FieldPrefixInstantiation field hist step ↔
      ∀ cell,
        v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell ≤
          v13ConcreteFailureCount (Ω := Ω) hist step field.cellOf cell := by
  exact v13FieldPrefixInstantiation_iff_success_le_failure

theorem field_failure_matching_iff_success_le_failure_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω} :
    V13FieldFailureMatching field hist step ↔
      ∀ cell,
        v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell ≤
          v13ConcreteFailureCount (Ω := Ω) hist step field.cellOf cell := by
  exact v13FieldFailureMatching_iff_success_le_failure

theorem bad_cell_from_failed_field_failure_matching_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hfail : ¬ V13FieldFailureMatching field hist step) :
    ∃ cell : field.Cell,
      v13ConcreteFailureCount (Ω := Ω) hist step field.cellOf cell <
        v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell := by
  exact exists_bad_cell_of_not_v13FieldFailureMatching hfail

theorem field_prefix_certificate_iff_failure_matching_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω} :
    V13FieldPrefixInstantiation field hist step ↔
      V13FieldFailureMatching field hist step := by
  exact v13FieldPrefixInstantiation_iff_failureMatching

def field_prefix_certificate_from_failure_matching_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hmatch : V13FieldFailureMatching field hist step) :
    V13FieldPrefixInstantiation field hist step :=
  v13FieldPrefixInstantiation_of_failureMatching hmatch

theorem same_cell_failure_from_failure_matching_success_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hmatch : V13FieldFailureMatching field hist step)
    {ω : Ω}
    (hhist : allEvents hist ω)
    (hsucc : step.successEvent.pred ω) :
    ∃ ω' : Ω,
      allEvents hist ω' ∧
        field.cellOf ω' = field.cellOf ω ∧
          ¬ step.successEvent.pred ω' := by
  exact
    exists_sameCell_failure_of_fieldFailureMatching_success
      hmatch hhist hsucc

theorem no_failure_matching_from_success_without_same_cell_failure_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    {ω : Ω}
    (hhist : allEvents hist ω)
    (hsucc : step.successEvent.pred ω)
    (hnoFailure :
      ∀ ⦃ω' : Ω⦄,
        allEvents hist ω' →
          field.cellOf ω' = field.cellOf ω →
            step.successEvent.pred ω') :
    ¬ V13FieldFailureMatching field hist step := by
  exact
    not_v13FieldFailureMatching_of_success_without_sameCell_failure
      hhist hsucc hnoFailure

theorem same_cell_failure_from_field_certificate_success_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cert : V13FieldPrefixInstantiation field hist step)
    {ω : Ω}
    (hhist : allEvents hist ω)
    (hsucc : step.successEvent.pred ω) :
    ∃ ω' : Ω,
      allEvents hist ω' ∧
        field.cellOf ω' = field.cellOf ω ∧
          ¬ step.successEvent.pred ω' := by
  exact
    exists_sameCell_failure_of_fieldPrefixInstantiation_success
      cert hhist hsucc

theorem no_field_prefix_certificate_from_no_failure_matching_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hfail : ¬ V13FieldFailureMatching field hist step) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact not_v13FieldPrefixInstantiation_of_not_failureMatching hfail

theorem bad_cell_from_failed_field_prefix_certificate_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hfail : ¬ V13FieldPrefixInstantiation field hist step) :
    ∃ cell : field.Cell,
      v13ConcreteFailureCount (Ω := Ω) hist step field.cellOf cell <
        v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell := by
  exact exists_bad_cell_of_not_v13FieldPrefixInstantiation hfail

theorem no_field_prefix_certificate_from_success_without_same_cell_failure_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    {ω : Ω}
    (hhist : allEvents hist ω)
    (hsucc : step.successEvent.pred ω)
    (hnoFailure :
      ∀ ⦃ω' : Ω⦄,
        allEvents hist ω' →
          field.cellOf ω' = field.cellOf ω →
            step.successEvent.pred ω') :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact
    not_v13FieldPrefixInstantiation_of_success_without_sameCell_failure
      hhist hsucc hnoFailure

theorem no_failure_matching_from_determined_success_positive_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccess field step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13FieldFailureMatching field hist step := by
  exact
    not_v13FieldFailureMatching_of_fieldDeterminesSuccess_positive_success
      hdet hpos

theorem failure_matching_blocks_determined_success_positive_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hmatch : V13FieldFailureMatching field hist step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13HistoryFieldDeterminesSuccess field step := by
  exact
    not_v13HistoryFieldDeterminesSuccess_of_failureMatching_positive_success
      hmatch hpos

theorem field_determines_success_on_from_global_regression
    {Ω : Type u}
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccess field step) :
    V13HistoryFieldDeterminesSuccessOn field hist step := by
  exact v13HistoryFieldDeterminesSuccessOn_of_determinesSuccess hdet

theorem no_failure_matching_from_determined_success_on_positive_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccessOn field hist step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13FieldFailureMatching field hist step := by
  exact
    not_v13FieldFailureMatching_of_fieldDeterminesSuccessOn_positive_success
      hdet hpos

theorem failure_matching_blocks_determined_success_on_positive_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hmatch : V13FieldFailureMatching field hist step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13HistoryFieldDeterminesSuccessOn field hist step := by
  exact
    not_v13HistoryFieldDeterminesSuccessOn_of_failureMatching_positive_success
      hmatch hpos

theorem no_field_prefix_certificate_from_success_gt_failure_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cell : field.Cell)
    (hbad :
      v13ConcreteFailureCount (Ω := Ω) hist step field.cellOf cell <
        v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact not_v13FieldPrefixInstantiation_of_success_gt_failure cell hbad

theorem field_determines_success_failure_count_zero_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccess field step)
    (cell : field.Cell)
    (hpos : 0 < v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell) :
    v13ConcreteFailureCount (Ω := Ω) hist step field.cellOf cell = 0 := by
  exact
    v13ConcreteFailureCount_eq_zero_of_fieldDeterminesSuccess_of_success_pos
      hdet cell hpos

theorem field_determines_success_on_failure_count_zero_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccessOn field hist step)
    (cell : field.Cell)
    (hpos : 0 < v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell) :
    v13ConcreteFailureCount (Ω := Ω) hist step field.cellOf cell = 0 := by
  exact
    v13ConcreteFailureCount_eq_zero_of_fieldDeterminesSuccessOn_of_success_pos
      hdet cell hpos

theorem no_field_prefix_certificate_from_determined_success_cell_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccess field step)
    (cell : field.Cell)
    (hpos : 0 < v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact
    not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccess_cell_success
      hdet cell hpos

theorem no_field_prefix_certificate_from_determined_success_on_cell_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccessOn field hist step)
    (cell : field.Cell)
    (hpos : 0 < v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact
    not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccessOn_cell_success
      hdet cell hpos

theorem no_field_prefix_certificate_from_determined_success_positive_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccess field step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact
    not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccess_positive_success
      hdet hpos

theorem no_field_prefix_certificate_from_determined_success_on_positive_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccessOn field hist step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact
    not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccessOn_positive_success
      hdet hpos

theorem no_field_prefix_certificate_from_bad_cell_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cell : field.Cell)
    (hbad :
      ¬ 2 * v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell ≤
        v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact not_v13FieldPrefixInstantiation_of_cell_half_violation cell hbad

end Mettapedia.Computability.PNP.PNPv13SwitchingInstantiationRegression
