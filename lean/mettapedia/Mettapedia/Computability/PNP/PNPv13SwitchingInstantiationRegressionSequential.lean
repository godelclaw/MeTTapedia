import Mettapedia.Computability.PNP.PNPv13SwitchingInstantiationRegressionAfterPrefix

/-!
# Regression checks for the PNP v13 switching instantiation interface

This module contains the v13 sequential and concrete switching regression checks.
-/

namespace Mettapedia.Computability.PNP.PNPv13SwitchingInstantiationRegression

open Mettapedia.Computability.PNP

universe u

theorem sequential_half_from_v13_instantiation_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (h : V13SwitchingInstantiatedFrom hist steps) :
    SequentialHalfAdmissibleFrom hist (v13SuccessEvents steps) := by
  exact sequentialHalfAdmissibleFrom_of_v13SwitchingInstantiatedFrom h

theorem v13_instantiation_from_sequential_half_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (h : SequentialHalfAdmissibleFrom hist (v13SuccessEvents steps)) :
    V13SwitchingInstantiatedFrom hist steps := by
  exact v13SwitchingInstantiatedFrom_of_sequentialHalfAdmissibleFrom h

theorem v13_instantiation_iff_sequential_half_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)} :
    V13SwitchingInstantiatedFrom hist steps ↔
      SequentialHalfAdmissibleFrom hist (v13SuccessEvents steps) := by
  exact v13SwitchingInstantiatedFrom_iff_sequentialHalfAdmissibleFrom

theorem v13_instantiation_empty_iff_sequential_half_regression
    {Ω : Type u} [Fintype Ω] {steps : List (V13SwitchedStep Ω)} :
    V13SwitchingInstantiated steps ↔
      SequentialHalfAdmissible (v13SuccessEvents steps) := by
  exact v13SwitchingInstantiated_iff_sequentialHalfAdmissible

theorem v13_instantiation_from_concrete_instantiation_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (h : V13ConcreteSwitchingInstantiatedFrom hist steps) :
    V13SwitchingInstantiatedFrom hist steps := by
  exact v13SwitchingInstantiatedFrom_of_concreteSwitchingInstantiatedFrom h

theorem concrete_v13_instantiation_from_sequential_half_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (h : SequentialHalfAdmissibleFrom hist (v13SuccessEvents steps)) :
    V13ConcreteSwitchingInstantiatedFrom hist steps := by
  exact v13ConcreteSwitchingInstantiatedFrom_of_sequentialHalfAdmissibleFrom h

theorem concrete_v13_instantiation_iff_sequential_half_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)} :
    V13ConcreteSwitchingInstantiatedFrom hist steps ↔
      SequentialHalfAdmissibleFrom hist (v13SuccessEvents steps) := by
  exact v13ConcreteSwitchingInstantiatedFrom_iff_sequentialHalfAdmissibleFrom

theorem concrete_v13_instantiation_empty_iff_sequential_half_regression
    {Ω : Type u} [Fintype Ω] {steps : List (V13SwitchedStep Ω)} :
    V13ConcreteSwitchingInstantiated steps ↔
      SequentialHalfAdmissible (v13SuccessEvents steps) := by
  exact v13ConcreteSwitchingInstantiated_iff_sequentialHalfAdmissible

theorem no_v13_instantiation_for_repeated_step_positive_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13SwitchingInstantiatedFrom hist [step, step] := by
  exact not_v13SwitchingInstantiatedFrom_repeated_step_of_positive hpos

theorem no_v13_instantiation_for_repeated_step_empty_positive_regression
    {Ω : Type u} [Fintype Ω] {step : V13SwitchedStep Ω}
    (hpos : 0 < finiteHistoryCount Ω [step.successEvent]) :
    ¬ V13SwitchingInstantiated [step, step] := by
  exact not_v13SwitchingInstantiated_repeated_step_of_positive hpos

theorem no_concrete_v13_instantiation_for_repeated_step_positive_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13ConcreteSwitchingInstantiatedFrom hist [step, step] := by
  exact not_v13ConcreteSwitchingInstantiatedFrom_repeated_step_of_positive hpos

theorem no_concrete_v13_instantiation_for_repeated_step_empty_positive_regression
    {Ω : Type u} [Fintype Ω] {step : V13SwitchedStep Ω}
    (hpos : 0 < finiteHistoryCount Ω [step.successEvent]) :
    ¬ V13ConcreteSwitchingInstantiated [step, step] := by
  exact not_v13ConcreteSwitchingInstantiated_repeated_step_of_positive hpos

theorem product_bound_from_v13_instantiation_regression
    {Ω : Type u} [Fintype Ω]
    (steps : List (V13SwitchedStep Ω))
    (h : V13SwitchingInstantiated steps) :
    2 ^ steps.length * finiteHistoryCount Ω (v13SuccessEvents steps) ≤
      finiteHistoryCount Ω ([] : List (FiniteEvent Ω)) := by
  exact v13_product_bound_of_instantiated steps h

theorem product_bound_from_concrete_v13_instantiation_regression
    {Ω : Type u} [Fintype Ω]
    (steps : List (V13SwitchedStep Ω))
    (h : V13ConcreteSwitchingInstantiated steps) :
    2 ^ steps.length * finiteHistoryCount Ω (v13SuccessEvents steps) ≤
      finiteHistoryCount Ω ([] : List (FiniteEvent Ω)) := by
  exact v13_product_bound_of_concreteInstantiated steps h

theorem product_bound_violation_blocks_v13_instantiation_regression
    {Ω : Type u} [Fintype Ω]
    {steps : List (V13SwitchedStep Ω)}
    (hbad :
      ¬ 2 ^ steps.length * finiteHistoryCount Ω (v13SuccessEvents steps) ≤
        finiteHistoryCount Ω ([] : List (FiniteEvent Ω))) :
    ¬ V13SwitchingInstantiated steps := by
  exact not_v13SwitchingInstantiated_of_product_bound_violation hbad

theorem product_bound_violation_blocks_concrete_v13_instantiation_regression
    {Ω : Type u} [Fintype Ω]
    {steps : List (V13SwitchedStep Ω)}
    (hbad :
      ¬ 2 ^ steps.length * finiteHistoryCount Ω (v13SuccessEvents steps) ≤
        finiteHistoryCount Ω ([] : List (FiniteEvent Ω))) :
    ¬ V13ConcreteSwitchingInstantiated steps := by
  exact not_v13ConcreteSwitchingInstantiated_of_product_bound_violation hbad

theorem failed_v13_prefix_position_from_not_instantiated_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (hfail : ¬ V13SwitchingInstantiatedFrom hist steps) :
    ∃ pre step suffix,
      steps = pre ++ step :: suffix ∧
        ¬ PrefixHalfStep (hist ++ v13SuccessEvents pre) step.successEvent := by
  exact
    exists_failed_prefixHalfStep_at_append_cons_of_not_v13SwitchingInstantiatedFrom
      hfail

theorem failed_v13_prefix_position_from_product_bound_violation_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (hbad :
      ¬ 2 ^ steps.length *
          finiteHistoryCount Ω (hist ++ v13SuccessEvents steps) ≤
        finiteHistoryCount Ω hist) :
    ∃ pre step suffix,
      steps = pre ++ step :: suffix ∧
        ¬ PrefixHalfStep (hist ++ v13SuccessEvents pre) step.successEvent := by
  exact
    exists_failed_prefixHalfStep_at_append_cons_of_v13_product_bound_violation
      hbad

theorem failed_v13_prefix_position_from_empty_product_bound_violation_regression
    {Ω : Type u} [Fintype Ω]
    {steps : List (V13SwitchedStep Ω)}
    (hbad :
      ¬ 2 ^ steps.length * finiteHistoryCount Ω (v13SuccessEvents steps) ≤
        finiteHistoryCount Ω ([] : List (FiniteEvent Ω))) :
    ∃ pre step suffix,
      steps = pre ++ step :: suffix ∧
        ¬ PrefixHalfStep (v13SuccessEvents pre) step.successEvent := by
  exact
    exists_failed_prefixHalfStep_at_append_cons_of_v13_empty_product_bound_violation
      hbad

theorem failed_prefix_blocks_v13_instantiation_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} {rest : List (V13SwitchedStep Ω)}
    (hfail : ¬ PrefixHalfStep hist step.successEvent) :
    ¬ V13SwitchingInstantiatedFrom hist (step :: rest) := by
  exact not_v13SwitchingInstantiatedFrom_cons_of_not_prefixHalfStep hfail

end Mettapedia.Computability.PNP.PNPv13SwitchingInstantiationRegression
