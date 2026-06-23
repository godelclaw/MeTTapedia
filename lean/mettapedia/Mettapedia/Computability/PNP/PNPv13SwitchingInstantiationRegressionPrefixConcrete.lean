import Mettapedia.Computability.PNP.PNPv13SwitchingInstantiationCore
import Mettapedia.Computability.PNP.PNPv13SwitchingInstantiationConcrete
import Mettapedia.Computability.PNP.PNPv13SwitchingHistoryConcretePrefix
import Mettapedia.Computability.PNP.PNPv13SwitchingFieldedSuffixObstructions
import Mettapedia.Computability.PNP.PNPv13SwitchingFailureLocalization
import Mettapedia.Computability.PNP.PNPv13BoolPairProductObstructions

/-!
# Regression checks for the PNP v13 switching instantiation interface

This module contains the prefix and concrete-cell regression checks.
-/

namespace Mettapedia.Computability.PNP.PNPv13SwitchingInstantiationRegression

open Mettapedia.Computability.PNP

universe u

theorem prefix_half_step_from_v13_prefix_certificate_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cert : V13PrefixInstantiation hist step) :
    PrefixHalfStep hist step.successEvent := by
  exact prefixHalfStep_of_v13PrefixInstantiation cert

def v13_prefix_certificate_from_prefix_half_step_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (h : PrefixHalfStep hist step.successEvent) :
    V13PrefixInstantiation hist step := by
  exact v13PrefixInstantiation_of_prefixHalfStep h

theorem v13_prefix_instantiated_iff_prefix_half_step_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω} :
    V13PrefixInstantiated hist step ↔
      PrefixHalfStep hist step.successEvent := by
  exact v13PrefixInstantiated_iff_prefixHalfStep

theorem no_v13_prefix_certificate_from_failed_half_step_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hfail : ¬ PrefixHalfStep hist step.successEvent) :
    ¬ V13PrefixInstantiated hist step := by
  exact not_v13PrefixInstantiated_of_not_prefixHalfStep hfail

def v13_prefix_certificate_from_concrete_certificate_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cert : V13ConcretePrefixInstantiation hist step) :
    V13PrefixInstantiation hist step := by
  exact v13PrefixInstantiation_of_concretePrefixInstantiation cert

theorem prefix_half_step_from_concrete_certificate_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cert : V13ConcretePrefixInstantiation hist step) :
    PrefixHalfStep hist step.successEvent := by
  exact prefixHalfStep_of_v13ConcretePrefixInstantiation cert

theorem finite_event_count_cell_partition_regression
    {Ω Cell : Type u} [Fintype Ω] [Fintype Cell] [DecidableEq Cell]
    {E : Ω → Prop} [DecidablePred E] (cellOf : Ω → Cell) :
    finiteEventCount Ω E =
      Finset.univ.sum (fun cell =>
        finiteEventCount Ω (fun ω => E ω ∧ cellOf ω = cell)) := by
  exact finiteEventCount_cell_partition cellOf

theorem finite_event_count_split_regression
    {Ω : Type u} [Fintype Ω]
    {E F : Ω → Prop} [DecidablePred E] [DecidablePred F] :
    finiteEventCount Ω E =
      finiteEventCount Ω (fun ω => E ω ∧ F ω) +
        finiteEventCount Ω (fun ω => E ω ∧ ¬ F ω) := by
  exact finiteEventCount_split

theorem concrete_prefix_count_decomp_regression
    {Ω Cell : Type u} [Fintype Ω] [Fintype Cell] [DecidableEq Cell]
    (hist : List (FiniteEvent Ω)) (cellOf : Ω → Cell) :
    finiteHistoryCount Ω hist =
      Finset.univ.sum (v13ConcretePrefixCount (Ω := Ω) hist cellOf) := by
  exact v13ConcretePrefixCount_decomp hist cellOf

theorem concrete_success_count_decomp_regression
    {Ω Cell : Type u} [Fintype Ω] [Fintype Cell] [DecidableEq Cell]
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω)
    (cellOf : Ω → Cell) :
    finiteHistoryCount Ω (hist ++ [step.successEvent]) =
      Finset.univ.sum (v13ConcreteSuccessCount (Ω := Ω) hist step cellOf) := by
  exact v13ConcreteSuccessCount_decomp hist step cellOf

theorem concrete_prefix_count_success_failure_split_regression
    {Ω Cell : Type u} [Fintype Ω] [DecidableEq Cell]
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω)
    (cellOf : Ω → Cell) (cell : Cell) :
    v13ConcretePrefixCount (Ω := Ω) hist cellOf cell =
      v13ConcreteSuccessCount (Ω := Ω) hist step cellOf cell +
        v13ConcreteFailureCount (Ω := Ω) hist step cellOf cell := by
  exact v13ConcretePrefixCount_eq_success_add_failure hist step cellOf cell

theorem concrete_cell_half_iff_success_le_failure_regression
    {Ω Cell : Type u} [Fintype Ω] [DecidableEq Cell]
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω)
    (cellOf : Ω → Cell) (cell : Cell) :
    (2 * v13ConcreteSuccessCount (Ω := Ω) hist step cellOf cell ≤
        v13ConcretePrefixCount (Ω := Ω) hist cellOf cell) ↔
      v13ConcreteSuccessCount (Ω := Ω) hist step cellOf cell ≤
        v13ConcreteFailureCount (Ω := Ω) hist step cellOf cell := by
  exact v13ConcreteCellHalf_iff_success_le_failure hist step cellOf cell

def concrete_prefix_certificate_from_prefix_half_step_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (h : PrefixHalfStep hist step.successEvent) :
    V13ConcretePrefixInstantiation hist step := by
  exact v13ConcretePrefixInstantiation_of_prefixHalfStep h

def concrete_prefix_certificate_from_cell_half_regression
    {Ω Cell : Type u} [Fintype Ω] [Fintype Cell] [DecidableEq Cell]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cellOf : Ω → Cell)
    (hhalf : ∀ cell,
      2 * v13ConcreteSuccessCount (Ω := Ω) hist step cellOf cell ≤
        v13ConcretePrefixCount (Ω := Ω) hist cellOf cell) :
    V13ConcretePrefixInstantiation hist step := by
  exact v13ConcretePrefixInstantiation_of_cellHalf cellOf hhalf

theorem concrete_prefix_instantiated_iff_prefix_half_step_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω} :
    V13ConcretePrefixInstantiated hist step ↔
      PrefixHalfStep hist step.successEvent := by
  exact v13ConcretePrefixInstantiated_iff_prefixHalfStep

end Mettapedia.Computability.PNP.PNPv13SwitchingInstantiationRegression
