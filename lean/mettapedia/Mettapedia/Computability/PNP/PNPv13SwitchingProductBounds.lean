import Mettapedia.Computability.PNP.PNPv13SwitchingRepeatedObstructions

/-!
# PNP v13 switching: product bounds

Tower product bounds and product-bound blockers for abstract and concrete v13 switching.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

universe u

/-- V13 atom-ledger certificates imply the finite tower product bound from an
arbitrary existing success history. -/
theorem v13_product_bound_of_instantiatedFrom
    {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (steps : List (V13SwitchedStep Ω))
    (h : V13SwitchingInstantiatedFrom hist steps) :
    2 ^ steps.length * finiteHistoryCount Ω (hist ++ v13SuccessEvents steps) ≤
      finiteHistoryCount Ω hist := by
  have hadm :
      SequentialHalfAdmissibleFrom hist (v13SuccessEvents steps) :=
    sequentialHalfAdmissibleFrom_of_v13SwitchingInstantiatedFrom h
  simpa [v13SuccessEvents_length] using
    finiteHistory_product_bound_of_sequentialHalfFrom hist
      (v13SuccessEvents steps) hadm

/-- V13 atom-ledger certificates imply the finite tower product bound from the
empty success history. -/
theorem v13_product_bound_of_instantiated
    {Ω : Type u} [Fintype Ω]
    (steps : List (V13SwitchedStep Ω))
    (h : V13SwitchingInstantiated steps) :
    2 ^ steps.length * finiteHistoryCount Ω (v13SuccessEvents steps) ≤
      finiteHistoryCount Ω ([] : List (FiniteEvent Ω)) := by
  simpa [V13SwitchingInstantiated] using
    v13_product_bound_of_instantiatedFrom
      ([] : List (FiniteEvent Ω)) steps h

/-- Semantic v13 cell-map certificates imply the finite tower product bound
from an arbitrary existing success history. -/
theorem v13_product_bound_of_concreteInstantiatedFrom
    {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (steps : List (V13SwitchedStep Ω))
    (h : V13ConcreteSwitchingInstantiatedFrom hist steps) :
    2 ^ steps.length * finiteHistoryCount Ω (hist ++ v13SuccessEvents steps) ≤
      finiteHistoryCount Ω hist := by
  exact v13_product_bound_of_instantiatedFrom hist steps
    (v13SwitchingInstantiatedFrom_of_concreteSwitchingInstantiatedFrom h)

/-- Semantic v13 cell-map certificates imply the finite tower product bound
from the empty success history. -/
theorem v13_product_bound_of_concreteInstantiated
    {Ω : Type u} [Fintype Ω]
    (steps : List (V13SwitchedStep Ω))
    (h : V13ConcreteSwitchingInstantiated steps) :
    2 ^ steps.length * finiteHistoryCount Ω (v13SuccessEvents steps) ≤
      finiteHistoryCount Ω ([] : List (FiniteEvent Ω)) := by
  simpa [V13ConcreteSwitchingInstantiated] using
    v13_product_bound_of_concreteInstantiatedFrom
      ([] : List (FiniteEvent Ω)) steps h

/-- A global tower-product violation blocks any v13 abstract atom-ledger
instantiation. -/
theorem not_v13SwitchingInstantiatedFrom_of_product_bound_violation
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (hbad :
      ¬ 2 ^ steps.length *
          finiteHistoryCount Ω (hist ++ v13SuccessEvents steps) ≤
        finiteHistoryCount Ω hist) :
    ¬ V13SwitchingInstantiatedFrom hist steps := by
  intro h
  exact hbad (v13_product_bound_of_instantiatedFrom hist steps h)

/-- Empty-history v13 abstract atom-ledger blocker from failure of the global
tower-product inequality. -/
theorem not_v13SwitchingInstantiated_of_product_bound_violation
    {Ω : Type u} [Fintype Ω]
    {steps : List (V13SwitchedStep Ω)}
    (hbad :
      ¬ 2 ^ steps.length * finiteHistoryCount Ω (v13SuccessEvents steps) ≤
        finiteHistoryCount Ω ([] : List (FiniteEvent Ω))) :
    ¬ V13SwitchingInstantiated steps := by
  intro h
  exact hbad (v13_product_bound_of_instantiated steps h)

/-- A global tower-product violation blocks any semantic concrete-cell v13
instantiation. -/
theorem not_v13ConcreteSwitchingInstantiatedFrom_of_product_bound_violation
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (hbad :
      ¬ 2 ^ steps.length *
          finiteHistoryCount Ω (hist ++ v13SuccessEvents steps) ≤
        finiteHistoryCount Ω hist) :
    ¬ V13ConcreteSwitchingInstantiatedFrom hist steps := by
  intro h
  exact hbad (v13_product_bound_of_concreteInstantiatedFrom hist steps h)

/-- Empty-history concrete-cell v13 blocker from failure of the global
tower-product inequality. -/
theorem not_v13ConcreteSwitchingInstantiated_of_product_bound_violation
    {Ω : Type u} [Fintype Ω]
    {steps : List (V13SwitchedStep Ω)}
    (hbad :
      ¬ 2 ^ steps.length * finiteHistoryCount Ω (v13SuccessEvents steps) ≤
        finiteHistoryCount Ω ([] : List (FiniteEvent Ω))) :
    ¬ V13ConcreteSwitchingInstantiated steps := by
  intro h
  exact hbad (v13_product_bound_of_concreteInstantiated steps h)

end Mettapedia.Computability.PNP
