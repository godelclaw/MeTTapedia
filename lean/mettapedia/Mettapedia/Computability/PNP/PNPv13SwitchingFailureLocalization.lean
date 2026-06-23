import Mettapedia.Computability.PNP.PNPv13SwitchingProductBounds

/-!
# PNP v13 switching: failure localization

Localization of failed prefix half-step obligations from switching failures and product-bound violations.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

universe u

/-- One failed prefix half-step blocks the corresponding v13 atom-ledger
instantiation for the whole remaining switched suffix. -/
theorem not_v13SwitchingInstantiatedFrom_cons_of_not_prefixHalfStep
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} {rest : List (V13SwitchedStep Ω)}
    (hfail : ¬ PrefixHalfStep hist step.successEvent) :
    ¬ V13SwitchingInstantiatedFrom hist (step :: rest) := by
  intro h
  exact not_v13PrefixInstantiated_of_not_prefixHalfStep hfail h.1

/-- Failure of abstract v13 switching localizes to one switched coordinate
whose induced success event fails the generic prefix half-step at the exact
accumulated success history. -/
theorem exists_failed_prefixHalfStep_at_append_cons_of_not_v13SwitchingInstantiatedFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (hfail : ¬ V13SwitchingInstantiatedFrom hist steps) :
    ∃ pre step suffix,
      steps = pre ++ step :: suffix ∧
        ¬ PrefixHalfStep (hist ++ v13SuccessEvents pre) step.successEvent := by
  induction steps generalizing hist with
  | nil =>
      exact False.elim (hfail trivial)
  | cons step rest ih =>
      by_cases hstep : PrefixHalfStep hist step.successEvent
      · have hrest :
            ¬ V13SwitchingInstantiatedFrom
                (hist ++ [step.successEvent]) rest := by
          intro htail
          exact hfail ⟨⟨v13PrefixInstantiation_of_prefixHalfStep hstep⟩, htail⟩
        rcases ih (hist := hist ++ [step.successEvent]) hrest with
          ⟨pre, failedStep, suffix, hsteps, hbad⟩
        refine ⟨step :: pre, failedStep, suffix, ?_, ?_⟩
        · simp [hsteps]
        · simpa [v13SuccessEvents, List.append_assoc] using hbad
      · refine ⟨[], step, rest, ?_, ?_⟩
        · simp
        · simpa [v13SuccessEvents] using hstep

/-- A v13 tower-product violation localizes to one switched coordinate whose
conditional half-success prefix cut fails. -/
theorem exists_failed_prefixHalfStep_at_append_cons_of_v13_product_bound_violation
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
    exists_failed_prefixHalfStep_at_append_cons_of_not_v13SwitchingInstantiatedFrom
      (not_v13SwitchingInstantiatedFrom_of_product_bound_violation hbad)

/-- Empty-history form: a v13 tower-product violation gives an exact failed
conditional cut in the switched-coordinate list. -/
theorem exists_failed_prefixHalfStep_at_append_cons_of_v13_empty_product_bound_violation
    {Ω : Type u} [Fintype Ω]
    {steps : List (V13SwitchedStep Ω)}
    (hbad :
      ¬ 2 ^ steps.length * finiteHistoryCount Ω (v13SuccessEvents steps) ≤
        finiteHistoryCount Ω ([] : List (FiniteEvent Ω))) :
    ∃ pre step suffix,
      steps = pre ++ step :: suffix ∧
        ¬ PrefixHalfStep (v13SuccessEvents pre) step.successEvent := by
  simpa using
    exists_failed_prefixHalfStep_at_append_cons_of_v13_product_bound_violation
      (Ω := Ω) (hist := ([] : List (FiniteEvent Ω)))
      (steps := steps) (by simpa using hbad)

end Mettapedia.Computability.PNP
