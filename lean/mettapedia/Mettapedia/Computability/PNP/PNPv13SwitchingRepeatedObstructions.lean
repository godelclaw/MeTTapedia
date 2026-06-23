import Mettapedia.Computability.PNP.PNPv13SwitchingEquivalences

/-!
# PNP v13 switching: repeated-step obstructions

Repeated success-event blockers for abstract and concrete v13 switching interfaces.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

universe u

/-- A positive-mass switched step cannot be repeated in the abstract v13
switching interface: after the first success event, the same event cannot halve
the current history again. -/
theorem not_v13SwitchingInstantiatedFrom_repeated_step_of_positive
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13SwitchingInstantiatedFrom hist [step, step] := by
  intro h
  have hadm :
      SequentialHalfAdmissibleFrom hist
        [step.successEvent, step.successEvent] := by
    simpa [v13SuccessEvents] using
      sequentialHalfAdmissibleFrom_of_v13SwitchingInstantiatedFrom h
  exact
    not_sequentialHalfAdmissibleFrom_repeated_pair_of_positive hpos hadm

/-- Empty-history form of the repeated switched-step obstruction. -/
theorem not_v13SwitchingInstantiated_repeated_step_of_positive
    {Ω : Type u} [Fintype Ω] {step : V13SwitchedStep Ω}
    (hpos : 0 < finiteHistoryCount Ω [step.successEvent]) :
    ¬ V13SwitchingInstantiated [step, step] := by
  simpa [V13SwitchingInstantiated] using
    not_v13SwitchingInstantiatedFrom_repeated_step_of_positive
      (Ω := Ω) (hist := ([] : List (FiniteEvent Ω))) (step := step)
      (by simpa using hpos)

/-- The repeated-step obstruction also blocks the existential concrete-cell
v13 interface. -/
theorem not_v13ConcreteSwitchingInstantiatedFrom_repeated_step_of_positive
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13ConcreteSwitchingInstantiatedFrom hist [step, step] := by
  intro h
  exact not_v13SwitchingInstantiatedFrom_repeated_step_of_positive hpos
    (v13SwitchingInstantiatedFrom_of_concreteSwitchingInstantiatedFrom h)

/-- Empty-history form for the existential concrete-cell v13 interface. -/
theorem not_v13ConcreteSwitchingInstantiated_repeated_step_of_positive
    {Ω : Type u} [Fintype Ω] {step : V13SwitchedStep Ω}
    (hpos : 0 < finiteHistoryCount Ω [step.successEvent]) :
    ¬ V13ConcreteSwitchingInstantiated [step, step] := by
  simpa [V13ConcreteSwitchingInstantiated] using
    not_v13ConcreteSwitchingInstantiatedFrom_repeated_step_of_positive
      (Ω := Ω) (hist := ([] : List (FiniteEvent Ω))) (step := step)
      (by simpa using hpos)

end Mettapedia.Computability.PNP
