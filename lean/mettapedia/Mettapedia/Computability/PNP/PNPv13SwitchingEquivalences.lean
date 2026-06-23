import Mettapedia.Computability.PNP.PNPv13SwitchingCore

/-!
# PNP v13 switching: sequential equivalences

Equivalence between v13 switching certificates and generic sequential half-admissibility.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

universe u

/-- Concrete semantic v13 certificates supply the abstract v13 summary
certificates. -/
theorem v13SwitchingInstantiatedFrom_of_concreteSwitchingInstantiatedFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (h : V13ConcreteSwitchingInstantiatedFrom hist steps) :
    V13SwitchingInstantiatedFrom hist steps := by
  induction steps generalizing hist with
  | nil =>
      trivial
  | cons step rest ih =>
      rcases h with ⟨hstep, hrest⟩
      exact ⟨v13PrefixInstantiated_of_v13ConcretePrefixInstantiated hstep,
        ih hrest⟩

/-- V13 atom-ledger certificates instantiate the generic sequential
half-admissibility interface. -/
theorem sequentialHalfAdmissibleFrom_of_v13SwitchingInstantiatedFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (h : V13SwitchingInstantiatedFrom hist steps) :
    SequentialHalfAdmissibleFrom hist (v13SuccessEvents steps) := by
  induction steps generalizing hist with
  | nil =>
      trivial
  | cons step rest ih =>
      rcases h with ⟨hstep, hrest⟩
      exact ⟨by
        simpa [PrefixHalfStep] using
          prefixHalfStep_of_v13PrefixInstantiated hstep, ih hrest⟩

/-- Conversely, generic sequential half-admissibility is enough to build the
abstract v13 atom-ledger instantiation, because every prefix half-step can be
represented by a one-cell ledger.  This pins the abstract v13 interface as no
stronger than the generic sequential condition. -/
theorem v13SwitchingInstantiatedFrom_of_sequentialHalfAdmissibleFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (h : SequentialHalfAdmissibleFrom hist (v13SuccessEvents steps)) :
    V13SwitchingInstantiatedFrom hist steps := by
  induction steps generalizing hist with
  | nil =>
      trivial
  | cons step rest ih =>
      rcases h with ⟨hstep, hrest⟩
      have hprefix : PrefixHalfStep hist step.successEvent := by
        simpa [PrefixHalfStep] using hstep
      exact ⟨⟨v13PrefixInstantiation_of_prefixHalfStep hprefix⟩, ih hrest⟩

/-- The whole abstract v13 atom-ledger switching interface is exactly generic
sequential half-admissibility of the induced success events. -/
theorem v13SwitchingInstantiatedFrom_iff_sequentialHalfAdmissibleFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)} :
    V13SwitchingInstantiatedFrom hist steps ↔
      SequentialHalfAdmissibleFrom hist (v13SuccessEvents steps) := by
  constructor
  · exact sequentialHalfAdmissibleFrom_of_v13SwitchingInstantiatedFrom
  · exact v13SwitchingInstantiatedFrom_of_sequentialHalfAdmissibleFrom

/-- Empty-history form: abstract v13 atom-ledger switching is equivalent to
generic sequential half-admissibility of the success-event list. -/
theorem v13SwitchingInstantiated_iff_sequentialHalfAdmissible
    {Ω : Type u} [Fintype Ω] {steps : List (V13SwitchedStep Ω)} :
    V13SwitchingInstantiated steps ↔
      SequentialHalfAdmissible (v13SuccessEvents steps) := by
  exact v13SwitchingInstantiatedFrom_iff_sequentialHalfAdmissibleFrom

/-- Generic sequential half-admissibility is also enough to build the
existential concrete-cell v13 instantiation, by choosing the constant cell map
at every prefix. -/
theorem v13ConcreteSwitchingInstantiatedFrom_of_sequentialHalfAdmissibleFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (h : SequentialHalfAdmissibleFrom hist (v13SuccessEvents steps)) :
    V13ConcreteSwitchingInstantiatedFrom hist steps := by
  induction steps generalizing hist with
  | nil =>
      trivial
  | cons step rest ih =>
      rcases h with ⟨hstep, hrest⟩
      have hprefix : PrefixHalfStep hist step.successEvent := by
        simpa [PrefixHalfStep] using hstep
      exact ⟨⟨v13ConcretePrefixInstantiation_of_prefixHalfStep hprefix⟩, ih hrest⟩

/-- The existential concrete-cell v13 switching interface is exactly generic
sequential half-admissibility of the induced success events.  Semantic force
only appears once the history fields are externally fixed. -/
theorem v13ConcreteSwitchingInstantiatedFrom_iff_sequentialHalfAdmissibleFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)} :
    V13ConcreteSwitchingInstantiatedFrom hist steps ↔
      SequentialHalfAdmissibleFrom hist (v13SuccessEvents steps) := by
  constructor
  · intro h
    exact sequentialHalfAdmissibleFrom_of_v13SwitchingInstantiatedFrom
      (v13SwitchingInstantiatedFrom_of_concreteSwitchingInstantiatedFrom h)
  · exact v13ConcreteSwitchingInstantiatedFrom_of_sequentialHalfAdmissibleFrom

/-- Empty-history form: existential concrete-cell v13 switching is equivalent
to generic sequential half-admissibility of the success-event list. -/
theorem v13ConcreteSwitchingInstantiated_iff_sequentialHalfAdmissible
    {Ω : Type u} [Fintype Ω] {steps : List (V13SwitchedStep Ω)} :
    V13ConcreteSwitchingInstantiated steps ↔
      SequentialHalfAdmissible (v13SuccessEvents steps) := by
  exact v13ConcreteSwitchingInstantiatedFrom_iff_sequentialHalfAdmissibleFrom

end Mettapedia.Computability.PNP
