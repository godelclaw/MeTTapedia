import Mettapedia.Computability.PNP.PNPv13SwitchingFieldedAppendObstructions

/-!
# PNP v13 fielded switching: sequential admissibility and product bounds

Consequences from fielded certificates to sequential half-admissibility and tower product bounds, including repeated-step and product-violation blockers.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

universe u

/-- Fixed-field v13 certificates instantiate the generic sequential
half-admissibility interface. -/
theorem sequentialHalfAdmissibleFrom_of_v13FieldSwitchingInstantiatedFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (h : V13FieldSwitchingInstantiatedFrom hist items) :
    SequentialHalfAdmissibleFrom hist (v13FieldedSuccessEvents items) := by
  induction items generalizing hist with
  | nil =>
      trivial
  | cons item rest ih =>
      rcases h with ⟨hitem, hrest⟩
      exact ⟨by
        simpa [PrefixHalfStep] using
          prefixHalfStep_of_v13FieldPrefixInstantiation hitem, ih hrest⟩

/-- No choice of fixed fields can make a positive-mass repeated fielded step
sequentially admissible: the second copy has conditional success mass `1`. -/
theorem not_v13FieldSwitchingInstantiatedFrom_repeated_item_of_positive
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {item : V13FieldedStep Ω}
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [item.step.successEvent])) :
    ¬ V13FieldSwitchingInstantiatedFrom hist [item, item] := by
  intro h
  have hadm :
      SequentialHalfAdmissibleFrom hist
        [item.step.successEvent, item.step.successEvent] := by
    simpa [v13FieldedSuccessEvents] using
      sequentialHalfAdmissibleFrom_of_v13FieldSwitchingInstantiatedFrom h
  exact
    not_sequentialHalfAdmissibleFrom_repeated_pair_of_positive hpos hadm

/-- Empty-history form of the repeated-fielded-step obstruction. -/
theorem not_v13FieldSwitchingInstantiated_repeated_item_of_positive
    {Ω : Type u} [Fintype Ω] {item : V13FieldedStep Ω}
    (hpos : 0 < finiteHistoryCount Ω [item.step.successEvent]) :
    ¬ V13FieldSwitchingInstantiated [item, item] := by
  simpa [V13FieldSwitchingInstantiated] using
    not_v13FieldSwitchingInstantiatedFrom_repeated_item_of_positive
      (Ω := Ω) (hist := ([] : List (FiniteEvent Ω))) (item := item)
      (by simpa using hpos)

/-- The same repeated-fielded-step obstruction blocks the operational
same-cell matching formulation. -/
theorem not_v13FieldSwitchingFailureMatchingFrom_repeated_item_of_positive
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {item : V13FieldedStep Ω}
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [item.step.successEvent])) :
    ¬ V13FieldSwitchingFailureMatchingFrom hist [item, item] := by
  intro hmatch
  exact not_v13FieldSwitchingInstantiatedFrom_repeated_item_of_positive hpos
    (v13FieldSwitchingInstantiatedFrom_iff_failureMatchingFrom.mpr hmatch)

/-- Empty-history form of the repeated-fielded-step matching obstruction. -/
theorem not_v13FieldSwitchingFailureMatching_repeated_item_of_positive
    {Ω : Type u} [Fintype Ω] {item : V13FieldedStep Ω}
    (hpos : 0 < finiteHistoryCount Ω [item.step.successEvent]) :
    ¬ V13FieldSwitchingFailureMatching [item, item] := by
  simpa [V13FieldSwitchingFailureMatching] using
    not_v13FieldSwitchingFailureMatchingFrom_repeated_item_of_positive
      (Ω := Ω) (hist := ([] : List (FiniteEvent Ω))) (item := item)
      (by simpa using hpos)

/-- Fixed-field v13 certificates imply the finite tower product bound from an
arbitrary existing success history. -/
theorem v13_product_bound_of_fieldInstantiatedFrom
    {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (items : List (V13FieldedStep Ω))
    (h : V13FieldSwitchingInstantiatedFrom hist items) :
    2 ^ items.length * finiteHistoryCount Ω (hist ++ v13FieldedSuccessEvents items) ≤
      finiteHistoryCount Ω hist := by
  have hadm :
      SequentialHalfAdmissibleFrom hist (v13FieldedSuccessEvents items) :=
    sequentialHalfAdmissibleFrom_of_v13FieldSwitchingInstantiatedFrom h
  simpa [v13FieldedSuccessEvents_length] using
    finiteHistory_product_bound_of_sequentialHalfFrom hist
      (v13FieldedSuccessEvents items) hadm

/-- Fixed-field v13 certificates imply the finite tower product bound from the
empty success history. -/
theorem v13_product_bound_of_fieldInstantiated
    {Ω : Type u} [Fintype Ω]
    (items : List (V13FieldedStep Ω))
    (h : V13FieldSwitchingInstantiated items) :
    2 ^ items.length * finiteHistoryCount Ω (v13FieldedSuccessEvents items) ≤
      finiteHistoryCount Ω ([] : List (FiniteEvent Ω)) := by
  simpa [V13FieldSwitchingInstantiated] using
    v13_product_bound_of_fieldInstantiatedFrom
      ([] : List (FiniteEvent Ω)) items h

/-- Recursive same-cell matchings imply the finite tower product bound. -/
theorem v13_product_bound_of_fieldFailureMatchingFrom
    {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (items : List (V13FieldedStep Ω))
    (h : V13FieldSwitchingFailureMatchingFrom hist items) :
    2 ^ items.length * finiteHistoryCount Ω (hist ++ v13FieldedSuccessEvents items) ≤
      finiteHistoryCount Ω hist := by
  exact v13_product_bound_of_fieldInstantiatedFrom hist items
    (v13FieldSwitchingInstantiatedFrom_iff_failureMatchingFrom.mpr h)

/-- Empty-history tower product bound from recursive same-cell matchings. -/
theorem v13_product_bound_of_fieldFailureMatching
    {Ω : Type u} [Fintype Ω]
    (items : List (V13FieldedStep Ω))
    (h : V13FieldSwitchingFailureMatching items) :
    2 ^ items.length * finiteHistoryCount Ω (v13FieldedSuccessEvents items) ≤
      finiteHistoryCount Ω ([] : List (FiniteEvent Ω)) := by
  simpa [V13FieldSwitchingFailureMatching] using
    v13_product_bound_of_fieldFailureMatchingFrom
      ([] : List (FiniteEvent Ω)) items h

/-- A global tower-product violation blocks any fixed-field v13 instantiation,
regardless of the individual cells. -/
theorem not_v13FieldSwitchingInstantiatedFrom_of_product_bound_violation
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hbad :
      ¬ 2 ^ items.length *
          finiteHistoryCount Ω (hist ++ v13FieldedSuccessEvents items) ≤
        finiteHistoryCount Ω hist) :
    ¬ V13FieldSwitchingInstantiatedFrom hist items := by
  intro h
  exact hbad (v13_product_bound_of_fieldInstantiatedFrom hist items h)

/-- Empty-history fixed-field v13 blocker from failure of the global
tower-product inequality. -/
theorem not_v13FieldSwitchingInstantiated_of_product_bound_violation
    {Ω : Type u} [Fintype Ω]
    {items : List (V13FieldedStep Ω)}
    (hbad :
      ¬ 2 ^ items.length * finiteHistoryCount Ω (v13FieldedSuccessEvents items) ≤
        finiteHistoryCount Ω ([] : List (FiniteEvent Ω))) :
    ¬ V13FieldSwitchingInstantiated items := by
  intro h
  exact hbad (v13_product_bound_of_fieldInstantiated items h)

/-- A global tower-product violation also blocks the operational recursive
same-cell matching obligation directly. -/
theorem not_v13FieldSwitchingFailureMatchingFrom_of_product_bound_violation
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hbad :
      ¬ 2 ^ items.length *
          finiteHistoryCount Ω (hist ++ v13FieldedSuccessEvents items) ≤
        finiteHistoryCount Ω hist) :
    ¬ V13FieldSwitchingFailureMatchingFrom hist items := by
  intro hmatch
  exact hbad (v13_product_bound_of_fieldFailureMatchingFrom hist items hmatch)

/-- Empty-history tower-product blocker for the operational recursive same-cell
matching obligation. -/
theorem not_v13FieldSwitchingFailureMatching_of_product_bound_violation
    {Ω : Type u} [Fintype Ω]
    {items : List (V13FieldedStep Ω)}
    (hbad :
      ¬ 2 ^ items.length * finiteHistoryCount Ω (v13FieldedSuccessEvents items) ≤
        finiteHistoryCount Ω ([] : List (FiniteEvent Ω))) :
    ¬ V13FieldSwitchingFailureMatching items := by
  intro hmatch
  exact hbad (v13_product_bound_of_fieldFailureMatching items hmatch)

end Mettapedia.Computability.PNP
