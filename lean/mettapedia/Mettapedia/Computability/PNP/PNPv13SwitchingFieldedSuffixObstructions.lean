import Mettapedia.Computability.PNP.PNPv13SwitchingFieldedFailureLocalization

/-!
# PNP v13 fielded switching: suffix blockers

Fielded-switching suffix blockers from failed prefix certificates, missing same-cell failures, and success-determining fields.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

universe u

/-- One failed fixed-field prefix certificate blocks the corresponding
fixed-field switching suffix. -/
theorem not_v13FieldSwitchingInstantiatedFrom_cons_of_not_fieldPrefixInstantiation
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {item : V13FieldedStep Ω} {rest : List (V13FieldedStep Ω)}
    (hfail : ¬ V13FieldPrefixInstantiation item.field hist item.step) :
    ¬ V13FieldSwitchingInstantiatedFrom hist (item :: rest) := by
  intro h
  exact hfail h.1

/-- If the supplied first field in a fielded suffix determines the next success
event on the current history support and that next-success prefix has positive
mass, the whole fielded suffix is blocked. -/
theorem not_v13FieldSwitchingInstantiatedFrom_cons_of_fieldDeterminesSuccessOn_positive_success
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {item : V13FieldedStep Ω}
    {rest : List (V13FieldedStep Ω)}
    (hdet : V13HistoryFieldDeterminesSuccessOn item.field hist item.step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [item.step.successEvent])) :
    ¬ V13FieldSwitchingInstantiatedFrom hist (item :: rest) := by
  exact not_v13FieldSwitchingInstantiatedFrom_cons_of_not_fieldPrefixInstantiation
    (not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccessOn_positive_success
      hdet hpos)

/-- If the supplied first field in a fielded suffix globally determines the next
success event and that next-success prefix has positive mass, the whole fielded
suffix is blocked. -/
theorem not_v13FieldSwitchingInstantiatedFrom_cons_of_fieldDeterminesSuccess_positive_success
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {item : V13FieldedStep Ω}
    {rest : List (V13FieldedStep Ω)}
    (hdet : V13HistoryFieldDeterminesSuccess item.field item.step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [item.step.successEvent])) :
    ¬ V13FieldSwitchingInstantiatedFrom hist (item :: rest) := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_cons_of_fieldDeterminesSuccessOn_positive_success
      (v13HistoryFieldDeterminesSuccessOn_of_determinesSuccess hdet) hpos

/-- A failed fixed-field prefix certificate at any later position blocks the
whole fielded switching list.  The history at the failed item is exactly the
incoming history extended by the success events of the preceding fielded
prefix. -/
theorem not_v13FieldSwitchingInstantiatedFrom_append_cons_of_not_fieldPrefixInstantiation
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hfail :
      ¬ V13FieldPrefixInstantiation item.field
          (hist ++ v13FieldedSuccessEvents pre) item.step) :
    ¬ V13FieldSwitchingInstantiatedFrom hist (pre ++ item :: suffix) := by
  induction pre generalizing hist with
  | nil =>
      have hfail' :
          ¬ V13FieldPrefixInstantiation item.field hist item.step := by
        simpa [v13FieldedSuccessEvents] using hfail
      simpa using
        (not_v13FieldSwitchingInstantiatedFrom_cons_of_not_fieldPrefixInstantiation
          (hist := hist) (item := item) (rest := suffix) hfail')
  | cons head tail ih =>
      intro h
      have hfail' :
          ¬ V13FieldPrefixInstantiation item.field
              ((hist ++ [head.step.successEvent]) ++
                v13FieldedSuccessEvents tail) item.step := by
        simpa [v13FieldedSuccessEvents, List.append_assoc] using hfail
      exact ih (hist := hist ++ [head.step.successEvent]) hfail' h.2

/-- A single successful point whose accumulated-history field cell contains no
failed point blocks the whole fixed-field switching instantiation. -/
theorem not_v13FieldSwitchingInstantiatedFrom_append_cons_of_success_without_sameCell_failure
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)} {ω : Ω}
    (hhist : allEvents (hist ++ v13FieldedSuccessEvents pre) ω)
    (hsucc : item.step.successEvent.pred ω)
    (hnoFailure :
      ∀ ⦃ω' : Ω⦄,
        allEvents (hist ++ v13FieldedSuccessEvents pre) ω' →
          item.field.cellOf ω' = item.field.cellOf ω →
            item.step.successEvent.pred ω') :
    ¬ V13FieldSwitchingInstantiatedFrom hist (pre ++ item :: suffix) := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_append_cons_of_not_fieldPrefixInstantiation
      (hist := hist) (pre := pre) (item := item) (suffix := suffix)
      (not_v13FieldPrefixInstantiation_of_success_without_sameCell_failure
        (field := item.field) (hist := hist ++ v13FieldedSuccessEvents pre)
        (step := item.step) hhist hsucc hnoFailure)

/-- If any later supplied field determines its next success event on the
accumulated history support and the corresponding next-success prefix has
positive mass, the whole fielded switching list is blocked. -/
theorem not_v13FieldSwitchingInstantiatedFrom_append_cons_of_fieldDeterminesSuccessOn_positive_success
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
    not_v13FieldSwitchingInstantiatedFrom_append_cons_of_not_fieldPrefixInstantiation
      (hist := hist) (pre := pre) (item := item) (suffix := suffix)
      (not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccessOn_positive_success
        (Ω := Ω) (field := item.field)
        (hist := hist ++ v13FieldedSuccessEvents pre) (step := item.step)
        hdet hpos)

/-- If any later supplied field globally determines its next success event and
the corresponding next-success prefix has positive mass, the whole fielded
switching list is blocked. -/
theorem not_v13FieldSwitchingInstantiatedFrom_append_cons_of_fieldDeterminesSuccess_positive_success
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
    not_v13FieldSwitchingInstantiatedFrom_append_cons_of_fieldDeterminesSuccessOn_positive_success
      (hdet :=
        v13HistoryFieldDeterminesSuccessOn_of_determinesSuccess
          (hist := hist ++ v13FieldedSuccessEvents pre) hdet)
      hpos

/-- A success-revealing fielded step with positive next-success mass blocks the
entire fixed-field switching suffix. -/
theorem not_v13FieldSwitchingInstantiatedFrom_successField_cons_of_positive_success
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} {rest : List (V13FieldedStep Ω)}
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13FieldSwitchingInstantiatedFrom hist
      (v13SuccessFieldedStep step :: rest) := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_cons_of_not_fieldPrefixInstantiation
      (not_v13FieldPrefixInstantiation_successHistoryField_of_positive_success hpos)

end Mettapedia.Computability.PNP
