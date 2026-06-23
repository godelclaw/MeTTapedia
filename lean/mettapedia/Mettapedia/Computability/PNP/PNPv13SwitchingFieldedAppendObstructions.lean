import Mettapedia.Computability.PNP.PNPv13SwitchingFieldedEquivalences

/-!
# PNP v13 fielded switching: append-position matching obstructions

Later-position extraction of same-cell matching obligations and positive-success blockers for success-determining supplied fields.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

universe u

/-- Extract the same-cell matching obligation for any later fielded step from
the recursive fielded matching proof. -/
theorem v13FieldFailureMatching_at_append_cons_of_failureMatchingFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (h : V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix)) :
    V13FieldFailureMatching item.field
      (hist ++ v13FieldedSuccessEvents pre) item.step := by
  induction pre generalizing hist with
  | nil =>
      simpa [v13FieldedSuccessEvents] using h.1
  | cons head tail ih =>
      have htail :
          V13FieldSwitchingFailureMatchingFrom
            (hist ++ [head.step.successEvent]) (tail ++ item :: suffix) := h.2
      have hitem := ih (hist := hist ++ [head.step.successEvent]) htail
      simpa [v13FieldedSuccessEvents, List.append_assoc] using hitem

/-- At any later fielded position, recursive same-cell matching supplies an
explicit failed prefix point in the same field cell for every successful prefix
point. -/
theorem exists_sameCell_failure_at_append_cons_of_failureMatchingFrom_success
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hmatch :
      V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix))
    {ω : Ω}
    (hhist : allEvents (hist ++ v13FieldedSuccessEvents pre) ω)
    (hsucc : item.step.successEvent.pred ω) :
    ∃ ω' : Ω,
      allEvents (hist ++ v13FieldedSuccessEvents pre) ω' ∧
        item.field.cellOf ω' = item.field.cellOf ω ∧
          ¬ item.step.successEvent.pred ω' := by
  exact
    exists_sameCell_failure_of_fieldFailureMatching_success
      (v13FieldFailureMatching_at_append_cons_of_failureMatchingFrom
        (hist := hist) (pre := pre) (item := item) (suffix := suffix) hmatch)
      hhist hsucc

/-- A single successful point whose accumulated-history field cell contains no
failed point blocks the recursive same-cell matching obligation. -/
theorem not_v13FieldSwitchingFailureMatchingFrom_append_cons_of_success_without_sameCell_failure
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
    ¬ V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix) := by
  intro hmatch
  rcases exists_sameCell_failure_at_append_cons_of_failureMatchingFrom_success
      hmatch hhist hsucc with
    ⟨ω', hhist', hcell', hfail'⟩
  exact hfail' (hnoFailure hhist' hcell')

/-- At any later fielded position, a recursive matching proof on a positive
next-success prefix rules out a supplied field that determines the next success
bit on the accumulated history support. -/
theorem not_v13HistoryFieldDeterminesSuccessOn_at_append_cons_of_failureMatchingFrom_positive_success
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hmatch :
      V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix))
    (hpos :
      0 < finiteHistoryCount Ω
        ((hist ++ v13FieldedSuccessEvents pre) ++ [item.step.successEvent])) :
    ¬ V13HistoryFieldDeterminesSuccessOn item.field
      (hist ++ v13FieldedSuccessEvents pre) item.step := by
  exact
    not_v13HistoryFieldDeterminesSuccessOn_of_failureMatching_positive_success
      (v13FieldFailureMatching_at_append_cons_of_failureMatchingFrom
        (hist := hist) (pre := pre) (item := item) (suffix := suffix) hmatch)
      hpos

/-- At any later fielded position, a recursive matching proof on a positive
next-success prefix rules out a supplied field that globally determines the
next success bit. -/
theorem not_v13HistoryFieldDeterminesSuccess_at_append_cons_of_failureMatchingFrom_positive_success
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hmatch :
      V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix))
    (hpos :
      0 < finiteHistoryCount Ω
        ((hist ++ v13FieldedSuccessEvents pre) ++ [item.step.successEvent])) :
    ¬ V13HistoryFieldDeterminesSuccess item.field item.step := by
  intro hdet
  exact
    not_v13HistoryFieldDeterminesSuccessOn_at_append_cons_of_failureMatchingFrom_positive_success
      hmatch hpos
      (v13HistoryFieldDeterminesSuccessOn_of_determinesSuccess hdet)

/-- A prefix-relative success-determining later field with positive
next-success mass blocks the recursive same-cell matching obligation itself. -/
theorem not_v13FieldSwitchingFailureMatchingFrom_append_cons_of_fieldDeterminesSuccessOn_positive_success
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
    ¬ V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix) := by
  intro hmatch
  exact
    not_v13HistoryFieldDeterminesSuccessOn_at_append_cons_of_failureMatchingFrom_positive_success
      hmatch hpos hdet

/-- A globally success-determining later field with positive next-success mass
blocks the recursive same-cell matching obligation itself. -/
theorem not_v13FieldSwitchingFailureMatchingFrom_append_cons_of_fieldDeterminesSuccess_positive_success
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hdet : V13HistoryFieldDeterminesSuccess item.field item.step)
    (hpos :
      0 < finiteHistoryCount Ω
        ((hist ++ v13FieldedSuccessEvents pre) ++ [item.step.successEvent])) :
    ¬ V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix) := by
  exact
    not_v13FieldSwitchingFailureMatchingFrom_append_cons_of_fieldDeterminesSuccessOn_positive_success
      (hdet :=
        v13HistoryFieldDeterminesSuccessOn_of_determinesSuccess
          (hist := hist ++ v13FieldedSuccessEvents pre) hdet)
      hpos

end Mettapedia.Computability.PNP
