import Mettapedia.Computability.PNP.PNPv13SwitchingHistoryFailureMatching

/-!
# PNP v13 switching: success-determination obstructions

Obstructions showing that success-determining supplied fields cannot satisfy the fixed-field matching certificate at positive next-success mass.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

universe u

/-- If a field cell has more next-success points than next-failure points, the
fixed-field prefix certificate is impossible. -/
theorem not_v13FieldPrefixInstantiation_of_success_gt_failure
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} (cell : field.Cell)
    (hbad :
      v13ConcreteFailureCount (Ω := Ω) hist step field.cellOf cell <
        v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  intro cert
  have hbalance :=
    (v13FieldPrefixInstantiation_iff_success_le_failure.mp cert) cell
  exact (not_le_of_gt hbad) hbalance

/-- In a prefix-relative success-homogeneous field cell, positive success mass
forces the next-failure count in that same cell to be zero. -/
theorem v13ConcreteFailureCount_eq_zero_of_fieldDeterminesSuccessOn_of_success_pos
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccessOn field hist step)
    (cell : field.Cell)
    (hpos : 0 < v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell) :
    v13ConcreteFailureCount (Ω := Ω) hist step field.cellOf cell = 0 := by
  have hnonempty :
      Nonempty {ω : Ω //
        allEvents hist ω ∧ field.cellOf ω = cell ∧ step.successEvent.pred ω} := by
    exact Fintype.card_pos_iff.mp (by
      simpa [v13ConcreteSuccessCount, finiteEventCount] using hpos)
  rcases hnonempty with ⟨⟨ω₀, hhist₀, hcell₀, hsuccess₀⟩⟩
  apply Nat.eq_zero_of_le_zero
  have hle :
      finiteEventCount Ω
          (fun ω =>
            allEvents hist ω ∧ field.cellOf ω = cell ∧
              ¬ step.successEvent.pred ω) ≤
        finiteEventCount Ω (fun _ : Ω => False) := by
    exact finiteEventCount_le_of_imp (Ω := Ω)
      (E := fun ω =>
        allEvents hist ω ∧ field.cellOf ω = cell ∧
          ¬ step.successEvent.pred ω)
      (F := fun _ : Ω => False)
      (by
        intro ω hω
        exact hω.2.2
          (hdet hhist₀ hω.1 (hcell₀.trans hω.2.1.symm) hsuccess₀))
  simpa [v13ConcreteFailureCount, finiteEventCount] using hle

/-- In a globally success-homogeneous field cell, positive success mass forces
the next-failure count in that same cell to be zero. -/
theorem v13ConcreteFailureCount_eq_zero_of_fieldDeterminesSuccess_of_success_pos
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccess field step)
    (cell : field.Cell)
    (hpos : 0 < v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell) :
    v13ConcreteFailureCount (Ω := Ω) hist step field.cellOf cell = 0 := by
  exact
    v13ConcreteFailureCount_eq_zero_of_fieldDeterminesSuccessOn_of_success_pos
      (v13HistoryFieldDeterminesSuccessOn_of_determinesSuccess hdet) cell hpos

/-- If a supplied field determines the next success event on the current
history support, any cell with positive next-success mass blocks the fixed-field
prefix certificate. -/
theorem not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccessOn_cell_success
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccessOn field hist step)
    (cell : field.Cell)
    (hpos : 0 < v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  have hfailure_zero :=
    v13ConcreteFailureCount_eq_zero_of_fieldDeterminesSuccessOn_of_success_pos
      (Ω := Ω) (field := field) (hist := hist) (step := step)
      hdet cell hpos
  exact not_v13FieldPrefixInstantiation_of_success_gt_failure cell (by
    rw [hfailure_zero]
    exact hpos)

/-- If a supplied field determines the next success event, any cell with
positive next-success mass blocks the fixed-field prefix certificate. -/
theorem not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccess_cell_success
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccess field step)
    (cell : field.Cell)
    (hpos : 0 < v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact
    not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccessOn_cell_success
      (v13HistoryFieldDeterminesSuccessOn_of_determinesSuccess hdet) cell hpos

/-- A prefix-relative success-determining field can satisfy the fixed-field
prefix certificate only when the next-success prefix has zero mass. -/
theorem not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccessOn_positive_success
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccessOn field hist step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  have hnonempty :
      Nonempty {ω : Ω // allEvents (hist ++ [step.successEvent]) ω} := by
    exact Fintype.card_pos_iff.mp (by
      simpa [finiteHistoryCount, finiteEventCount] using hpos)
  rcases hnonempty with ⟨⟨ω, hω⟩⟩
  have hboth := (allEvents_append_singleton_iff hist step.successEvent ω).mp hω
  let cell : field.Cell := field.cellOf ω
  have hcellpos :
      0 < v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell := by
    rw [v13ConcreteSuccessCount]
    exact Fintype.card_pos_iff.mpr ⟨⟨ω, hboth.1, rfl, hboth.2⟩⟩
  exact not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccessOn_cell_success
    hdet cell hcellpos

/-- A success-determining field can satisfy the fixed-field prefix certificate
only when the next-success prefix has zero mass. -/
theorem not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccess_positive_success
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccess field step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact
    not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccessOn_positive_success
      (v13HistoryFieldDeterminesSuccessOn_of_determinesSuccess hdet) hpos

/-- A prefix-relative success-determining field with positive next-success mass
cannot satisfy the operational same-cell failure-matching obligation. -/
theorem not_v13FieldFailureMatching_of_fieldDeterminesSuccessOn_positive_success
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccessOn field hist step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13FieldFailureMatching field hist step := by
  intro hmatch
  exact not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccessOn_positive_success
    hdet hpos (v13FieldPrefixInstantiation_of_failureMatching hmatch)

/-- A success-determining field with positive next-success mass cannot satisfy
the operational same-cell failure-matching obligation. -/
theorem not_v13FieldFailureMatching_of_fieldDeterminesSuccess_positive_success
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccess field step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13FieldFailureMatching field hist step := by
  exact
    not_v13FieldFailureMatching_of_fieldDeterminesSuccessOn_positive_success
      (v13HistoryFieldDeterminesSuccessOn_of_determinesSuccess hdet) hpos

/-- Conversely, a valid same-cell failure matching on a positive next-success
prefix proves that the supplied field does not determine the next success bit
on the current history support. -/
theorem not_v13HistoryFieldDeterminesSuccessOn_of_failureMatching_positive_success
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hmatch : V13FieldFailureMatching field hist step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13HistoryFieldDeterminesSuccessOn field hist step := by
  intro hdet
  exact
    not_v13FieldFailureMatching_of_fieldDeterminesSuccessOn_positive_success
      hdet hpos hmatch

/-- Conversely, a valid same-cell failure matching on a positive next-success
prefix proves that the supplied field does not globally determine the next
success bit. -/
theorem not_v13HistoryFieldDeterminesSuccess_of_failureMatching_positive_success
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hmatch : V13FieldFailureMatching field hist step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13HistoryFieldDeterminesSuccess field step := by
  intro hdet
  exact
    not_v13HistoryFieldDeterminesSuccessOn_of_failureMatching_positive_success
      hmatch hpos
      (v13HistoryFieldDeterminesSuccessOn_of_determinesSuccess hdet)


end Mettapedia.Computability.PNP
