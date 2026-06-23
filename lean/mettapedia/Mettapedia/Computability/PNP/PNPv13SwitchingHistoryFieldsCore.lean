import Mettapedia.Computability.PNP.PNPv13SwitchingInstantiationConcrete

/-!
# PNP v13 switching fixed history fields

Fixed history-field certificates, success-determination obstructions, and same-cell failure matching.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

universe u

/-- A fixed history field for a v13 prefix.  Unlike
`V13ConcretePrefixInstantiation`, this is meant to be supplied by the
manuscript's actual switched-history construction, not existentially chosen
after the fact. -/
structure V13HistoryField (Ω : Type u) where
  Cell : Type u
  [fintypeCell : Fintype Cell]
  [decidableEqCell : DecidableEq Cell]
  cellOf : Ω → Cell

attribute [instance] V13HistoryField.fintypeCell
attribute [instance] V13HistoryField.decidableEqCell

/-- A fixed history field determines the next success event when every field
cell is success-homogeneous: once one point in a cell is successful for the
next switched coordinate, every point in that same cell is also successful. -/
def V13HistoryFieldDeterminesSuccess {Ω : Type u}
    (field : V13HistoryField Ω) (step : V13SwitchedStep Ω) : Prop :=
  ∀ ⦃ω ω' : Ω⦄,
    field.cellOf ω = field.cellOf ω' →
      step.successEvent.pred ω → step.successEvent.pred ω'

/-- Prefix-relative success determination.  This is the relevant obstruction
for conditioned switching histories: a field may reveal the next success event
on the current history support even if it does not reveal it globally. -/
def V13HistoryFieldDeterminesSuccessOn {Ω : Type u}
    (field : V13HistoryField Ω) (hist : List (FiniteEvent Ω))
    (step : V13SwitchedStep Ω) : Prop :=
  ∀ ⦃ω ω' : Ω⦄,
    allEvents hist ω →
      allEvents hist ω' →
        field.cellOf ω = field.cellOf ω' →
          step.successEvent.pred ω → step.successEvent.pred ω'

/-- Global success determination implies prefix-relative success determination
on every current history support. -/
theorem v13HistoryFieldDeterminesSuccessOn_of_determinesSuccess {Ω : Type u}
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccess field step) :
    V13HistoryFieldDeterminesSuccessOn field hist step := by
  intro ω ω' _ _ hcell hsucc
  exact hdet hcell hsucc

/-- The fixed field that reveals exactly whether the next v13 switched step is
successful.  A genuine v13 history field cannot behave this way on a
positive-mass prefix while also satisfying the cellwise half-success
certificate below. -/
def v13SuccessHistoryField {Ω : Type u} (step : V13SwitchedStep Ω) :
    V13HistoryField Ω where
  Cell := ULift.{u} Bool
  cellOf := fun ω => ULift.up (decide (step.successEvent.pred ω))

/-- The success-revealing history field determines the next success event. -/
theorem v13SuccessHistoryField_determinesSuccess {Ω : Type u}
    (step : V13SwitchedStep Ω) :
    V13HistoryFieldDeterminesSuccess (v13SuccessHistoryField step) step := by
  intro ω ω' hcell hsucc
  have hbool :
      decide (step.successEvent.pred ω) =
        decide (step.successEvent.pred ω') := congrArg ULift.down hcell
  rw [decide_eq_true hsucc] at hbool
  exact of_decide_eq_true hbool.symm

/-- In the success-revealing field, the `true` cell is exactly the next success
event. -/
theorem v13SuccessHistoryField_prefix_true_count
    {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω) :
    v13ConcretePrefixCount (Ω := Ω) hist
        (v13SuccessHistoryField step).cellOf (ULift.up true) =
      finiteHistoryCount Ω (hist ++ [step.successEvent]) := by
  rw [v13ConcretePrefixCount,
    finiteHistoryCount_append_singleton (Ω := Ω) hist step.successEvent]
  exact finiteEventCount_congr (Ω := Ω)
    (E := fun ω =>
      allEvents hist ω ∧ (v13SuccessHistoryField step).cellOf ω = ULift.up true)
    (F := fun ω => allEvents hist ω ∧ step.successEvent.pred ω)
    (by
      intro ω
      simp [v13SuccessHistoryField])

/-- Once the fixed field has already selected the next-success cell, intersecting
that cell with the next success event does not reduce it. -/
theorem v13SuccessHistoryField_success_true_count_eq_prefix_true_count
    {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω) :
    v13ConcreteSuccessCount (Ω := Ω) hist step
        (v13SuccessHistoryField step).cellOf (ULift.up true) =
      v13ConcretePrefixCount (Ω := Ω) hist
        (v13SuccessHistoryField step).cellOf (ULift.up true) := by
  rw [v13ConcreteSuccessCount, v13ConcretePrefixCount]
  exact finiteEventCount_congr (Ω := Ω)
    (E := fun ω =>
      allEvents hist ω ∧
        (v13SuccessHistoryField step).cellOf ω = ULift.up true ∧
          step.successEvent.pred ω)
    (F := fun ω =>
      allEvents hist ω ∧ (v13SuccessHistoryField step).cellOf ω = ULift.up true)
    (by
      intro ω
      simp [v13SuccessHistoryField])

end Mettapedia.Computability.PNP
