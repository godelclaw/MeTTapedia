import Mettapedia.Computability.PNP.PNPv13SwitchingFailureLocalization

/-!
# PNP v13 Bool-pair: core examples

Boolean-square switched steps, history fields, and success-determination facts used by the counterexample cluster.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

universe u

/-- A concrete repeated-coordinate switched step on the Boolean square.  Exact
success is the first-coordinate event. -/
def v13BoolPairRepeatedStep : V13SwitchedStep (Bool × Bool) where
  coordinate := 0
  observerBit := fun ω => ω.1
  targetBit := fun _ => true

/-- The fixed field that reveals the same first coordinate used by the success
event. -/
def v13BoolPairFirstCoordinateField : V13HistoryField (Bool × Bool) where
  Cell := Bool
  cellOf := fun ω => ω.1

/-- A fixed field that reveals the second coordinate.  It does not globally
determine first-coordinate success, but it does after conditioning on the
diagonal history event below. -/
def v13BoolPairSecondCoordinateField : V13HistoryField (Bool × Bool) where
  Cell := Bool
  cellOf := fun ω => ω.2

/-- The diagonal history event `first = second` on the Boolean square. -/
def v13BoolPairDiagonalEvent : FiniteEvent (Bool × Bool) where
  pred := fun ω => ω.1 = ω.2
  decidablePred := fun _ => inferInstance

/-- The first-coordinate field determines exact success for the repeated
first-coordinate switched step. -/
theorem v13BoolPairFirstCoordinateField_determinesSuccess :
    V13HistoryFieldDeterminesSuccess v13BoolPairFirstCoordinateField
      v13BoolPairRepeatedStep := by
  intro ω ω' hcell hsucc
  cases ω with
  | mk a b =>
      cases ω' with
      | mk a' b' =>
          cases a <;> cases a' <;> cases b <;> cases b' <;>
            simp [v13BoolPairFirstCoordinateField, v13BoolPairRepeatedStep,
              V13SwitchedStep.successEvent] at hcell hsucc ⊢

/-- The second-coordinate field does not globally determine first-coordinate
success: outside the diagonal, points with the same second coordinate can have
different first-coordinate success values. -/
theorem not_v13BoolPairSecondCoordinateField_determinesSuccess :
    ¬ V13HistoryFieldDeterminesSuccess v13BoolPairSecondCoordinateField
      v13BoolPairRepeatedStep := by
  intro hdet
  have htarget :
      v13BoolPairRepeatedStep.successEvent.pred (false, true) :=
    hdet (ω := (true, true)) (ω' := (false, true)) rfl (by decide)
  simp [v13BoolPairRepeatedStep, V13SwitchedStep.successEvent] at htarget

/-- After conditioning on the diagonal history event, the second-coordinate
field does determine first-coordinate success.  This is the prefix-relative
case that a purely global blocker would miss. -/
theorem v13BoolPairSecondCoordinateField_determinesSuccessOn_diagonal :
    V13HistoryFieldDeterminesSuccessOn v13BoolPairSecondCoordinateField
      [v13BoolPairDiagonalEvent] v13BoolPairRepeatedStep := by
  intro ω ω' hω hω' hcell hsucc
  cases ω with
  | mk a b =>
      cases ω' with
      | mk a' b' =>
          cases a <;> cases a' <;> cases b <;> cases b' <;>
            simp [v13BoolPairSecondCoordinateField, v13BoolPairRepeatedStep,
              v13BoolPairDiagonalEvent, V13SwitchedStep.successEvent,
              allEvents] at hω hω' hcell hsucc ⊢

/-- The first-coordinate switched step paired with the fixed field that reveals
that same coordinate. -/
def v13BoolPairFirstCoordinateFieldedStep : V13FieldedStep (Bool × Bool) where
  field := v13BoolPairFirstCoordinateField
  step := v13BoolPairRepeatedStep

/-- The one-cell field on the Boolean square.  It is the honest finite field
that certifies the first global half-success cut for the repeated-coordinate
test case. -/
def v13BoolPairUnitField : V13HistoryField (Bool × Bool) where
  Cell := PUnit
  cellOf := fun _ => PUnit.unit

/-- The repeated-coordinate switched step paired with the one-cell field. -/
def v13BoolPairUnitFieldedStep : V13FieldedStep (Bool × Bool) where
  field := v13BoolPairUnitField
  step := v13BoolPairRepeatedStep

end Mettapedia.Computability.PNP
