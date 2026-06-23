import Mettapedia.Computability.PNP.PNPv13BoolPairCore

/-!
# PNP v13 Bool-pair: prefix obstructions

Concrete counts and one-step fixed-field blockers separating generic half-steps from fixed-field certificates.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

universe u

/-- The repeated-step success event has numerator `2` over the four-point
Boolean square. -/
theorem v13BoolPairRepeatedStep_success_count :
    finiteHistoryCount (Bool × Bool) [v13BoolPairRepeatedStep.successEvent] = 2 := by
  decide

/-- On the diagonal prefix, first-coordinate success has positive mass. -/
theorem v13BoolPairDiagonal_repeatedStep_success_count :
    finiteHistoryCount (Bool × Bool)
      ([v13BoolPairDiagonalEvent] ++ [v13BoolPairRepeatedStep.successEvent]) = 1 := by
  decide

/-- The first success event is globally half-admissible from the empty history. -/
theorem prefixHalfStep_v13BoolPairRepeatedStep_empty :
    PrefixHalfStep ([] : List (FiniteEvent (Bool × Bool)))
      v13BoolPairRepeatedStep.successEvent := by
  rw [PrefixHalfStep]
  decide

/-- The one-cell field certifies the first repeated-coordinate step from the
empty history: the first-coordinate success event has exactly half the four
Boolean-square points. -/
theorem v13FieldPrefixInstantiation_unitField_empty :
    V13FieldPrefixInstantiation v13BoolPairUnitField
      ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep := by
  refine v13FieldPrefixInstantiation_of_cellHalf ?_
  intro cell
  cases cell
  decide

/-- In the first-coordinate field, the `true` cell has two points before the
step. -/
theorem v13BoolPairFirstCoordinateField_prefix_true_count :
    v13ConcretePrefixCount (Ω := Bool × Bool)
      ([] : List (FiniteEvent (Bool × Bool)))
      v13BoolPairFirstCoordinateField.cellOf true = 2 := by
  decide

/-- In the first-coordinate field, the `true` cell is entirely successful for
the first-coordinate exact-success event. -/
theorem v13BoolPairFirstCoordinateField_success_true_count :
    v13ConcreteSuccessCount (Ω := Bool × Bool)
      ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep
      v13BoolPairFirstCoordinateField.cellOf true = 2 := by
  decide

/-- Global half-success does not imply the fixed-field cellwise half-success
obligation.  The field that reveals the successful first coordinate has a
`true` cell where success has conditional mass `1`. -/
theorem not_v13FieldPrefixInstantiation_firstCoordinateField_empty :
    ¬ V13FieldPrefixInstantiation v13BoolPairFirstCoordinateField
      ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep := by
  exact not_v13FieldPrefixInstantiation_of_cell_half_violation true (by
    rw [v13BoolPairFirstCoordinateField_prefix_true_count,
      v13BoolPairFirstCoordinateField_success_true_count]
    decide)

/-- The same first-coordinate field failure follows from the general theorem:
a success-determining field with positive next-success mass cannot satisfy a
fixed-field certificate. -/
theorem not_v13FieldPrefixInstantiation_firstCoordinateField_empty_by_determined_success :
    ¬ V13FieldPrefixInstantiation v13BoolPairFirstCoordinateField
      ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep := by
  exact
    not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccess_positive_success
      v13BoolPairFirstCoordinateField_determinesSuccess (by decide)

/-- Prefix-relative success determination is enough to block a fixed-field
certificate even when the field is not globally success-determining. -/
theorem not_v13FieldPrefixInstantiation_secondCoordinateField_diagonal_by_determines_success_on :
    ¬ V13FieldPrefixInstantiation v13BoolPairSecondCoordinateField
      [v13BoolPairDiagonalEvent] v13BoolPairRepeatedStep := by
  exact
    not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccessOn_positive_success
      v13BoolPairSecondCoordinateField_determinesSuccessOn_diagonal
      (by
        rw [v13BoolPairDiagonal_repeatedStep_success_count]
        decide)

/-- The same diagonal-prefix obstruction blocks the operational same-cell
success-to-failure matching formulation. -/
theorem not_v13FieldFailureMatching_secondCoordinateField_diagonal_by_determines_success_on :
    ¬ V13FieldFailureMatching v13BoolPairSecondCoordinateField
      [v13BoolPairDiagonalEvent] v13BoolPairRepeatedStep := by
  exact
    not_v13FieldFailureMatching_of_fieldDeterminesSuccessOn_positive_success
      v13BoolPairSecondCoordinateField_determinesSuccessOn_diagonal
      (by
        rw [v13BoolPairDiagonal_repeatedStep_success_count]
        decide)

/-- A compact separation theorem: the generic prefix half-step can hold while
the natural fixed first-coordinate history field fails the v13 cellwise
instantiation. -/
theorem prefixHalfStep_without_firstCoordinateFieldInstantiation :
    PrefixHalfStep ([] : List (FiniteEvent (Bool × Bool)))
        v13BoolPairRepeatedStep.successEvent ∧
      ¬ V13FieldPrefixInstantiation v13BoolPairFirstCoordinateField
        ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep := by
  exact ⟨prefixHalfStep_v13BoolPairRepeatedStep_empty,
    not_v13FieldPrefixInstantiation_firstCoordinateField_empty⟩

/-- The fixed first-coordinate one-step switching claim is blocked already at
its first field certificate. -/
theorem not_v13FieldSwitchingInstantiated_firstCoordinateOneStep :
    ¬ V13FieldSwitchingInstantiated
      [v13BoolPairFirstCoordinateFieldedStep] := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_cons_of_not_fieldPrefixInstantiation
      not_v13FieldPrefixInstantiation_firstCoordinateField_empty

/-- Even after a valid one-cell certificate for the first cut, using the
first-coordinate field for the repeated second cut is blocked because that
later field determines the next success event on a positive-mass prefix. -/
theorem unitField_first_step_then_firstCoordinateField_second_blocked :
    V13FieldPrefixInstantiation v13BoolPairUnitField
        ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep ∧
      ¬ V13FieldSwitchingInstantiated
        [v13BoolPairUnitFieldedStep, v13BoolPairFirstCoordinateFieldedStep] := by
  refine ⟨v13FieldPrefixInstantiation_unitField_empty, ?_⟩
  exact
    not_v13FieldSwitchingInstantiatedFrom_append_cons_of_fieldDeterminesSuccess_positive_success
      (hist := ([] : List (FiniteEvent (Bool × Bool))))
      (pre := [v13BoolPairUnitFieldedStep])
      (item := v13BoolPairFirstCoordinateFieldedStep)
      (suffix := [])
      v13BoolPairFirstCoordinateField_determinesSuccess
      (by
        decide)

end Mettapedia.Computability.PNP
