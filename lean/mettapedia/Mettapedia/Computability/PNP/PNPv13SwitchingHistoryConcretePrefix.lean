import Mettapedia.Computability.PNP.PNPv13SwitchingHistoryDeterminationObstructions

/-!
# PNP v13 switching: concrete-prefix consequences

Consequences connecting fixed-field certificates back to the existential concrete-cell certificate and singleton/positive-success blockers.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

universe u

def v13ConcretePrefixInstantiation_of_fieldPrefixInstantiation
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (cert : V13FieldPrefixInstantiation field hist step) :
    V13ConcretePrefixInstantiation hist step := by
  letI : Fintype field.Cell := field.fintypeCell
  letI : DecidableEq field.Cell := field.decidableEqCell
  exact
    { Cell := field.Cell
      cellOf := field.cellOf
      prefix_decomp := cert.prefix_decomp
      success_decomp := cert.success_decomp
      cell_half := cert.cell_half }

/-- A fixed-field v13 certificate is sufficient for the generic prefix
half-step. -/
theorem prefixHalfStep_of_v13FieldPrefixInstantiation
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (cert : V13FieldPrefixInstantiation field hist step) :
    PrefixHalfStep hist step.successEvent := by
  exact prefixHalfStep_of_v13ConcretePrefixInstantiation
    (v13ConcretePrefixInstantiation_of_fieldPrefixInstantiation cert)

/-- A fixed-field prefix certificate is blocked by one cell whose conditional
success count exceeds half of the cell's prefix count. -/
theorem not_v13FieldPrefixInstantiation_of_cell_half_violation
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} (cell : field.Cell)
    (hbad :
      ¬ 2 * v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell ≤
        v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  intro cert
  exact hbad (cert.cell_half cell)

/-- In any fixed-field prefix certificate, every cell containing a successful
point must also contain at least one unsuccessful prefix point. -/
theorem v13FieldPrefixInstantiation_successCount_lt_prefixCount_of_success_pos
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (cert : V13FieldPrefixInstantiation field hist step)
    (cell : field.Cell)
    (hpos :
      0 < v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell) :
    v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell <
      v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell := by
  have hlt :
      1 * v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell <
        2 * v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell :=
    Nat.mul_lt_mul_of_pos_right (by decide) hpos
  exact lt_of_lt_of_le (by simpa using hlt) (cert.cell_half cell)

/-- A one-success cell in a fixed-field prefix certificate must contain at
least two prefix points.  Thus singleton successful cells are forbidden. -/
theorem v13FieldPrefixInstantiation_two_le_prefixCount_of_successCount_eq_one
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (cert : V13FieldPrefixInstantiation field hist step)
    (cell : field.Cell)
    (hsucc :
      v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell = 1) :
    2 ≤ v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell := by
  simpa [hsucc] using cert.cell_half cell

/-- A fixed-field prefix certificate is impossible when some positive-mass cell
is entirely successful for the next switched coordinate. -/
theorem not_v13FieldPrefixInstantiation_of_cell_success_eq_prefix
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} (cell : field.Cell)
    (hpos :
      0 < v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell)
    (hall :
      v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell =
        v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact not_v13FieldPrefixInstantiation_of_cell_half_violation cell (by
    rw [hall]
    exact not_le_of_gt (by
      have hlt :
          1 * v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell <
            2 * v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell :=
        Nat.mul_lt_mul_of_pos_right (by decide) hpos
      simpa using hlt))

/-- A fixed-field prefix certificate is impossible when a cell has positive
success mass and that success mass exhausts the cell. -/
theorem not_v13FieldPrefixInstantiation_of_positive_success_eq_prefix
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} (cell : field.Cell)
    (hpos :
      0 < v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell)
    (hall :
      v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell =
        v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact not_v13FieldPrefixInstantiation_of_cell_success_eq_prefix cell
    (by
      rw [← hall]
      exact hpos)
    hall

/-- A singleton cell that is successful for the next switched coordinate
cannot satisfy the fixed-field half-success certificate. -/
theorem not_v13FieldPrefixInstantiation_of_singleton_success_cell
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} (cell : field.Cell)
    (hprefix :
      v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell = 1)
    (hsuccess :
      v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell = 1) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact not_v13FieldPrefixInstantiation_of_positive_success_eq_prefix cell
    (by
      rw [hsuccess]
      decide)
    (by
      rw [hsuccess, hprefix])

/-- If the supplied fixed history field reveals the next success event, then a
positive-mass next-success prefix blocks the v13 cellwise half-success
certificate. -/
theorem not_v13FieldPrefixInstantiation_successHistoryField_of_positive_success
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13FieldPrefixInstantiation (v13SuccessHistoryField step) hist step := by
  exact not_v13FieldPrefixInstantiation_of_cell_success_eq_prefix (ULift.up true)
    (by
      rw [v13SuccessHistoryField_prefix_true_count]
      exact hpos)
    (v13SuccessHistoryField_success_true_count_eq_prefix_true_count hist step)

end Mettapedia.Computability.PNP
