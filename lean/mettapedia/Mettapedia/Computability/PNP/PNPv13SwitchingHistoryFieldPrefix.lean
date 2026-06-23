import Mettapedia.Computability.PNP.PNPv13SwitchingHistoryFieldsCore

/-!
# PNP v13 switching: fixed-field prefix certificates

Cellwise half-success certificates for a supplied fixed history field, before same-cell failure matching is introduced.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

universe u

/-- Cellwise half-success certificate for a fixed externally supplied history
field.  This is the non-vacuous v13 instantiation target: the field is a
parameter, not part of an existential certificate. -/
structure V13FieldPrefixInstantiation {Ω : Type u} [Fintype Ω]
    (field : V13HistoryField Ω) (hist : List (FiniteEvent Ω))
    (step : V13SwitchedStep Ω) where
  prefix_decomp :
    finiteHistoryCount Ω hist =
      Finset.univ.sum (v13ConcretePrefixCount (Ω := Ω) hist field.cellOf)
  success_decomp :
    finiteHistoryCount Ω (hist ++ [step.successEvent]) =
      Finset.univ.sum (v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf)
  cell_half : ∀ cell,
    2 * v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell ≤
      v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell

/-- Build a fixed-field prefix certificate from the cellwise half-success
inequality.  The decomposition obligations are automatic finite partition
identities for the supplied field. -/
def v13FieldPrefixInstantiation_of_cellHalf
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hhalf : ∀ cell,
      2 * v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell ≤
        v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell) :
    V13FieldPrefixInstantiation field hist step where
  prefix_decomp := v13ConcretePrefixCount_decomp hist field.cellOf
  success_decomp := v13ConcreteSuccessCount_decomp hist step field.cellOf
  cell_half := hhalf

/-- For a fixed supplied history field, the v13 prefix certificate is exactly
the cellwise half-success inequality.  The decomposition fields in the record
are audit data, not additional mathematical obligations. -/
theorem v13FieldPrefixInstantiation_iff_cellHalf
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} :
    V13FieldPrefixInstantiation field hist step ↔
      ∀ cell,
        2 * v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell ≤
          v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell := by
  constructor
  · intro cert
    exact cert.cell_half
  · intro hhalf
    exact v13FieldPrefixInstantiation_of_cellHalf hhalf

/-- Equivalently, the exact missing fixed-field theorem is a per-cell balance:
every successful prefix point in a supplied history atom must be matched by at
least one unsuccessful prefix point in the same atom. -/
theorem v13FieldPrefixInstantiation_iff_success_le_failure
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} :
    V13FieldPrefixInstantiation field hist step ↔
      ∀ cell,
        v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell ≤
          v13ConcreteFailureCount (Ω := Ω) hist step field.cellOf cell := by
  rw [v13FieldPrefixInstantiation_iff_cellHalf]
  constructor
  · intro h cell
    exact (v13ConcreteCellHalf_iff_success_le_failure
      (Ω := Ω) hist step field.cellOf cell).mp (h cell)
  · intro h cell
    exact (v13ConcreteCellHalf_iff_success_le_failure
      (Ω := Ω) hist step field.cellOf cell).mpr (h cell)

end Mettapedia.Computability.PNP
