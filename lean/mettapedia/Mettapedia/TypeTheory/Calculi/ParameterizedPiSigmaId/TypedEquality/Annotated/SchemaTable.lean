import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.SchemaTableConversionCode
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Schemas

/-!
# Finite schema selections in the existing annotation interface

The selected table keeps its original addresses. A finite first-order/linearity
check discharges the existing annotation-lifting theorem's syntactic condition.
It is not a typing, normalization or computational-admission check.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality.Annotated.SchemaTable

open AlgebraicSchema

variable {Head : Type}

def linearCheck (table : AlgebraicSchema.SchemaTable Head)
    (enabled : Fin table.length → Bool) : Bool :=
  (List.finRange table.length).all fun index =>
    !enabled index || firstOrderLinear (table.get index).2.1

theorem linearCheck_sound (table : AlgebraicSchema.SchemaTable Head)
    (enabled : Fin table.length → Bool) (accepted : linearCheck table enabled = true) :
    FirstOrderFamily (SchemaTableConversionCode.selectedFamily table enabled) := by
  intro arity left right source
  obtain ⟨index, permitted, row⟩ := source
  have checked := List.all_eq_true.mp accepted index (List.mem_finRange index)
  simp only [permitted, Bool.not_true, Bool.false_or] at checked
  have facts := firstOrderLinear_spec checked
  rw [row] at facts
  exact facts

/-- Every raw root at an annotated input lifts when the actual selected
schemas meet the existing first-order/linearity condition. -/
theorem root_lift {R : Rules Head} (table : AlgebraicSchema.SchemaTable Head)
    (enabled : Fin table.length → Bool)
    (present : Presents R.computation (SchemaTableConversionCode.selectedFamily table enabled))
    (accepted : linearCheck table enabled = true) {n : Nat} {left : CTm Head n}
    {right : Tm Head n} (step : R.computation.step left.erase right) :
    ∃ result, (ChurchRules.ofSchemas R
      (SchemaTableConversionCode.selectedFamily table enabled) present).computation.step left result ∧
      result.erase = right :=
  ChurchRules.ofSchemas_lift _ present (linearCheck_sound table enabled accepted) step

end TypedEquality.Annotated.SchemaTable
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
