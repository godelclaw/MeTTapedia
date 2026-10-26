import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableEvaluation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.ExecutableCheckingControls

/-! # Computing and checking proposed readback in the natural-number instance

These controls run the actual finite procedures. They include dependent
results, open contexts, a lying readback, an undeclared source and exhausted
fuel. No source proof or claimed normal form is passed to the evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ExecutableEvaluationControls

open TypedEquality.Normalization
open ExecutableCheckingControls (level num zero succ numeral copiedByRecursor)

abbrev rules := TowerNumbersModel.rules level

def run (readback : ExecutableEvaluation.Readback Tower.Head) (fuel : Nat) {n : Nat}
    (context : Ctx Tower.Head n) (source : Tm Tower.Head n) :=
  ExecutableEvaluation.run rules (ExecutableTowerNumbers.choices level)
    (ExecutableTowerNumbers.fullReducer level) readback fuel context source

def identityRedex {n : Nat} (value : Tm Tower.Head n) : Tm Tower.Head n :=
  .app (.lam (.var 0)) value

/-- Readback may choose another convertible presentation, but must earn it. -/
def betaReadback : ExecutableEvaluation.Readback Tower.Head :=
  fun term => some (identityRedex term)

theorem recursor_returns :
    run (fun term => some term) 60 .nil (copiedByRecursor 2) =
      some (numeral 2, num) := by decide +kernel

theorem alternate_presentation_checked :
    run betaReadback 60 .nil (copiedByRecursor 2) =
      some (identityRedex (numeral 2), num) := by decide +kernel

theorem lying_readback_refused :
    run (fun _ => some zero) 60 .nil (copiedByRecursor 2) = none := by decide +kernel

theorem ill_typed_readback_refused :
    run (fun _ => some num) 60 .nil (copiedByRecursor 2) = none := by decide +kernel

theorem missing_source_refused :
    run (fun term => some term) 60 (.nil : Ctx Tower.Head 0) (.const `missing) = none := by
  decide +kernel

theorem open_context_returns :
    run (fun term => some term) 40 (.snoc .nil num) (identityRedex (.var 0)) =
      some (.var 0, num) := by decide +kernel

theorem dependent_result_returns :
    run (fun term => some term) 60 .nil (.refl (copiedByRecursor 1)) =
      some (.refl (numeral 1), .id num (copiedByRecursor 1) (copiedByRecursor 1)) := by
  decide +kernel

theorem no_readback_no_result :
    run (fun _ => none) 40 .nil (zero : Tm Tower.Head 0) = none := by decide +kernel

theorem exhausted_has_no_partial_value :
    run (fun term => some term) 1 .nil (copiedByRecursor 2) = none := by decide +kernel

/-- Instantiate every admission hypothesis from the constructed number model. -/
theorem returned_equal_source {fuel n : Nat} {context : Ctx Tower.Head n}
    {source value type : Tm Tower.Head n} (readback : ExecutableEvaluation.Readback Tower.Head)
    (returned : run readback fuel context source = some (value, type)) :
    TypedEquality.Typed rules context source type ∧ TypedEquality.Typed rules context value type ∧
      TypedEquality.Equal rules context source value type := by
  exact ExecutableEvaluation.run_sound (S := TowerNumbersModel.setting level (fun _ => 0))
    (TowerNumbersModel.facts level) (TowerNumbersModel.roots level) (TowerNumbersModel.heads level)
    (TowerNumbersModel.algebra level) (ExecutableTowerNumbers.declaredTypesFormed level)
    (ExecutableTowerNumbers.choices level) (ExecutableTowerNumbers.fullReducer level) readback returned

end ExecutableEvaluationControls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
