import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.EquationAdmission
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.ExecutableEvaluationControls

/-! # Positive and separating controls for computed equation admission -/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace EquationAdmissionControls

open TypedEquality.Normalization
open ExecutableCheckingControls (level num zero numeral copiedByRecursor)

def betaEquation : EquationAdmission.Equation Tower.Head :=
  ⟨1, .snoc .nil num, .app (.lam (.var 0)) (.var 0), .var 0, num⟩

def recursorEquation : EquationAdmission.Equation Tower.Head :=
  ⟨0, .nil, copiedByRecursor 2, numeral 2, num⟩

def wrongEquation : EquationAdmission.Equation Tower.Head :=
  { recursorEquation with right := zero }

def check (fuel : Nat) (equations : List (EquationAdmission.Equation Tower.Head)) : Bool :=
  EquationAdmission.check ExecutableEvaluationControls.rules
    (ExecutableTowerNumbers.choices level) (ExecutableTowerNumbers.fullReducer level)
    fuel equations

theorem open_and_closed_equations : check 60 [betaEquation, recursorEquation] = true := by
  decide +kernel

theorem every_equation_required : check 60 [betaEquation, wrongEquation] = false := by
  decide +kernel

theorem repeated_occurrences_checked : check 60 [betaEquation, betaEquation] = true := by
  decide +kernel

theorem wrong_displayed_type :
    check 60 [{ recursorEquation with type := .head (.sort (.const 0)) }] = false := by
  decide +kernel

theorem zero_fuel_cannot_admit : check 0 [betaEquation] = false := by
  decide +kernel

end EquationAdmissionControls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
