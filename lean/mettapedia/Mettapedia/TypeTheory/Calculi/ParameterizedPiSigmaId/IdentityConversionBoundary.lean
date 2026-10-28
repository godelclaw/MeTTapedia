import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.EmptyRootConversion

/-!
# Distinct variables in empty-root conversion

The existing empty-root Church--Rosser theorem separates distinct variables.
The concrete formed identity-premise example is in Examples.IdentityConversionBoundary.
These generic laws require no particular universe or typing profile.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

namespace EmptyRootConversion

variable {Head : Type} {n : Nat}

theorem variable_has_no_step (rules : Rules Head)
    (empty : rules.computation = RootComputation.empty)
    (index : Fin n) {target : Tm Head n}
    (step : Step rules.headEq (.var index) target rules.computation) : False := by
  cases step with
  | root step => rw [empty] at step; exact step

theorem variable_stepStar (rules : Rules Head)
    (empty : rules.computation = RootComputation.empty)
    (index : Fin n) {target : Tm Head n}
    (steps : ConversionCoherence.StepStar rules (.var index) target) : target = .var index := by
  induction steps with
  | refl => rfl
  | tail _ step ih =>
      exact False.elim (variable_has_no_step rules empty index (by simpa only [ih] using step))

theorem variable_conversion_injective (rules : Rules Head)
    (empty : rules.computation = RootComputation.empty)
    (symmetric : Std.Symm rules.headEq) {first second : Fin n}
    (converted : Conv rules.headEq (.var first) (.var second) rules.computation) : first = second := by
  obtain ⟨common, left, right⟩ := churchRosser rules empty symmetric converted
  have one := variable_stepStar rules empty first left
  have two := variable_stepStar rules empty second right
  exact Tm.var.inj (one.symm.trans two)

end EmptyRootConversion

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
