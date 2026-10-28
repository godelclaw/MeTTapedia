import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IdentityConversionBoundary
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeConversion

/-! # A formed identity premise without judgmental equality reflection -/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

namespace IdentityConversionBoundary

open FormationSensitive
open Mettapedia.TypeTheory.UniverseLevel

abbrev level : LevelExpr Nat := .const 0

def carrierContext : Tower.Ctx 1 := .snoc .nil (.head (.sort level))
def pointsContext : Tower.Ctx 3 := .snoc (.snoc carrierContext (.var 0)) (.var 1)
def context : Tower.Ctx 4 := .snoc pointsContext (.id (.var 2) (.var 1) (.var 0))

theorem carrier_context_formed : ContextFormation Tower.rules carrierContext :=
  .snoc .nil (.headType (.sort level)) (.sort _)

theorem points_context_formed : ContextFormation Tower.rules pointsContext :=
  .snoc (.snoc carrier_context_formed (.var 0) (.sort level)) (.var 1) (.sort level)

theorem context_formed : ContextFormation Tower.rules context :=
  .snoc points_context_formed (.idForm (.var 2) (.sort level) (.var 1) (.var 0)) (.sort level)

/-- The identity is an actual typed variable in a fully formed telescope. -/
theorem identity_premise :
    Judgment Tower.rules context (.var 0) (.id (.var 3) (.var 2) (.var 1)) :=
  ⟨context_formed, .var 0⟩

theorem endpoints_not_convertible :
    ¬Conv Tower.rules.headEq (.var 2 : Tower.Tm 4) (.var 1) Tower.rules.computation := by
  intro converted
  have same := EmptyRootConversion.variable_conversion_injective
    Tower.rules rfl LevelTower.headEq_symmetric converted
  have indices := congrArg Fin.val same
  contradiction

theorem identity_without_judgmental_conversion :
    Judgment Tower.rules context (.var 0) (.id (.var 3) (.var 2) (.var 1)) ∧
      ¬Conv Tower.rules.headEq (.var 2 : Tower.Tm 4) (.var 1) Tower.rules.computation :=
  ⟨identity_premise, endpoints_not_convertible⟩

#print axioms EmptyRootConversion.variable_conversion_injective
#print axioms identity_without_judgmental_conversion

end IdentityConversionBoundary
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
