import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.UniverseProfiles

/-!
# Finite evidence checking for the existing cumulative tower

The selected mathematical profile has the existing natural-number level
expressions, dependent Pi/Sigma/identity syntax, cumulativity and structural
beta conversion. Its authored declaration-root relation is empty; structural
beta steps remain available. Local universe decisions use the existing level
normal-form algorithm, including semantic order under every valuation.

This is an instance of common finite evidence replay, not a new type theory,
a proof-search algorithm, a portable byte protocol or a native C refinement.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tower
namespace Checking

open FormationSensitiveRuleSignature FormationSensitiveChecking

instance : DecidableRel Tower.rules.headEq :=
  fun left right => LevelTower.instDecidableHeadEq left right

abbrev decoder : StructuralConversionCode.RootDecoder Tower.rules.computation :=
  .ofEmpty _ rfl

abbrev interface := FormationSensitiveChecking.interface decoder
abbrev Request (claim : Judgment Tower.Head) := FormationSensitiveChecking.Request decoder claim
abbrev check {claim : Judgment Tower.Head} (request : Request claim) := request.check decoder

/-- Formation-sensitive judgments have exactly finite accepted evidence in
this already admitted cumulative profile. -/
theorem coverage (claim : Judgment Tower.Head) :
    FormationSensitive.Judgment Tower.rules claim.context claim.subject claim.type ↔
      ∃ request : Request claim, check request = true := by
  constructor
  · intro derived
    obtain ⟨context, nodes, root, checked⟩ := (judgment_iff_checked decoder claim).mp derived
    exact ⟨⟨context, nodes, root⟩, checked⟩
  · rintro ⟨request, checked⟩
    exact request.sound decoder checked

end Checking
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tower
