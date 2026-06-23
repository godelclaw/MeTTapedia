import Mettapedia.Computability.PNP.CruxResidualSideInformationCoverageV13CollisionMass
import Mettapedia.Computability.PNP.CruxResidualSideInformationCoverageV13ExactPostSwitch
import Mettapedia.Computability.PNP.CruxResidualSideInformationCoverageV13AdvantageConsequences
import Mettapedia.Computability.PNP.CruxResidualSideInformationCoverageV13Counterexample

/-!
# PNP residual-side-information V13 subcoverage package

This compatibility module keeps the historical
`V13ResidualSideInformationSubcoverage` surface while its collision/mass,
exact post-switch, advantage-consequence, and concrete counterexample layers
live in focused sibling modules.
-/

namespace Mettapedia.Computability.PNP

universe u v w

/-- The V13 residual-side-information subledger is theorem-backed by four
focused layers: collision/mass facts, exact post-switch active-orbit witnesses,
advantage consequences, and the balanced four-point counterexample. -/
def V13ResidualSideInformationSubcoverage : Prop :=
  V13ResidualSideInformationCollisionMassSubcoverage.{u, v, w} ∧
    V13ResidualSideInformationExactPostSwitchSubcoverage.{u} ∧
      V13ResidualSideInformationAdvantageConsequenceSubcoverage.{u, v, w} ∧
        V13ResidualSideInformationCounterexampleSubcoverage

@[simp] theorem v13ResidualSideInformationSubcoverage :
    V13ResidualSideInformationSubcoverage := by
  exact
    ⟨v13ResidualSideInformationCollisionMassSubcoverage,
      v13ResidualSideInformationExactPostSwitchSubcoverage,
      v13ResidualSideInformationAdvantageConsequenceSubcoverage,
      v13ResidualSideInformationCounterexampleSubcoverage⟩

end Mettapedia.Computability.PNP
