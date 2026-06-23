import Mettapedia.Computability.PNP.CruxResidualSideInformationCoverageCounterexamples
import Mettapedia.Computability.PNP.CruxResidualSideInformationCoverageRepairEquivalences
import Mettapedia.Computability.PNP.CruxResidualSideInformationCoverageExactPostSwitch

/-!
# PNP residual-side-information broad coverage package

This compatibility module keeps the historical `ResidualSideInformationCoverage`
surface while the theorem-backed counterexample, repair-equivalence, and exact
post-switch layers live in focused sibling modules.
-/

namespace Mettapedia.Computability.PNP

/-- The broad residual-side-information repair class is covered by three
focused theorem-backed layers: concrete counterexamples, repair/equivalence
transfers, and exact post-switch active-orbit witnesses. -/
def ResidualSideInformationCoverage : Prop :=
  ResidualSideInformationCounterexampleCoverage ∧
    ResidualSideInformationRepairEquivalenceCoverage ∧
      ResidualSideInformationExactPostSwitchCoverage

@[simp] theorem residualSideInformationCoverage :
    ResidualSideInformationCoverage := by
  exact
    ⟨residualSideInformationCounterexampleCoverage,
      residualSideInformationRepairEquivalenceCoverage,
      residualSideInformationExactPostSwitchCoverage⟩

end Mettapedia.Computability.PNP
