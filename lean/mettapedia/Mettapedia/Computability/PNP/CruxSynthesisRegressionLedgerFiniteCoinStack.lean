import Mettapedia.Computability.PNP.CruxFiniteCoinSubrepairLedger
import Mettapedia.Computability.PNP.CruxLocalPacketStatus

/-!
# Regression checks for finite-coin PNP crux ledger surfaces

Finite-coin subrepair and broad uncovered-class ledger regressions extracted
from the historical `CruxSynthesisRegressionLedger` module.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem current_pnp_finite_coin_covered_subrepairs_exact_regression
    (repair : PNPFiniteCoinSubrepairClass) :
    repair ∈ currentPNPFiniteCoinCoveredSubrepairs := by
  exact currentPNPFiniteCoinCoveredSubrepairs_exact repair

theorem finite_coin_stack_uncovered_broad_classes_exact_regression
    (repair : PNPRepairClass) :
    repair ∈ finiteCoinStackUncoveredBroadRepairClasses ↔
      repair ∈ currentPNPUncoveredRepairClasses := by
  exact finiteCoinStackUncoveredBroadRepairClasses_exact repair

end Mettapedia.Computability.PNP.CruxSynthesisRegression
