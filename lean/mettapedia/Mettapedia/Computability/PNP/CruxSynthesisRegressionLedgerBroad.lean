import Mettapedia.Computability.PNP.CruxLocalPacketStatus
import Mettapedia.Computability.PNP.CruxLocalRouteCoverageAtomicBudget
import Mettapedia.Computability.PNP.CruxLocalRouteCoverageDecoder
import Mettapedia.Computability.PNP.CruxLocalRouteCoverageEvidenceTrace
import Mettapedia.Computability.PNP.CruxLocalRouteCoverageFielded
import Mettapedia.Computability.PNP.CruxLocalRouteCoverageFiniteEnvelope

/-!
# Regression checks for broad PNP crux ledger surfaces

Broad current-packet list and short-global-decoder ledger regressions extracted
from the historical `CruxSynthesisRegressionLedger` module.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem current_pnp_covered_repair_classes_exact_regression
    (repair : PNPRepairClass) :
    repair ∈ currentPNPCoveredRepairClasses ↔
      currentPNPLocalCruxPacket.covers repair := by
  exact currentPNPCoveredRepairClasses_exact repair

theorem current_pnp_uncovered_repair_classes_exact_regression
    (repair : PNPRepairClass) :
    repair ∈ currentPNPUncoveredRepairClasses ↔
      ¬ currentPNPLocalCruxPacket.covers repair := by
  exact currentPNPUncoveredRepairClasses_exact repair

theorem short_global_decoder_supported_sat_search_equiv_single_message_regression
    {Public : Type u} {Var : Public → Type v}
    {Witness : Public → Type w} {Message : Type z}
    (D : ManuscriptCNFReadoutData Public Var Witness Message)
    (hsat : D.SupportedCNFSatisfiable)
    (hcomplete : D.CNFExtractionComplete) :
    D.SupportedArbitraryOutputSATSearchCorrect ↔ D.SingleMessagePromise := by
  exact
    shortGlobalDecoderCoverage_anchor_supported_sat_search_equiv_singleMessagePromise
      D hsat hcomplete

theorem short_global_decoder_incomplete_extraction_countermodel_regression :
    unrepresentedOneVarManuscriptCNFReadoutData.SupportedArbitraryOutputSATSearchCorrect ∧
      ¬ unrepresentedOneVarManuscriptCNFReadoutData.SingleMessagePromise ∧
      ¬ unrepresentedOneVarManuscriptCNFReadoutData.CNFExtractionComplete := by
  exact shortGlobalDecoderCoverage_anchor_incomplete_extraction_countermodel

end Mettapedia.Computability.PNP.CruxSynthesisRegression
