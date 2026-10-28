import Mettapedia.Computability.PNP.PNPv13FiniteGibbsDobrushinCanaries

/-!
# Regression checks for finite Gibbs/Dobrushin mixing canaries
-/

namespace Mettapedia.Computability.PNP.PNPv13FiniteGibbsDobrushinCanariesRegression

open Mettapedia.Computability.PNP

theorem strict_contraction_positive_regression :
    finiteGibbsDobrushinStrictContractionAudit.rowSums = [25, 35] ∧
      finiteGibbsDobrushinStrictContractionAudit.maxQSSMConstantScaled = 35 ∧
      finiteGibbsDobrushinStrictContractionAudit.strictMaxRowContractionClears = true ∧
      finiteGibbsDobrushinStrictContractionAudit.boundaryContractionMargin? =
        some 65 ∧
      finiteGibbsDobrushinStrictContractionAudit.sampledRowsStrictBelow = true := by
  exact finiteGibbsDobrushinStrictContraction_lab_positive_canary

theorem average_only_negative_regression :
    finiteGibbsDobrushinAverageOnlyAudit.averageRowMassClears = true ∧
      finiteGibbsDobrushinAverageOnlyAudit.maxQSSMConstantScaled = 150 ∧
      finiteGibbsDobrushinAverageOnlyAudit.strictMaxRowContractionClears = false ∧
      finiteGibbsDobrushinAverageOnlyAudit.boundaryContractionMargin? = none := by
  exact finiteGibbsDobrushinAverageOnly_negative_canary

theorem equality_negative_regression :
    finiteGibbsDobrushinEqualityAudit.nonStrictMaxRowBoundClears = true ∧
      finiteGibbsDobrushinEqualityAudit.maxQSSMConstantScaled = 100 ∧
      finiteGibbsDobrushinEqualityAudit.strictMaxRowContractionClears = false ∧
      finiteGibbsDobrushinEqualityAudit.boundaryContractionMargin? = none := by
  exact finiteGibbsDobrushinEquality_negative_canary

theorem sampled_rows_negative_regression :
    finiteGibbsDobrushinSampledRowsAudit.sampledRowsStrictBelow = true ∧
      finiteGibbsDobrushinSampledRowsAudit.rowViolatesAt 2 = true ∧
      finiteGibbsDobrushinSampledRowsAudit.maxQSSMConstantScaled = 150 ∧
      finiteGibbsDobrushinSampledRowsAudit.strictMaxRowContractionClears = false := by
  exact finiteGibbsDobrushinSampledRows_negative_canary

theorem finite_gibbs_dobrushin_guardrails_regression :
    finiteGibbsDobrushinStrictContractionAudit.strictMaxRowContractionClears = true ∧
      finiteGibbsDobrushinAverageOnlyAudit.averageRowMassClears = true ∧
      finiteGibbsDobrushinAverageOnlyAudit.strictMaxRowContractionClears = false ∧
      finiteGibbsDobrushinEqualityAudit.nonStrictMaxRowBoundClears = true ∧
      finiteGibbsDobrushinEqualityAudit.strictMaxRowContractionClears = false ∧
      finiteGibbsDobrushinSampledRowsAudit.sampledRowsStrictBelow = true ∧
      finiteGibbsDobrushinSampledRowsAudit.strictMaxRowContractionClears = false := by
  exact finiteGibbsDobrushinCanaries_guardrails

end Mettapedia.Computability.PNP.PNPv13FiniteGibbsDobrushinCanariesRegression
