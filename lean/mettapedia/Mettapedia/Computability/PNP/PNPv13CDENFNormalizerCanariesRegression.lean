import Mettapedia.Computability.PNP.PNPv13CDENFNormalizerCanaries

/-!
# Regression checks for PNP v13 CD-ENF normalizer canaries
-/

namespace Mettapedia.Computability.PNP.PNPv13CDENFNormalizerCanariesRegression

open Mettapedia.Computability.PNP

theorem cdenf_normalizer_positive_canary_regression :
    CDENFAllTargetRelevantLeavesInAllowedClasses cdenfPositiveCanaryLeaves ∧
      CDENFResidualReports cdenfPositiveCanaryLeaves = [] := by
  exact cdenfNormalizer_lab_positive_canary

theorem cdenf_normalizer_negative_canary_regression :
    CDENFResidualReports cdenfNegativeCanaryLeaves =
        [cdenfTargetResidualReport] ∧
      ¬ CDENFAllTargetRelevantLeavesInAllowedClasses
        cdenfNegativeCanaryLeaves := by
  exact cdenfNormalizer_lab_negative_canary

theorem cdenf_normalizer_negative_report_regression :
    cdenfTargetResidualReport.rawAtom = .positiveResidual ∧
      cdenfTargetResidualReport.source = .positiveCorrelationTail ∧
      cdenfTargetResidualReport.branchContext = .targetMessageBranch := by
  exact cdenfNormalizer_lab_negative_report_pinpoints_obligation

theorem cdenf_normalizer_off_target_guard_regression :
    cdenfOffTargetResidualLeaf.targetResidualReport? = none ∧
      CDENFAllTargetRelevantLeavesInAllowedClasses
        [cdenfOffTargetResidualLeaf] := by
  exact cdenfNormalizer_offTargetResidual_not_target_obligation

theorem cdenf_normalizer_blocks_v13_normalization_regression :
    ¬ cdenfEvidenceSurface.NormalizesNonNeutral := by
  exact cdenfNormalizer_lab_negative_blocks_v13_normalization

theorem cdenf_normalizer_separates_off_target_from_target_regression :
    CDENFAllTargetRelevantLeavesInAllowedClasses [cdenfOffTargetResidualLeaf] ∧
      ¬ CDENFAllTargetRelevantLeavesInAllowedClasses [cdenfTargetResidualLeaf] := by
  exact cdenfNormalizerCanaries_separate_offTarget_from_targetResidual

end Mettapedia.Computability.PNP.PNPv13CDENFNormalizerCanariesRegression
