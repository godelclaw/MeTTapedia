import Mettapedia.Computability.PNP.CruxKpolyActualLocalPluginFamilies
import Mettapedia.Computability.PNP.CruxKpolyActualLocalSparseThreshold
import Mettapedia.Computability.PNP.CruxKpolyBitFallbackThresholdSurjective

/-!
# CruxSynthesisRegressionKpolyVisibleActualLocalExamples

Concrete surjective actual-local visible-width regressions.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
open scoped ENNReal

universe u v w z

theorem kpoly_anchor_surjective_actual_local_no_extractor_visible_width_plugin_sample_majority_regression
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 0))
    (q : ℝ≥0∞) :
    ¬ ∃ zfeat : BitVec 2 → BitVec 0,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            μ
            (pluginSampleMajorityActualSwitchedLocalInterface (BitVec 2) 0)
            zfeat
            q) := by
  exact
    kpolyCoverage_anchor_surjectiveActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (n := 2)
      (k := 0)
      (r := 0)
      (μ := μ)
      (T := pluginSampleMajorityActualSwitchedLocalInterface (BitVec 2) 0)
      (q := q)
      (kpolyCoverage_anchor_pluginSampleMajority_surjective (BitVec 2) 0)
      (by decide)

theorem kpoly_anchor_surjective_actual_local_not_exists_recovery_of_visible_width_gap_or_lt_one_sub_apply_lightest_point_full_rule_regression
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 0))
    (q : ℝ≥0∞) :
    ¬ ∃ zfeat : BitVec 2 → BitVec 0,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            μ
            (fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
            zfeat
            q) := by
  letI : Nonempty (ExactVisiblePostSwitchSurface (BitVec 2) 0) :=
    ⟨⟨zeroVec, zeroVec, zeroVec⟩⟩
  exact
    kpolyCoverage_anchor_surjectiveActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_visibleWidth_gap_or_lt_one_sub_apply_lightestPoint
      (n := 2)
      (k := 0)
      (r := 0)
      (μ := μ)
      (T := fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
      (q := q)
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec 2) 0)
      (Or.inl (by decide))

end Mettapedia.Computability.PNP.CruxSynthesisRegression
