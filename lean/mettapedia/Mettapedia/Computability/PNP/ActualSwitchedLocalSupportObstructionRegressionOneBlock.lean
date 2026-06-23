import Mettapedia.Computability.PNP.ActualSwitchedLocalSupportTransfer
import Mettapedia.Computability.PNP.ActualSwitchedLocalSupportAdaptive
import Mettapedia.Computability.PNP.ActualSwitchedLocalSupportFullRule
import Mettapedia.Computability.PNP.ActualSwitchedLocalSupportCardinality
import Mettapedia.Computability.PNP.ActualSwitchedLocalSupportOneBlock

/-!
# One-block regression checks for the actual-local support obstruction
-/

namespace Mettapedia.Computability.PNP

universe v

section OneBlock

variable {Z : Type v} {k s clock : ℕ}
variable (u0 : ExactVisiblePostSwitchSurface Z k)

theorem regression_oneBlockFullRule_surjective :
    Function.Surjective
      (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily.predict := by
  exact oneBlockFullRule_surjective u0

theorem regression_oneBlockFullRule_observed_budget_one :
    (oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.HasBitBudget 1 := by
  exact oneBlockFullRule_outputFamily_hasBitBudget_one u0

theorem regression_oneBlockFullRule_observed_cover_two :
    (oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.FinitePredictorCover 2 := by
  exact oneBlockFullRule_outputFamily_finitePredictorCover_two u0

theorem regression_oneBlockFullRule_no_uniform_section
    [Fintype Z]
    (hcard : 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ sec : ExactVisiblePostSwitchSurface Z k → Unit,
      (oneBlockFullRuleActualSwitchedLocalInterface u0).HasUniformVisibleSection sec := by
  exact oneBlockFullRule_not_hasUniformVisibleSection_of_one_lt_surfaceCard u0 hcard

theorem regression_oneBlockFullRule_off_support_rules_indistinguishable
    [Fintype Z]
    (hcard : 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ∃ rule₀ rule₁ : ExactVisibleRule Z k,
      rule₀ ≠ rule₁ ∧
        (oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.predict rule₀ =
          (oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.predict rule₁ ∧
        (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily.predict rule₀ ≠
          (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily.predict rule₁ := by
  exact
    oneBlockFullRule_exists_distinct_rules_same_outputFamily_of_one_lt_surfaceCard
      u0 hcard

theorem regression_oneBlockFullRule_no_exact_decoder
    [Fintype Z]
    (hcard : 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ decode : (Unit → Bool) → ExactVisibleRule Z k,
      ∀ rule : ExactVisibleRule Z k,
        decode ((oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.predict rule) =
          rule := by
  exact
    oneBlockFullRule_not_exists_exactDecoder_of_one_lt_surfaceCard
      u0 hcard

theorem regression_oneBlockFullRule_exists_unobservable_eval
    [Fintype Z]
    (hcard : 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ∃ u : ExactVisiblePostSwitchSurface Z k,
      ¬ ∃ decode : (Unit → Bool) → Bool,
        ∀ rule : ExactVisibleRule Z k,
          decode ((oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.predict rule) =
            rule u := by
  exact
    oneBlockFullRule_exists_unobservable_eval_of_one_lt_surfaceCard
      u0 hcard

theorem regression_oneBlockFullRule_no_full_cover
    [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily.FinitePredictorCover
        (2 ^ s) := by
  exact oneBlockFullRule_not_finitePredictorCover_of_lt_surfaceCard u0 hs

theorem regression_oneBlockFullRule_observed_small_not_full_cover
    [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    (oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.FinitePredictorCover 2 ∧
      ¬ (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily.FinitePredictorCover
        (2 ^ s) := by
  exact oneBlockFullRule_observedSmall_and_not_exactVisibleCover u0 hs

theorem regression_oneBlockFullRule_no_clocked_payload
    [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily s clock := by
  exact oneBlockFullRule_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    u0 hs

end OneBlock

end Mettapedia.Computability.PNP
