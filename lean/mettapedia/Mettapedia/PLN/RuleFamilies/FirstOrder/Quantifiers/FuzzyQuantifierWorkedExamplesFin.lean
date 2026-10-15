import Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.QuantifierWorkedExamples
import Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.FuzzyITVBridgeFin

/-!
# Finite Fuzzy Quantifier Worked Examples

Finite/counting Chapter-11 worked examples and canaries.
-/

namespace Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers

abbrev aFewParamsFin := aFewParams
abbrev manyParamsFin := manyParams
abbrev mostParamsFin := mostParams
abbrev fewParamsFin := fewParams
abbrev almostAllParamsFin := almostAllParams
abbrev aboutHalfParamsFin := aboutHalfParams
abbrev probablyParamsFin := probablyParams
abbrev maybeParamsFin := maybeParams
abbrev almostNoneParamsFin := almostNoneParams
abbrev manyNotMostParamsFin := manyNotMostParams
abbrev itvConjunctionSeparationParamsFin := itvConjunctionSeparationParams
abbrev mostPCL1ParamsFin := mostPCL1Params

abbrev oneHighOneLowFin := oneHighOneLow
abbrev bothHighFin := bothHigh
abbrev bothLowFin := bothLow
abbrev threeHighOneLowFin := threeHighOneLow
abbrev oneHighThreeLowFin := oneHighThreeLow
abbrev oneHighFourLowFin5Fin := oneHighFourLowFin5
abbrev threeHighTwoLowFin5Fin := threeHighTwoLowFin5
abbrev itvHiFin := itvHi
abbrev itvLoFin := itvLo
abbrev itvGFin := itvG
noncomputable abbrev rule4ProfileFinFixture := itvSeparationStrengthProfile
abbrev rule4ITVProfileFinFixture := itvSeparationProfile

abbrev canary_crookedLottery_afew_not_forallFin := canary_crookedLottery_afew_not_forall
abbrev canary_fuzzySyllogism_manyFin := canary_fuzzySyllogism_many
abbrev canary_allHigh_forallFin := canary_allHigh_forall
abbrev canary_allLow_not_thereExistsFin := canary_allLow_not_thereExists
abbrev canary_most_fraction_threeQuartersFin := canary_most_fraction_threeQuarters
abbrev canary_few_fraction_oneQuarterFin := canary_few_fraction_oneQuarter
abbrev canary_most_vs_few_split_on_threeQuartersFin := canary_most_vs_few_split_on_threeQuarters
abbrev canary_existentialConjunction_not_equivalent_itvPathFin := canary_existentialConjunction_not_equivalent_itvPath
abbrev canary_itv_strength_interval_of_lower_upperFin :=
  canary_itv_strength_interval_of_lower_upper
abbrev canary_itv_existential_generalization_mixedFin :=
  canary_itv_existential_generalization_mixed
abbrev canary_itv_universal_specification_allHighFin :=
  canary_itv_universal_specification_allHigh
abbrev canary_itv_exchange_allLow_falseFin :=
  canary_itv_exchange_allLow_false
abbrev canary_itv_rule_family_bundle_boolFin :=
  canary_itv_rule_family_bundle_bool

end Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers
