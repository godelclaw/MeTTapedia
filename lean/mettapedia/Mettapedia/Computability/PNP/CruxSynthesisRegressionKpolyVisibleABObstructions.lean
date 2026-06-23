import Mettapedia.Computability.PNP.CruxKpolyCoverageFullABObstructions
import Mettapedia.Computability.PNP.CruxKpolyCoverageProbeObstructions

/-!
# CruxSynthesisRegressionKpolyVisibleABObstructions

AB/full-AB and injective-probe obstruction regressions for visible Kpoly anchors.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem kpoly_anchor_full_ab_rule_not_raw_decision_list_regression
    {k : ℕ} (hk : 0 < k) :
    ¬ RealizedByABDecisionListFamily (k := k) (fullABRuleFamily k) := by
  exact kpolyCoverage_anchor_fullABRule_not_rawDecisionList_of_pos
    (k := k) hk

theorem kpoly_anchor_full_exact_ab_rule_not_raw_exact_decision_list_regression
    (Z : Type*) [Inhabited Z] {k : ℕ} (hk : 0 < k) :
    ¬ RealizedByRawExactABDecisionListFamily (Z := Z) (k := k)
        (fullExactABRuleFamily Z k) := by
  exact kpolyCoverage_anchor_fullExactABRule_not_rawExactDecisionList_of_pos
    (Z := Z) (k := k) hk

theorem kpoly_anchor_full_ab_rule_not_shared_affine_feature_regression
    {r k : ℕ} (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 ^ r < 2 ^ (2 * k)) :
    ¬ RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features
        (fullABRuleFamily k) := by
  exact kpolyCoverage_anchor_fullABRule_not_sharedAffineFeature_of_lt_cardFormula
    (r := r) (k := k) features hs

theorem kpoly_anchor_full_ab_rule_not_shared_sparse_threshold_regression
    {r k : ℕ} (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 * r < 2 ^ (2 * k)) :
    ¬ RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features
        (fullABRuleFamily k) := by
  exact kpolyCoverage_anchor_fullABRule_not_sharedSparseThreshold_of_lt_cardFormula
    (r := r) (k := k) features hs

theorem kpoly_anchor_full_ab_rule_not_shared_decision_list_regression
    {r k : ℕ} (features : Fin r → AffineColumnCode (k + k))
    (hs : r + 1 < 2 ^ (2 * k)) :
    ¬ RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features
        (fullABRuleFamily k) := by
  exact kpolyCoverage_anchor_fullABRule_not_sharedDecisionList_of_lt_cardFormula
    (r := r) (k := k) features hs

theorem kpoly_anchor_full_exact_ab_rule_not_shared_exact_affine_feature_regression
    (Z : Type*) [Inhabited Z] {r k : ℕ}
    (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 ^ r < 2 ^ (2 * k)) :
    ¬ RealizedBySharedExactABAffineFeatureFamily (Z := Z) (r := r) (k := k)
        features (fullExactABRuleFamily Z k) := by
  exact kpolyCoverage_anchor_fullExactABRule_not_sharedExactAffineFeature_of_lt_cardFormula
    (Z := Z) (r := r) (k := k) features hs

theorem kpoly_anchor_full_exact_ab_rule_not_shared_exact_sparse_threshold_regression
    (Z : Type*) [Inhabited Z] {r k : ℕ}
    (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 * r < 2 ^ (2 * k)) :
    ¬ RealizedBySharedExactABSparseThresholdAffineFamily (Z := Z) (r := r) (k := k)
        features (fullExactABRuleFamily Z k) := by
  exact kpolyCoverage_anchor_fullExactABRule_not_sharedExactSparseThreshold_of_lt_cardFormula
    (Z := Z) (r := r) (k := k) features hs

theorem kpoly_anchor_full_exact_ab_rule_not_shared_exact_decision_list_regression
    (Z : Type*) [Inhabited Z] {r k : ℕ}
    (features : Fin r → AffineColumnCode (k + k))
    (hs : r + 1 < 2 ^ (2 * k)) :
    ¬ RealizedBySharedExactABAffineDecisionListFamily (Z := Z) (r := r) (k := k)
        features (fullExactABRuleFamily Z k) := by
  exact kpolyCoverage_anchor_fullExactABRule_not_sharedExactDecisionList_of_lt_cardFormula
    (Z := Z) (r := r) (k := k) features hs

theorem kpoly_anchor_not_shared_ab_affine_feature_of_injective_probe_regression
    {Probe : Type*} [Fintype Probe] {r k : ℕ} {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (2 ^ r) < Fintype.card Probe) :
    ¬ RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features H := by
  exact
    kpolyCoverage_anchor_not_sharedABAffineFeature_of_injective_probe_of_lt_budgetImageCard
      target hinj hprobe hcard

theorem kpoly_anchor_not_shared_ab_sparse_threshold_of_injective_probe_regression
    {Probe : Type*} [Fintype Probe] {r k : ℕ} {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (2 * r) < Fintype.card Probe) :
    ¬ RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features H := by
  exact
    kpolyCoverage_anchor_not_sharedABSparseThreshold_of_injective_probe_of_lt_budgetImageCard
      target hinj hprobe hcard

theorem kpoly_anchor_not_shared_ab_decision_list_of_injective_probe_regression
    {Probe : Type*} [Fintype Probe] {r k : ℕ} {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (r + 1) < Fintype.card Probe) :
    ¬ RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features H := by
  exact
    kpolyCoverage_anchor_not_sharedABDecisionList_of_injective_probe_of_lt_budgetImageCard
      target hinj hprobe hcard

theorem kpoly_anchor_not_shared_exact_ab_affine_feature_of_factorsThrough_injective_probe_regression
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {r k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (2 ^ r) < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ RealizedBySharedExactABAffineFeatureFamily
        (Z := Z) (r := r) (k := k) features G := by
  exact
    kpolyCoverage_anchor_not_sharedExactABAffineFeature_of_factorsThrough_ab_and_injective_probe_of_lt_budgetImageCard
      target hinj hprobe hcard hfactor

theorem kpoly_anchor_not_shared_exact_ab_sparse_threshold_of_factorsThrough_injective_probe_regression
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {r k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (2 * r) < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ RealizedBySharedExactABSparseThresholdAffineFamily
        (Z := Z) (r := r) (k := k) features G := by
  exact
    kpolyCoverage_anchor_not_sharedExactABSparseThreshold_of_factorsThrough_ab_and_injective_probe_of_lt_budgetImageCard
      target hinj hprobe hcard hfactor

theorem kpoly_anchor_not_shared_exact_ab_decision_list_of_factorsThrough_injective_probe_regression
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {r k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (r + 1) < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ RealizedBySharedExactABAffineDecisionListFamily
        (Z := Z) (r := r) (k := k) features G := by
  exact
    kpolyCoverage_anchor_not_sharedExactABDecisionList_of_factorsThrough_ab_and_injective_probe_of_lt_budgetImageCard
      target hinj hprobe hcard hfactor

end Mettapedia.Computability.PNP.CruxSynthesisRegression
