import Mettapedia.Computability.PNP.ABDecisionListObstruction
import Mettapedia.Computability.PNP.SharedABFeatureRoutesExactPullback

/-!
# Shared `(a,b)` feature obstructions: reduced full-rule lower bounds

This module isolates truth-table lower bounds for the full raw `(a,b)` rule
family under shared affine, sparse-threshold, and decision-list feature routes.
-/

namespace Mettapedia.Computability.PNP

section ReducedFullRules

variable {r k : ℕ}

/-- The full raw `(a,b)` rule family cannot be realized by a shared affine
feature family below the reduced truth-table threshold. -/
theorem fullABRuleFamily_not_realizedBySharedABAffineFeatureFamily_of_lt_surfaceCard
    (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 ^ r < Fintype.card (ABVisibleSurface k)) :
    ¬ RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features
        (fullABRuleFamily k) := by
  exact
    not_realizedBySharedABAffineFeatureFamily_of_surjective_predict_of_lt_surfaceCard
      (r := r) (k := k) hs (fullABRuleFamily_surjective k)

/-- Formula form of the full-rule obstruction for shared affine features. -/
theorem fullABRuleFamily_not_realizedBySharedABAffineFeatureFamily_of_lt_cardFormula
    (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 ^ r < 2 ^ (2 * k)) :
    ¬ RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features
        (fullABRuleFamily k) := by
  exact
    fullABRuleFamily_not_realizedBySharedABAffineFeatureFamily_of_lt_surfaceCard
      (r := r) (k := k) features
      (by simpa [card_abVisibleSurface (k := k)] using hs)

/-- The full raw `(a,b)` rule family cannot be realized by a shared sparse
threshold family below the reduced truth-table threshold. -/
theorem fullABRuleFamily_not_realizedBySharedABSparseThresholdAffineFamily_of_lt_surfaceCard
    (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 * r < Fintype.card (ABVisibleSurface k)) :
    ¬ RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features
        (fullABRuleFamily k) := by
  exact
    not_realizedBySharedABSparseThresholdAffineFamily_of_surjective_predict_of_lt_surfaceCard
      (r := r) (k := k) hs (fullABRuleFamily_surjective k)

/-- Formula form of the full-rule obstruction for shared sparse-threshold
features. -/
theorem fullABRuleFamily_not_realizedBySharedABSparseThresholdAffineFamily_of_lt_cardFormula
    (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 * r < 2 ^ (2 * k)) :
    ¬ RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features
        (fullABRuleFamily k) := by
  exact
    fullABRuleFamily_not_realizedBySharedABSparseThresholdAffineFamily_of_lt_surfaceCard
      (r := r) (k := k) features
      (by simpa [card_abVisibleSurface (k := k)] using hs)

/-- The full raw `(a,b)` rule family cannot be realized by a shared decision-list
family below the reduced truth-table threshold. -/
theorem fullABRuleFamily_not_realizedBySharedABAffineDecisionListFamily_of_lt_surfaceCard
    (features : Fin r → AffineColumnCode (k + k))
    (hs : r + 1 < Fintype.card (ABVisibleSurface k)) :
    ¬ RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features
        (fullABRuleFamily k) := by
  exact
    not_realizedBySharedABAffineDecisionListFamily_of_surjective_predict_of_lt_surfaceCard
      (r := r) (k := k) hs (fullABRuleFamily_surjective k)

/-- Formula form of the full-rule obstruction for shared decision-list
features. -/
theorem fullABRuleFamily_not_realizedBySharedABAffineDecisionListFamily_of_lt_cardFormula
    (features : Fin r → AffineColumnCode (k + k))
    (hs : r + 1 < 2 ^ (2 * k)) :
    ¬ RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features
        (fullABRuleFamily k) := by
  exact
    fullABRuleFamily_not_realizedBySharedABAffineDecisionListFamily_of_lt_surfaceCard
      (r := r) (k := k) features
      (by simpa [card_abVisibleSurface (k := k)] using hs)

end ReducedFullRules

end Mettapedia.Computability.PNP
