import Mettapedia.Computability.PNP.SharedABFeatureObstructionExactPullback

/-!
# Shared `(a,b)` feature obstructions: full exact-pullback corollaries

This module applies the exact pullback obstruction layer to the full raw
`(a,b)` rule family.
-/

namespace Mettapedia.Computability.PNP

section FullExactPullback

variable {Z : Type*} {r k : ℕ}

/-- The exact pullback of the full raw `(a,b)` rule family cannot be realized by
shared affine features below the reduced truth-table threshold. -/
theorem fullExactABRuleFamily_not_realizedBySharedExactABAffineFeatureFamily_of_lt_surfaceCard
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 ^ r < Fintype.card (ABVisibleSurface k)) :
    ¬ RealizedBySharedExactABAffineFeatureFamily
        (Z := Z) (r := r) (k := k) features (fullExactABRuleFamily Z k) := by
  exact
    not_realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab_and_surjective_predict_of_lt_surfaceCard
      (Z := Z) (r := r) (k := k) hs
      (fullExactABRuleFamily_factorsThrough_ab Z k)
      (fullABRuleFamily_surjective k)

/-- Formula form for the exact full raw-rule pullback and shared affine
features. -/
theorem fullExactABRuleFamily_not_realizedBySharedExactABAffineFeatureFamily_of_lt_cardFormula
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 ^ r < 2 ^ (2 * k)) :
    ¬ RealizedBySharedExactABAffineFeatureFamily
        (Z := Z) (r := r) (k := k) features (fullExactABRuleFamily Z k) := by
  exact
    fullExactABRuleFamily_not_realizedBySharedExactABAffineFeatureFamily_of_lt_surfaceCard
      (Z := Z) (r := r) (k := k) features
      (by simpa [card_abVisibleSurface (k := k)] using hs)

/-- The exact pullback of the full raw `(a,b)` rule family cannot be realized by
shared sparse-threshold features below the reduced truth-table threshold. -/
theorem fullExactABRuleFamily_not_realizedBySharedExactABSparseThresholdAffineFamily_of_lt_surfaceCard
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 * r < Fintype.card (ABVisibleSurface k)) :
    ¬ RealizedBySharedExactABSparseThresholdAffineFamily
        (Z := Z) (r := r) (k := k) features (fullExactABRuleFamily Z k) := by
  exact
    not_realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab_and_surjective_predict_of_lt_surfaceCard
      (Z := Z) (r := r) (k := k) hs
      (fullExactABRuleFamily_factorsThrough_ab Z k)
      (fullABRuleFamily_surjective k)

/-- Formula form for the exact full raw-rule pullback and shared
sparse-threshold features. -/
theorem fullExactABRuleFamily_not_realizedBySharedExactABSparseThresholdAffineFamily_of_lt_cardFormula
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 * r < 2 ^ (2 * k)) :
    ¬ RealizedBySharedExactABSparseThresholdAffineFamily
        (Z := Z) (r := r) (k := k) features (fullExactABRuleFamily Z k) := by
  exact
    fullExactABRuleFamily_not_realizedBySharedExactABSparseThresholdAffineFamily_of_lt_surfaceCard
      (Z := Z) (r := r) (k := k) features
      (by simpa [card_abVisibleSurface (k := k)] using hs)

/-- The exact pullback of the full raw `(a,b)` rule family cannot be realized by
shared decision-list features below the reduced truth-table threshold. -/
theorem fullExactABRuleFamily_not_realizedBySharedExactABAffineDecisionListFamily_of_lt_surfaceCard
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (hs : r + 1 < Fintype.card (ABVisibleSurface k)) :
    ¬ RealizedBySharedExactABAffineDecisionListFamily
        (Z := Z) (r := r) (k := k) features (fullExactABRuleFamily Z k) := by
  exact
    not_realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab_and_surjective_predict_of_lt_surfaceCard
      (Z := Z) (r := r) (k := k) hs
      (fullExactABRuleFamily_factorsThrough_ab Z k)
      (fullABRuleFamily_surjective k)

/-- Formula form for the exact full raw-rule pullback and shared decision-list
features. -/
theorem fullExactABRuleFamily_not_realizedBySharedExactABAffineDecisionListFamily_of_lt_cardFormula
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (hs : r + 1 < 2 ^ (2 * k)) :
    ¬ RealizedBySharedExactABAffineDecisionListFamily
        (Z := Z) (r := r) (k := k) features (fullExactABRuleFamily Z k) := by
  exact
    fullExactABRuleFamily_not_realizedBySharedExactABAffineDecisionListFamily_of_lt_surfaceCard
      (Z := Z) (r := r) (k := k) features
      (by simpa [card_abVisibleSurface (k := k)] using hs)

end FullExactPullback

end Mettapedia.Computability.PNP
