import Mettapedia.Computability.PNP.ABDecisionListObstruction
import Mettapedia.Computability.PNP.SharedABFeatureObstructionFullExactPullback

/-!
# PNP `Kpoly` coverage anchors: full AB obstructions

Raw and exact-visible full `(a,b)` rule-family obstructions for decision-list, affine-feature, and sparse-threshold classes.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: the full raw `(a,b)` Boolean rule family is not
realized by the fixed-order raw decision-list class at positive width. -/
theorem kpolyCoverage_anchor_fullABRule_not_rawDecisionList_of_pos
    {k : ℕ} (hk : 0 < k) :
    ¬ RealizedByABDecisionListFamily (k := k) (fullABRuleFamily k) :=
  fullABRuleFamily_not_realizedByABDecisionListFamily_of_pos (k := k) hk

/-- Route-coverage anchor: the exact visible pullback of the full raw `(a,b)`
rule family is not realized by the raw exact-surface decision-list class at
positive width. -/
theorem kpolyCoverage_anchor_fullExactABRule_not_rawExactDecisionList_of_pos
    (Z : Type*) [Inhabited Z] {k : ℕ} (hk : 0 < k) :
    ¬ RealizedByRawExactABDecisionListFamily (Z := Z) (k := k)
        (fullExactABRuleFamily Z k) :=
  fullExactABRuleFamily_not_realizedByRawExactABDecisionListFamily_of_pos
    (Z := Z) (k := k) hk

/-- Route-coverage anchor: the full raw `(a,b)` Boolean rule family is not
realized by shared affine-feature families below the reduced truth-table
threshold. -/
theorem kpolyCoverage_anchor_fullABRule_not_sharedAffineFeature_of_lt_cardFormula
    {r k : ℕ} (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 ^ r < 2 ^ (2 * k)) :
    ¬ RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features
        (fullABRuleFamily k) :=
  fullABRuleFamily_not_realizedBySharedABAffineFeatureFamily_of_lt_cardFormula
    (r := r) (k := k) features hs

/-- Route-coverage anchor: the full raw `(a,b)` Boolean rule family is not
realized by shared sparse-threshold families below the reduced truth-table
threshold. -/
theorem kpolyCoverage_anchor_fullABRule_not_sharedSparseThreshold_of_lt_cardFormula
    {r k : ℕ} (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 * r < 2 ^ (2 * k)) :
    ¬ RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features
        (fullABRuleFamily k) :=
  fullABRuleFamily_not_realizedBySharedABSparseThresholdAffineFamily_of_lt_cardFormula
    (r := r) (k := k) features hs

/-- Route-coverage anchor: the full raw `(a,b)` Boolean rule family is not
realized by shared decision-list families below the reduced truth-table
threshold. -/
theorem kpolyCoverage_anchor_fullABRule_not_sharedDecisionList_of_lt_cardFormula
    {r k : ℕ} (features : Fin r → AffineColumnCode (k + k))
    (hs : r + 1 < 2 ^ (2 * k)) :
    ¬ RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features
        (fullABRuleFamily k) :=
  fullABRuleFamily_not_realizedBySharedABAffineDecisionListFamily_of_lt_cardFormula
    (r := r) (k := k) features hs

/-- Route-coverage anchor: the exact visible pullback of the full raw `(a,b)`
rule family is not realized by shared affine-feature exact families below the
reduced truth-table threshold. -/
theorem kpolyCoverage_anchor_fullExactABRule_not_sharedExactAffineFeature_of_lt_cardFormula
    (Z : Type*) [Inhabited Z] {r k : ℕ}
    (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 ^ r < 2 ^ (2 * k)) :
    ¬ RealizedBySharedExactABAffineFeatureFamily (Z := Z) (r := r) (k := k)
        features (fullExactABRuleFamily Z k) :=
  fullExactABRuleFamily_not_realizedBySharedExactABAffineFeatureFamily_of_lt_cardFormula
    (Z := Z) (r := r) (k := k) features hs

/-- Route-coverage anchor: the exact visible pullback of the full raw `(a,b)`
rule family is not realized by shared sparse-threshold exact families below the
reduced truth-table threshold. -/
theorem kpolyCoverage_anchor_fullExactABRule_not_sharedExactSparseThreshold_of_lt_cardFormula
    (Z : Type*) [Inhabited Z] {r k : ℕ}
    (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 * r < 2 ^ (2 * k)) :
    ¬ RealizedBySharedExactABSparseThresholdAffineFamily (Z := Z) (r := r) (k := k)
        features (fullExactABRuleFamily Z k) :=
  fullExactABRuleFamily_not_realizedBySharedExactABSparseThresholdAffineFamily_of_lt_cardFormula
    (Z := Z) (r := r) (k := k) features hs

/-- Route-coverage anchor: the exact visible pullback of the full raw `(a,b)`
rule family is not realized by shared decision-list exact families below the
reduced truth-table threshold. -/
theorem kpolyCoverage_anchor_fullExactABRule_not_sharedExactDecisionList_of_lt_cardFormula
    (Z : Type*) [Inhabited Z] {r k : ℕ}
    (features : Fin r → AffineColumnCode (k + k))
    (hs : r + 1 < 2 ^ (2 * k)) :
    ¬ RealizedBySharedExactABAffineDecisionListFamily (Z := Z) (r := r) (k := k)
        features (fullExactABRuleFamily Z k) :=
  fullExactABRuleFamily_not_realizedBySharedExactABAffineDecisionListFamily_of_lt_cardFormula
    (Z := Z) (r := r) (k := k) features hs


end Mettapedia.Computability.PNP
