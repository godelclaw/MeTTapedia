import Mettapedia.Computability.PNP.GlobalWeaknessObstruction
import Mettapedia.Computability.PNP.AsymmetryBudgetObstruction
import Mettapedia.Computability.PNP.WeightAsymmetryObstruction
import Mettapedia.Computability.PNP.ResolutionDemandObstructionAdvantage
import Mettapedia.Computability.PNP.ResolutionDemandObstructionPairBounds
import Mettapedia.Computability.PNP.ResolutionDemandObstructionResolvedMass
import Mettapedia.Computability.PNP.ResolutionDemandObstructionPrediction
import Mettapedia.Computability.PNP.ResolutionDemandObstructionWitnesses

/-!
# PNP randomized-residual anchors: symmetry and side-channel budget

Global weakness, invariant-score, asymmetry-budget, and deterministic side-channel anchors for randomized-residual coverage.
-/

namespace Mettapedia.Computability.PNP

open Mettapedia.GSLT.Meredith.WeaknessBridge
open scoped BigOperators
universe u v w z

/-- Route-coverage anchor: decoding every selected predictor from the one
global distinction-weakness scalar cannot cover all Boolean classifiers on a
nontrivial state space. -/
theorem globalWeaknessCoverage_anchor_distinction_family_not_surjective
    {U : Type u} [Fintype U] [DecidableEq U] [Nontrivial U]
    {Q : Type v} [Monoid Q] [CompleteLattice Q]
    (ev : GSLTEvidence U Q) {Index : Type*} {predict : Index → U → Bool}
    (hfamily : FamilyFactorsThroughDistinctionWeakness ev predict) :
    ¬ Function.Surjective predict :=
  not_surjective_familyFactorsThroughDistinctionWeakness_of_nontrivial
    ev hfamily

/-- Route-coverage anchor: decoding every selected predictor from the one
global non-distinction weakness scalar cannot cover all Boolean classifiers on a
nontrivial state space. -/
theorem globalWeaknessCoverage_anchor_nonDistinction_family_not_surjective
    {U : Type u} [Fintype U] [DecidableEq U] [Nontrivial U]
    {Q : Type v} [Monoid Q] [CompleteLattice Q]
    (ev : GSLTEvidence U Q) {Index : Type*} {predict : Index → U → Bool}
    (hfamily : FamilyFactorsThroughNonDistinctionWeakness ev predict) :
    ¬ Function.Surjective predict :=
  not_surjective_familyFactorsThroughNonDistinctionWeakness_of_nontrivial
    ev hfamily

/-- Route-coverage anchor: an invariant soft score has no signed signal if
weights are symmetric on every nonzero-score point. -/
theorem invariantScoreCoverage_anchor_score_support_weight_symmetric_zero_signal
    {α U : Type*} [Fintype α]
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → ℕ)
    (score : U → ℤ)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hsym : ∀ x, score (u x) ≠ 0 → w (τ x) = w x) :
    ∑ x : α, signedScoreContribution u y w score x = 0 :=
  signedScore_sum_eq_zero_of_score_support_weight_symmetric
    τ u y w score hτ hu hy hsym

/-- Route-coverage anchor: a nonzero invariant-score signal exposes a
nonzero-score sample point where the weighting is asymmetric across the
involution. -/
theorem invariantScoreCoverage_anchor_nonzero_signal_exposes_weight_asymmetric_score_point
    {α U : Type*} [Fintype α]
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → ℕ)
    (score : U → ℤ)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hsignal :
      (∑ x : α, signedScoreContribution u y w score x) ≠ 0) :
    ∃ x, w x ≠ w (τ x) ∧ score (u x) ≠ 0 :=
  exists_weight_asymmetric_score_point_of_signedScore_sum_ne_zero
    τ u y w score hτ hu hy hsignal

/-- Route-coverage anchor: if all positive-weight points remain inside an
unresolved symmetric slice, feature-only classification cannot have strict
advantage over half accuracy. -/
theorem asymmetryBudgetCoverage_anchor_support_inside_symmetric_slice_blocks_strict_advantage
    {α U : Type*} [Fintype α]
    (τ : α → α) (p : α → Prop) [DecidablePred p]
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hτ : Function.Involutive τ)
    (hp : ∀ x, p x → p (τ x))
    (hu : ∀ x, p x → u (τ x) = u x)
    (hy : ∀ x, p x → y (τ x) = !(y x))
    (hw : ∀ x, p x → w (τ x) = w x)
    (hsupport : ∀ x, 0 < w x → p x) :
    ¬ weightedTotalMass w < 2 * weightedCorrectMass u y w h :=
  not_total_lt_two_mul_weightedCorrectMass_of_support_subset
    τ p u y w h hτ hp hu hy hw hsupport

/-- Route-coverage anchor: a strict feature-only advantage claim must expose a
positive-weight sample outside the unresolved symmetric slice. -/
theorem asymmetryBudgetCoverage_anchor_strict_advantage_exposes_outside_support
    {α U : Type*} [Fintype α]
    (τ : α → α) (p : α → Prop) [DecidablePred p]
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hτ : Function.Involutive τ)
    (hp : ∀ x, p x → p (τ x))
    (hu : ∀ x, p x → u (τ x) = u x)
    (hy : ∀ x, p x → y (τ x) = !(y x))
    (hw : ∀ x, p x → w (τ x) = w x)
    (hadv : weightedTotalMass w < 2 * weightedCorrectMass u y w h) :
    ∃ x, 0 < w x ∧ ¬ p x :=
  exists_support_outside_of_total_lt_two_mul_weightedCorrectMass
    τ p u y w h hτ hp hu hy hw hadv

/-- Route-coverage anchor: a deterministic residual side channel that is
unresolved on every positive-weight source point cannot provide positive
doubled advantage. -/
theorem sideChannelCoverage_anchor_supportwise_unresolved_no_positive_advantage
    {α U V : Type*} [Fintype α]
    (τ : α → α) (u : α → U) (v : α → V)
    (y : α → Bool) (w : α → ℕ) (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hunresolved : ∀ x, 0 < w x → v (τ x) = v x) :
    ¬ 0 < doubledAdvantage (fun x => (u x, v x)) y w h :=
  not_pos_doubledAdvantage_pair_of_supportwise_unresolved
    τ u v y w h hτ hu hy hw hunresolved

/-- Route-coverage anchor: positive deterministic side-channel advantage
exposes a positive-weight source point where the side channel changes across
the involution. -/
theorem sideChannelCoverage_anchor_positive_advantage_resolution_witness
    {α U V : Type*} [Fintype α]
    (τ : α → α) (u : α → U) (v : α → V)
    (y : α → Bool) (w : α → ℕ) (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (u x, v x)) y w h) :
    ∃ x, 0 < w x ∧ v (τ x) ≠ v x :=
  exists_resolving_point_of_pos_doubledAdvantage_pair
    τ u v y w h hτ hu hy hw hadv

/-- Route-coverage anchor: phrased directly at the success-rate surface, any
strict advantage over half accuracy from an invariant feature plus residual
side channel exposes a positive-weight point where the residual changes across
the involution. -/
theorem sideChannelCoverage_anchor_strict_half_accuracy_advantage_resolution_witness
    {α U V : Type*} [Fintype α]
    (τ : α → α) (u : α → U) (v : α → V)
    (y : α → Bool) (w : α → ℕ) (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (u x, v x)) y w h) :
    ∃ x, 0 < w x ∧ v (τ x) ≠ v x :=
  exists_resolving_point_of_total_lt_two_mul_weightedCorrectMass_pair
    τ u v y w h hτ hu hy hw hadv

end Mettapedia.Computability.PNP
