import Mettapedia.Computability.PNP.CruxRandomizedResidualAnchorsSymmetry
import Mettapedia.Computability.PNP.CruxRandomizedResidualAnchorsPostSwitchFork
import Mettapedia.Computability.PNP.CruxRandomizedResidualAnchorsFiniteCoin
import Mettapedia.Computability.PNP.CruxRandomizedResidualAnchorsPostSwitchFiniteCoin

/-!
# Regression checks for PNP residual-side-information anchors: global weakness, invariant-score, and asymmetry-budget checks

This module is part of the decomposed residual-side-information regression
ledger.  It keeps the historical `CruxSynthesisRegression` theorem namespace
while separating residual-anchor checks by mathematical role.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
open Mettapedia.GSLT.Meredith.WeaknessBridge
universe u v w z

theorem global_weakness_distinction_family_not_surjective_regression
    {U : Type u} [Fintype U] [DecidableEq U] [Nontrivial U]
    {Q : Type v} [Monoid Q] [CompleteLattice Q]
    (ev : GSLTEvidence U Q) {Index : Type*} {predict : Index → U → Bool}
    (hfamily : FamilyFactorsThroughDistinctionWeakness ev predict) :
    ¬ Function.Surjective predict := by
  exact
    globalWeaknessCoverage_anchor_distinction_family_not_surjective
      ev hfamily

theorem global_weakness_nonDistinction_family_not_surjective_regression
    {U : Type u} [Fintype U] [DecidableEq U] [Nontrivial U]
    {Q : Type v} [Monoid Q] [CompleteLattice Q]
    (ev : GSLTEvidence U Q) {Index : Type*} {predict : Index → U → Bool}
    (hfamily : FamilyFactorsThroughNonDistinctionWeakness ev predict) :
    ¬ Function.Surjective predict := by
  exact
    globalWeaknessCoverage_anchor_nonDistinction_family_not_surjective
      ev hfamily

theorem invariant_score_anchor_score_support_weight_symmetric_zero_signal_regression
    {α U : Type*} [Fintype α]
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → ℕ)
    (score : U → ℤ)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hsym : ∀ x, score (u x) ≠ 0 → w (τ x) = w x) :
    ∑ x : α, signedScoreContribution u y w score x = 0 := by
  exact
    invariantScoreCoverage_anchor_score_support_weight_symmetric_zero_signal
      τ u y w score hτ hu hy hsym

theorem invariant_score_anchor_nonzero_signal_exposes_weight_asymmetric_score_point_regression
    {α U : Type*} [Fintype α]
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → ℕ)
    (score : U → ℤ)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hsignal :
      (∑ x : α, signedScoreContribution u y w score x) ≠ 0) :
    ∃ x, w x ≠ w (τ x) ∧ score (u x) ≠ 0 := by
  exact
    invariantScoreCoverage_anchor_nonzero_signal_exposes_weight_asymmetric_score_point
      τ u y w score hτ hu hy hsignal

theorem asymmetry_budget_anchor_support_inside_symmetric_slice_blocks_strict_advantage_regression
    {α U : Type*} [Fintype α]
    (τ : α → α) (p : α → Prop) [DecidablePred p]
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hτ : Function.Involutive τ)
    (hp : ∀ x, p x → p (τ x))
    (hu : ∀ x, p x → u (τ x) = u x)
    (hy : ∀ x, p x → y (τ x) = !(y x))
    (hw : ∀ x, p x → w (τ x) = w x)
    (hsupport : ∀ x, 0 < w x → p x) :
    ¬ weightedTotalMass w < 2 * weightedCorrectMass u y w h := by
  exact
    asymmetryBudgetCoverage_anchor_support_inside_symmetric_slice_blocks_strict_advantage
      τ p u y w h hτ hp hu hy hw hsupport

theorem asymmetry_budget_anchor_strict_advantage_exposes_outside_support_regression
    {α U : Type*} [Fintype α]
    (τ : α → α) (p : α → Prop) [DecidablePred p]
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hτ : Function.Involutive τ)
    (hp : ∀ x, p x → p (τ x))
    (hu : ∀ x, p x → u (τ x) = u x)
    (hy : ∀ x, p x → y (τ x) = !(y x))
    (hw : ∀ x, p x → w (τ x) = w x)
    (hadv : weightedTotalMass w < 2 * weightedCorrectMass u y w h) :
    ∃ x, 0 < w x ∧ ¬ p x := by
  exact
    asymmetryBudgetCoverage_anchor_strict_advantage_exposes_outside_support
      τ p u y w h hτ hp hu hy hw hadv

end Mettapedia.Computability.PNP.CruxSynthesisRegression
