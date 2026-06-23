import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExistentialWitnessesCore
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExistentialWitnessesNoVisiblePairBalancing
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExistentialWitnessesFiberImbalance
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesPure
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesBalancing
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesWitnesses
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesAnySuccess

/-!
# Regression checks for residual-side-information witnesses

Resolving-witness, visible-pair-balancing, and fiber-imbalance wrappers extracted
from the historical residual-side-information ledger regression module.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem residual_side_information_existential_positive_advantage_repair_exposes_resolving_witness_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsuccess : ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x := by
  exact
    residualSideInformationCoverage_anchor_existential_positive_advantage_repair_exposes_resolving_witness
      τ base side y w hτ hbase hy hw hsuccess

theorem residual_side_information_existential_strict_half_repair_exposes_resolving_witness_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsuccess : ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x := by
  exact
    residualSideInformationCoverage_anchor_existential_strict_half_repair_exposes_resolving_witness
      τ base side y w hτ hbase hy hw hsuccess

theorem residual_side_information_positive_advantage_forbids_visible_pair_balancing_regression
    {α Base Side : Type*} [Fintype α]
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ¬ SupportwiseVisiblePairBalancing base side y w := by
  exact
    residualSideInformationCoverage_anchor_positive_advantage_forbids_visible_pair_balancing
      base side y w h hadv

theorem residual_side_information_strict_half_forbids_visible_pair_balancing_regression
    {α Base Side : Type*} [Fintype α]
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ¬ SupportwiseVisiblePairBalancing base side y w := by
  exact
    residualSideInformationCoverage_anchor_strict_half_advantage_forbids_visible_pair_balancing
      base side y w h hadv

theorem residual_side_information_existential_positive_advantage_repair_iff_resolving_witness_and_no_visible_pair_balancing_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    ((∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) ↔
    ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      ¬ SupportwiseVisiblePairBalancing base side y w) := by
  exact
    residualSideInformationCoverage_anchor_existential_positive_advantage_repair_iff_resolving_witness_and_no_visible_pair_balancing
      τ base side y w hτ hbase hy hw

theorem residual_side_information_existential_strict_half_repair_iff_resolving_witness_and_no_visible_pair_balancing_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    ((∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) ↔
    ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      ¬ SupportwiseVisiblePairBalancing base side y w) := by
  exact
    residualSideInformationCoverage_anchor_existential_strict_half_repair_iff_resolving_witness_and_no_visible_pair_balancing
      τ base side y w hτ hbase hy hw

theorem residual_side_information_existential_positive_advantage_repair_iff_visible_pair_fiber_imbalance_regression
    {α Base Side : Type*} [Fintype α] [Fintype Base] [Fintype Side]
    [DecidableEq Base] [DecidableEq Side]
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) :
    (∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) ↔
      ∃ bs : Base × Side,
        weightedFeatureFiberTrueMass (fun x => (base x, side x)) y w bs ≠
          weightedFeatureFiberFalseMass (fun x => (base x, side x)) y w bs := by
  exact
    residualSideInformationCoverage_anchor_existential_positive_advantage_repair_iff_visible_pair_fiber_imbalance
      base side y w

theorem residual_side_information_existential_strict_half_repair_iff_visible_pair_fiber_imbalance_regression
    {α Base Side : Type*} [Fintype α] [Fintype Base] [Fintype Side]
    [DecidableEq Base] [DecidableEq Side]
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) :
    (∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) ↔
      ∃ bs : Base × Side,
        weightedFeatureFiberTrueMass (fun x => (base x, side x)) y w bs ≠
          weightedFeatureFiberFalseMass (fun x => (base x, side x)) y w bs := by
  exact
    residualSideInformationCoverage_anchor_existential_strict_half_repair_iff_visible_pair_fiber_imbalance
      base side y w

theorem residual_side_information_existential_positive_advantage_repair_iff_resolving_witness_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    (∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) ↔
    ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x := by
  exact
    residualSideInformationCoverage_anchor_existential_positive_advantage_repair_iff_resolving_witness
      τ base side y w hτ hbase hy hw

theorem residual_side_information_existential_strict_half_repair_iff_resolving_witness_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    (∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) ↔
    ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x := by
  exact
    residualSideInformationCoverage_anchor_existential_strict_half_repair_iff_resolving_witness
      τ base side y w hτ hbase hy hw

end Mettapedia.Computability.PNP.CruxSynthesisRegression
