import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExistentialPackagesCore
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExistentialPackagesSupported
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExistentialPackagesNoVisiblePairBalancing
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExistentialPackagesExactSuccess

/-!
# PNP residual-side-information repair-equivalence coverage specification

This file names the reusable subpackages in the residual-side-information
repair/equivalence layer.  The proof file proves each subcoverage from the
underlying theorem-backed anchors.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Positive and strict-half success can be repackaged as resolving witnesses,
with or without the no-visible-pair-balancing refinement. -/
def ResidualSideInformationRepairWitnessCoverage : Prop :=
  (∀ {α Base Side : Type} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              ((∃ h : Base × Side → Bool,
                0 < doubledAdvantage (fun x => (base x, side x)) y w h) ↔
              ∃ h : Base × Side → Bool,
                0 < doubledAdvantage (fun x => (base x, side x)) y w h ∧
                0 < resolvedMass τ side w ∧
                (∃ x, 0 < w x ∧
                  base (τ x) = base x ∧ side (τ x) ≠ side x))) ∧
  (∀ {α Base Side : Type} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              ((∃ h : Base × Side → Bool,
                weightedTotalMass w <
                  2 * weightedCorrectMass (fun x => (base x, side x)) y w h) ↔
              ∃ h : Base × Side → Bool,
                weightedTotalMass w <
                  2 * weightedCorrectMass (fun x => (base x, side x)) y w h ∧
                0 < resolvedMass τ side w ∧
                (∃ x, 0 < w x ∧
                  base (τ x) = base x ∧ side (τ x) ≠ side x))) ∧
  (∀ {α Base Side : Type} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              ((∃ h : Base × Side → Bool,
                0 < doubledAdvantage (fun x => (base x, side x)) y w h) ↔
              ∃ h : Base × Side → Bool,
                0 < doubledAdvantage (fun x => (base x, side x)) y w h ∧
                0 < resolvedMass τ side w ∧
                (∃ x, 0 < w x ∧
                  base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
                ¬ SupportwiseVisiblePairBalancing base side y w)) ∧
  (∀ {α Base Side : Type} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              ((∃ h : Base × Side → Bool,
                weightedTotalMass w <
                  2 * weightedCorrectMass (fun x => (base x, side x)) y w h) ↔
              ∃ h : Base × Side → Bool,
                weightedTotalMass w <
                  2 * weightedCorrectMass (fun x => (base x, side x)) y w h ∧
                0 < resolvedMass τ side w ∧
                (∃ x, 0 < w x ∧
                  base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
                ¬ SupportwiseVisiblePairBalancing base side y w))

/-- Positive or strict-half success is equivalent to a visible-pair fiber
imbalance in the finite visible feature space. -/
def ResidualSideInformationRepairFiberImbalanceCoverage : Prop :=
  (∀ {α Base Side : Type} [Fintype α] [Fintype Base] [Fintype Side]
    [DecidableEq Base] [DecidableEq Side]
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ),
      ((∃ h : Base × Side → Bool,
        0 < doubledAdvantage (fun x => (base x, side x)) y w h) ↔
      ∃ bs : Base × Side,
        weightedFeatureFiberTrueMass (fun x => (base x, side x)) y w bs ≠
          weightedFeatureFiberFalseMass (fun x => (base x, side x)) y w bs)) ∧
  (∀ {α Base Side : Type} [Fintype α] [Fintype Base] [Fintype Side]
    [DecidableEq Base] [DecidableEq Side]
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ),
      ((∃ h : Base × Side → Bool,
        weightedTotalMass w <
          2 * weightedCorrectMass (fun x => (base x, side x)) y w h) ↔
      ∃ bs : Base × Side,
        weightedFeatureFiberTrueMass (fun x => (base x, side x)) y w bs ≠
          weightedFeatureFiberFalseMass (fun x => (base x, side x)) y w bs))

/-- Positive or strict-half success exposes the residual-side-information
obstruction packages used by the repair/equivalence layer. -/
def ResidualSideInformationRepairObstructionPackageCoverage : Prop :=
  (∀ {α Base Side : Type} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              0 < doubledAdvantage (fun x => (base x, side x)) y w h →
                0 < resolvedMass τ side w ∧
                  ¬ SideInfoDeterminedBy base side ∧
                  ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
                  (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
                  (∃ x, 0 < w x ∧
                    ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
                  (∃ x, 0 < w x ∧
                    h (base (τ x), side (τ x)) ≠ h (base x, side x))) ∧
  (∀ {α Base Side : Type} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              (∃ h : Base × Side → Bool,
                0 < doubledAdvantage (fun x => (base x, side x)) y w h) →
              0 < resolvedMass τ side w ∧
                ¬ SideInfoDeterminedBy base side ∧
                PositiveWeightSideInfoCollisionOverBase base side w ∧
                (∃ x, 0 < w x ∧
                  base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
                (∃ x, 0 < w x ∧
                  ¬ SourceOnlyPredicateCapturesSideEq base side (side x))) ∧
  (∀ {α Base Side : Type} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              (∃ h : Base × Side → Bool,
                weightedTotalMass w <
                  2 * weightedCorrectMass (fun x => (base x, side x)) y w h) →
              0 < resolvedMass τ side w ∧
                ¬ SideInfoDeterminedBy base side ∧
                PositiveWeightSideInfoCollisionOverBase base side w ∧
                (∃ x, 0 < w x ∧
                  base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
                (∃ x, 0 < w x ∧
                  ¬ SourceOnlyPredicateCapturesSideEq base side (side x))) ∧
  (∀ {α Base Side : Type} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              ((∃ h : Base × Side → Bool,
                0 < doubledAdvantage (fun x => (base x, side x)) y w h) ↔
              ∃ h : Base × Side → Bool,
                0 < doubledAdvantage (fun x => (base x, side x)) y w h ∧
                0 < resolvedMass τ side w ∧
                ¬ SideInfoDeterminedBy base side ∧
                ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
                (∃ x, 0 < w x ∧
                  base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
                (∃ x, 0 < w x ∧
                  ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
                (∃ x, 0 < w x ∧
                  h (base (τ x), side (τ x)) ≠ h (base x, side x)))) ∧
  (∀ {α Base Side : Type} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              ((∃ h : Base × Side → Bool,
                weightedTotalMass w <
                  2 * weightedCorrectMass (fun x => (base x, side x)) y w h) ↔
              ∃ h : Base × Side → Bool,
                weightedTotalMass w <
                  2 * weightedCorrectMass (fun x => (base x, side x)) y w h ∧
                0 < resolvedMass τ side w ∧
                ¬ SideInfoDeterminedBy base side ∧
                ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
                (∃ x, 0 < w x ∧
                  base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
                (∃ x, 0 < w x ∧
                  ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
                (∃ x, 0 < w x ∧
                  h (base (τ x), side (τ x)) ≠ h (base x, side x)))) ∧
  (∀ {α Base Side : Type} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              ((∃ h : Base × Side → Bool,
                0 < doubledAdvantage (fun x => (base x, side x)) y w h) ↔
              ∃ h : Base × Side → Bool,
                0 < doubledAdvantage (fun x => (base x, side x)) y w h ∧
                0 < resolvedMass τ side w ∧
                ¬ SideInfoDeterminedBy base side ∧
                ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
                (∃ x, 0 < w x ∧
                  base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
                (∃ x, 0 < w x ∧
                  ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
                (∃ x, 0 < w x ∧
                  h (base (τ x), side (τ x)) ≠ h (base x, side x)) ∧
                ¬ SupportwiseVisiblePairBalancing base side y w)) ∧
  (∀ {α Base Side : Type} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              ((∃ h : Base × Side → Bool,
                weightedTotalMass w <
                  2 * weightedCorrectMass (fun x => (base x, side x)) y w h) ↔
              ∃ h : Base × Side → Bool,
                weightedTotalMass w <
                  2 * weightedCorrectMass (fun x => (base x, side x)) y w h ∧
                0 < resolvedMass τ side w ∧
                ¬ SideInfoDeterminedBy base side ∧
                ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
                (∃ x, 0 < w x ∧
                  base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
                (∃ x, 0 < w x ∧
                  ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
                (∃ x, 0 < w x ∧
                  h (base (τ x), side (τ x)) ≠ h (base x, side x)) ∧
                ¬ SupportwiseVisiblePairBalancing base side y w))

/-- Exact supported success is exactly the full residual-resolution budget
plus the supported obstruction package and the no-visible-pair-balancing
condition. -/
def ResidualSideInformationRepairExactSuccessCoverage : Prop :=
  ∀ {α Base Side : Type} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              (((∃ h : Base × Side → Bool,
                weightedCorrectMass (fun x => (base x, side x)) y w h =
                  weightedTotalMass w) ∧
                0 < weightedTotalMass w) ↔
              ∃ h : Base × Side → Bool,
                doubledAdvantage (fun x => (base x, side x)) y w h =
                    resolvedMass τ side w ∧
                  resolvedMass τ side w = weightedTotalMass w ∧
                  0 < resolvedMass τ side w ∧
                  ¬ SideInfoDeterminedBy base side ∧
                  ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
                  (∃ x, 0 < w x ∧
                    base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
                  (∃ x, 0 < w x ∧
                    ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
                  (∃ x, 0 < w x ∧
                    h (base (τ x), side (τ x)) ≠ h (base x, side x)) ∧
                  ¬ SupportwiseVisiblePairBalancing base side y w)

/-- The broad residual-side-information repair/equivalence layer. -/
def ResidualSideInformationRepairEquivalenceCoverage : Prop :=
  ResidualSideInformationRepairWitnessCoverage ∧
    ResidualSideInformationRepairFiberImbalanceCoverage ∧
      ResidualSideInformationRepairObstructionPackageCoverage ∧
        ResidualSideInformationRepairExactSuccessCoverage

end Mettapedia.Computability.PNP
