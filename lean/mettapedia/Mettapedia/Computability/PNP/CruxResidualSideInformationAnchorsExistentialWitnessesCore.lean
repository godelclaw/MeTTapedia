import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsAdvantageConsequencesCore
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsAdvantageConsequencesPositive
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsAdvantageConsequencesStrictHalf
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsAdvantageConsequencesPrediction
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsAdvantageConsequencesSupportedPackages

/-!
# PNP residual-side-information anchors: existential resolving witnesses

Proof-relevant resolving-witness extraction for existential residual repair claims.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: any existential residual repair claim over an
invariant base is already proof-relevant.  If some classifier on `(base, side)`
achieves positive doubled advantage, Lean extracts that classifier together
with positive resolved mass and a supported same-base residual witness. -/
theorem residualSideInformationCoverage_anchor_existential_positive_advantage_repair_exposes_resolving_witness
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
    exists_classifier_and_same_base_residual_witness_of_exists_pos_doubledAdvantage_invariant_base
      τ base side y w hτ hbase hy hw hsuccess

/-- Route-coverage anchor: the strict half-accuracy residual repair claim is
already proof-relevant in the same minimal sense.  If some classifier on
`(base, side)` beats half accuracy, Lean extracts that classifier together
with positive resolved mass and a supported same-base residual witness. -/
theorem residualSideInformationCoverage_anchor_existential_strict_half_repair_exposes_resolving_witness
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
    exists_classifier_and_same_base_residual_witness_of_exists_total_lt_two_mul_weightedCorrectMass_invariant_base
      τ base side y w hτ hbase hy hw hsuccess

/-- Route-coverage anchor: an existential positive-advantage residual repair
claim is exactly equivalent to the same claim together with the minimal
proof-relevant residual witness forced by success. -/
theorem residualSideInformationCoverage_anchor_existential_positive_advantage_repair_iff_resolving_witness
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
    exists_pos_doubledAdvantage_iff_exists_classifier_and_same_base_residual_witness_invariant_base
      τ base side y w hτ hbase hy hw

/-- Route-coverage anchor: the strict half-accuracy residual repair claim is
exactly equivalent to the same claim together with the minimal proof-relevant
residual witness forced by success. -/
theorem residualSideInformationCoverage_anchor_existential_strict_half_repair_iff_resolving_witness
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
    exists_total_lt_two_mul_weightedCorrectMass_iff_exists_classifier_and_same_base_residual_witness_invariant_base
      τ base side y w hτ hbase hy hw

end Mettapedia.Computability.PNP
