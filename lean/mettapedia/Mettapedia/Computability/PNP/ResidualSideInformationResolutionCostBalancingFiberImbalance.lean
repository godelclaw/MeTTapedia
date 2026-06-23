import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCostBalancingSourceOnly
import Mathlib.Data.Fintype.Prod

/-!
# Residual side-information resolution cost: visible-fiber imbalance

Visible-pair fiber-imbalance criteria and fiber-balance obstructions for positive and strict-half success.
-/

namespace Mettapedia.Computability.PNP

section

variable {α Base Side : Type*} [Fintype α]

/-- On a finite visible `(base, side)` surface, any positive doubled advantage
must already break true/false mass balance on at least one visible fiber. -/
theorem exists_visiblePair_fiber_imbalance_of_pos_doubledAdvantage
    [Fintype Base] [Fintype Side] [DecidableEq Base] [DecidableEq Side]
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ∃ bs : Base × Side,
      weightedFeatureFiberTrueMass (fun x => (base x, side x)) y w bs ≠
        weightedFeatureFiberFalseMass (fun x => (base x, side x)) y w bs := by
  exact
    exists_weightedFeatureFiber_imbalance_of_pos_doubledAdvantage
      (fun x => (base x, side x)) y w h hadv

/-- The same visible-fiber imbalance is already forced by any strict half
accuracy claim on a finite visible `(base, side)` surface. -/
theorem exists_visiblePair_fiber_imbalance_of_total_lt_two_mul_weightedCorrectMass
    [Fintype Base] [Fintype Side] [DecidableEq Base] [DecidableEq Side]
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ∃ bs : Base × Side,
      weightedFeatureFiberTrueMass (fun x => (base x, side x)) y w bs ≠
        weightedFeatureFiberFalseMass (fun x => (base x, side x)) y w bs := by
  exact
    exists_weightedFeatureFiber_imbalance_of_total_lt_two_mul_weightedCorrectMass
      (fun x => (base x, side x)) y w h hadv

/-- If every visible `(base, side)` fiber is already weight-balanced, then no
classifier on that visible surface can achieve positive doubled advantage. -/
theorem not_pos_doubledAdvantage_pair_of_visiblePair_fiber_balanced
    [Fintype Base] [Fintype Side] [DecidableEq Base] [DecidableEq Side]
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hbal :
      ∀ bs : Base × Side,
        weightedFeatureFiberTrueMass (fun x => (base x, side x)) y w bs =
          weightedFeatureFiberFalseMass (fun x => (base x, side x)) y w bs) :
    ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h := by
  exact
    not_pos_doubledAdvantage_of_weightedFeatureFiberBalanced
      (fun x => (base x, side x)) y w h hbal

/-- The same visible-pair fiber balance blocks every strict-half weighted
success claim on that residual-side visible surface. -/
theorem not_total_lt_two_mul_weightedCorrectMass_pair_of_visiblePair_fiber_balanced
    [Fintype Base] [Fintype Side] [DecidableEq Base] [DecidableEq Side]
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hbal :
      ∀ bs : Base × Side,
        weightedFeatureFiberTrueMass (fun x => (base x, side x)) y w bs =
          weightedFeatureFiberFalseMass (fun x => (base x, side x)) y w bs) :
    ¬ weightedTotalMass w <
      2 * weightedCorrectMass (fun x => (base x, side x)) y w h := by
  exact
    not_total_lt_two_mul_weightedCorrectMass_of_weightedFeatureFiberBalanced
      (fun x => (base x, side x)) y w h hbal

/-- If every visible `(base, side)` fiber is weight-balanced, then there is no
successful classifier anywhere on that visible surface. -/
theorem not_exists_pos_doubledAdvantage_pair_of_visiblePair_fiber_balanced
    [Fintype Base] [Fintype Side] [DecidableEq Base] [DecidableEq Side]
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hbal :
      ∀ bs : Base × Side,
        weightedFeatureFiberTrueMass (fun x => (base x, side x)) y w bs =
          weightedFeatureFiberFalseMass (fun x => (base x, side x)) y w bs) :
    ¬ ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h := by
  rintro ⟨h, hadv⟩
  exact
    (not_pos_doubledAdvantage_pair_of_visiblePair_fiber_balanced
      base side y w h hbal) hadv

/-- The same visible-pair balance obstruction rules out every strict-half
weighted-success classifier on that visible surface. -/
theorem not_exists_total_lt_two_mul_weightedCorrectMass_pair_of_visiblePair_fiber_balanced
    [Fintype Base] [Fintype Side] [DecidableEq Base] [DecidableEq Side]
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hbal :
      ∀ bs : Base × Side,
        weightedFeatureFiberTrueMass (fun x => (base x, side x)) y w bs =
          weightedFeatureFiberFalseMass (fun x => (base x, side x)) y w bs) :
    ¬ ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h := by
  rintro ⟨h, hadv⟩
  exact
    (not_total_lt_two_mul_weightedCorrectMass_pair_of_visiblePair_fiber_balanced
      base side y w h hbal) hadv

/-- On a finite visible `(base, side)` surface, positive doubled advantage
exists exactly when some visible pair fiber has unequal retained `true` and
`false` mass. -/
theorem exists_pos_doubledAdvantage_pair_iff_exists_visiblePair_fiber_imbalance
    [Fintype Base] [Fintype Side] [DecidableEq Base] [DecidableEq Side]
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) :
    (∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) ↔
      ∃ bs : Base × Side,
        weightedFeatureFiberTrueMass (fun x => (base x, side x)) y w bs ≠
          weightedFeatureFiberFalseMass (fun x => (base x, side x)) y w bs := by
  exact
    exists_pos_doubledAdvantage_iff_exists_weightedFeatureFiber_imbalance
      (fun x => (base x, side x)) y w

/-- The strict-half weighted-success formulation has the same exact visible
pair-fiber criterion. -/
theorem exists_total_lt_two_mul_weightedCorrectMass_pair_iff_exists_visiblePair_fiber_imbalance
    [Fintype Base] [Fintype Side] [DecidableEq Base] [DecidableEq Side]
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) :
    (∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) ↔
      ∃ bs : Base × Side,
        weightedFeatureFiberTrueMass (fun x => (base x, side x)) y w bs ≠
          weightedFeatureFiberFalseMass (fun x => (base x, side x)) y w bs := by
  exact
    exists_total_lt_two_mul_weightedCorrectMass_iff_exists_weightedFeatureFiber_imbalance
      (fun x => (base x, side x)) y w

end

end Mettapedia.Computability.PNP
