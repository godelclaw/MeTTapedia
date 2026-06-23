import Mettapedia.Computability.PNP.ResidualSideInformationObstruction
import Mettapedia.Computability.PNP.ResolutionDemandObstructionAdvantage
import Mettapedia.Computability.PNP.ResolutionDemandObstructionPairBounds
import Mettapedia.Computability.PNP.ResolutionDemandObstructionResolvedMass
import Mettapedia.Computability.PNP.ResolutionDemandObstructionPrediction
import Mettapedia.Computability.PNP.ResolutionDemandObstructionWitnesses
import Mettapedia.Computability.PNP.WeightedFeatureFiberMarginMajorityCriterion

/-!
# Residual side-information resolution cost: invariant-base core

Source-determined residual side information over an invariant base has zero resolving mass and cannot beat chance.
-/

namespace Mettapedia.Computability.PNP

section

variable {α Base Side : Type*} [Fintype α]

omit [Fintype α] in
/-- Source-determined side information cannot change across an involution pair
when the base feature does not change. -/
theorem side_eq_under_involution_of_determinedBy_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (hbase : ∀ x, base (τ x) = base x)
    (hdet : SideInfoDeterminedBy base side) :
    ∀ x, side (τ x) = side x := by
  rcases hdet with ⟨decode, hdecode⟩
  intro x
  calc
    side (τ x) = decode (base (τ x)) := (hdecode (τ x)).symm
    _ = decode (base x) := by rw [hbase x]
    _ = side x := hdecode x

/-- A residual side channel decoded from an invariant base has zero
orbit-resolving mass. -/
theorem resolvedMass_eq_zero_of_determinedBy_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x)
    (hdet : SideInfoDeterminedBy base side) :
    resolvedMass τ side w = 0 :=
  resolvedMass_eq_zero_of_unresolved τ side w
    (side_eq_under_involution_of_determinedBy_invariant_base
      τ base side hbase hdet)

/-- A source-determined residual side channel over an invariant base cannot
give positive doubled advantage to a classifier on `(base, side)`. -/
theorem not_pos_doubledAdvantage_pair_of_determinedBy_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hdet : SideInfoDeterminedBy base side)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h :=
  not_pos_doubledAdvantage_pair_of_supportwise_unresolved
    τ base side y w h hτ hbase hy hw
    (fun x _ => side_eq_under_involution_of_determinedBy_invariant_base
      τ base side hbase hdet x)

/-- In the half-accuracy formulation, a classifier on `(base, side)` with
source-determined invariant side information cannot beat chance. -/
theorem not_total_lt_two_mul_weightedCorrectMass_pair_of_determinedBy_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hdet : SideInfoDeterminedBy base side)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    ¬ weightedTotalMass w <
      2 * weightedCorrectMass (fun x => (base x, side x)) y w h := by
  have hbound :
      2 * weightedCorrectMass (fun x => (base x, side x)) y w h
        ≤ weightedTotalMass w + resolvedMass τ side w :=
    two_mul_weightedCorrectMass_pair_le_total_plus_resolvedMass
      τ base side y w h hτ hbase hy hw
  have hzero : resolvedMass τ side w = 0 :=
    resolvedMass_eq_zero_of_determinedBy_invariant_base
      τ base side w hbase hdet
  omega

end

end Mettapedia.Computability.PNP
