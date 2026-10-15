import Mettapedia.Logic.MarkovLogicFiniteVolumeContraction

/-!
# A finite shell approximates a local query under uniform Dobrushin contraction

This packages the established restricted-DLR comparison; it introduces no new
convergence argument. The model must have a uniform influence bound C < 1.
It is not a convergence theorem for a loopy belief-propagation implementation.
-/

namespace Mettapedia.Logic.MarkovLogicLocalQueryApproximation
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteFiniteVolume
open Mettapedia.Logic.MarkovLogicInfinitePositive
open Mettapedia.Logic.MarkovLogicInfiniteWorldMeasures
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicFiniteVolumeContraction
open MeasureTheory

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- Every boundary-conditioned n-shell answer differs from a full DLR answer
by at most 2|Γ|C^n, under the stated uniform influence hypothesis. -/
theorem shell_query_error (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {C : ℝ} (hC_nonneg : 0 ≤ C) (hC_lt_one : C < 1)
    (hC_bound : ∀ Δ : Region Atom, M.finiteRegionPairwiseDobrushinConstant Δ ≤ C)
    (μ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Atom)))
    (Γ : Region Atom) (q : LocalConstraintQuery Atom Γ) (n : ℕ)
    (ξ : BoundaryCondition Atom) :
    let ν : ProbabilityMeasure (InfiniteWorld Atom) :=
      ⟨M.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure
        (M.iterExpandRegion Γ n) ξ, inferInstance⟩
    M.finiteRegionLocalQueryDiscrepancy μ ν Γ q ≤ 2 * (Γ.card : ℝ) * C^n := by
  dsimp only
  exact localQueryDiscrepancy_le_two_mul_card_mul_pow_on M hC_nonneg hC_lt_one
    hC_bound μ _ (FixedRegionCylinderDLR_on_of_full _ _ hμ _)
    (finiteVolumeWorldMeasure_fixedRegionCylinderDLR_on _ _ ξ) Γ q n (by intro i hi; exact hi)

end Mettapedia.Logic.MarkovLogicLocalQueryApproximation
