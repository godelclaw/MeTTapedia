import Mettapedia.PLN.Comparisons.DeductionStability
import Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointBalancedInformation

/-!
# Finite-world deduction with perturbed premise readouts

The source joint law supplies exact premise values and its balanced CMI
certificate. A separate stability term controls using perturbed readouts in the
existing PLN formula. Their sum bounds the actual source conditional error.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointInputStability

open Mettapedia.PLN.Comparisons.DeductionStability

open Mettapedia.PLN.Core.CompletePLN
open Mettapedia.InformationTheory.FiniteRV
open Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointBalancedInformation

/-- All four exact readouts from one finite joint distribution, with unit-interval proofs. -/
noncomputable def premises {n : ℕ} (joint : JointDistribution n) (a b c : Fin n) : PremiseValues where
  ab := ⟨condProb joint b a, cond_prob_mem_unit joint b a⟩
  bc := ⟨condProb joint c b, cond_prob_mem_unit joint c b⟩
  b := ⟨marginalProb joint b, marginal_prob_bounds joint b⟩
  c := ⟨marginalProb joint c, marginal_prob_bounds joint c⟩

/-- Dependence in the source law and perturbation of the premise readouts
contribute separate, proved terms to the conclusion-error certificate. -/
theorem query_error_with_perturbed_readouts {n : ℕ} (joint : JointDistribution n)
    (a b c : Fin n) (approximate : PremiseValues) (margin : ℝ)
    (possible : 0 < marginalProb joint a) (positive : 0 < margin)
    (sourceSeparated : margin ≤ 1-marginalProb joint b)
    (approximateSeparated : margin ≤ 1-(approximate.b : ℝ)) :
    |completeDeduction joint a b c - estimate approximate| ≤
      Real.sqrt ((1-marginalProb joint a) * condMutualInfo joint.prob
        (worldToAssignment n · a) (worldToAssignment n · b) (worldToAssignment n · c) /
          (2*marginalProb joint a)) +
      perturbationBudget margin (premises joint a b c) approximate := by
  exact (abs_sub_le _ (estimate (premises joint a b c)) _).trans
    (add_le_add (query_error_le_sqrt_balanced_cmi joint a b c possible)
      (estimate_stable (premises joint a b c) approximate margin positive
        sourceSeparated approximateSeparated))

end Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointInputStability
