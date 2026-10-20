import Mettapedia.PLN.Core.CompletePLN
import Mettapedia.ProbabilityTheory.FiniteConditionalStability

/-!
# Finite PLN joint tables and probability vectors

The two records retain exactly the same world weights and normalization
information. Their equivalence does not project a joint table onto marginal
strengths. Event and conditional readouts agree under that equivalence.
-/

namespace Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointDistribution

open Mettapedia.InformationTheory
open Mettapedia.PLN.Core.CompletePLN
open Mettapedia.ProbabilityTheory.FiniteEventMass
open Mettapedia.ProbabilityTheory.FiniteConditionalStability

variable {n : ℕ}

def probabilityEquiv : JointDistribution n ≃ Prob (Fin (2 ^ n)) where
  toFun source := ⟨source.prob, source.prob_nonneg, source.prob_sum_one⟩
  invFun source := ⟨source.1, source.2.1, source.2.2⟩
  left_inv source := by cases source; rfl
  right_inv source := by cases source; rfl

theorem mass_marginal (source : JointDistribution n) (i : Fin n) :
    mass (probabilityEquiv source).1 (worldToAssignment n · i) = marginalProb source i := rfl

theorem mass_joint (source : JointDistribution n) (i j : Fin n) :
    mass (probabilityEquiv source).1
      (fun world => worldToAssignment n world i && worldToAssignment n world j) =
      jointProb2 source i j := by
  simp only [mass, probabilityEquiv, Equiv.coe_fn_mk, jointProb2, Bool.and_eq_true]

theorem conditional_readout (source : JointDistribution n) (i j : Fin n) :
    conditional (probabilityEquiv source).1 (worldToAssignment n · i) (worldToAssignment n · j) =
      condProb source i j := by
  unfold conditional condProb
  rw [mass_joint, mass_marginal]
  dsimp only
  split_ifs with zero
  · simp [zero]
  · rfl

/-- The guarded numerical API agrees with division, including its zero-mass
convention. Possibility is a separate premise of probabilistic use. -/
theorem joint_ratio_readout (source : JointDistribution n) (i j : Fin n) :
    jointProb2 source i j / marginalProb source j = condProb source i j := by
  unfold condProb
  dsimp only
  split_ifs with zero
  · simp [zero]
  · rfl

end Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointDistribution
