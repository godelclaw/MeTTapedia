import Mettapedia.ProbabilityTheory.ImpreciseProbability.IntervalError
import Mettapedia.PLN.Comparisons.ErrorCharacterization
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeductionITVBridge
import Mettapedia.ProbabilityTheory.FiniteEventMass

/-!
# Query error from dependence and compatible joint information

The full joint distribution supplies an actual branch allocation. Its Fréchet
interval bounds the error of any proposed point estimate. The largest endpoint
distance is attained by a compatible allocation, so the bound is sharp for the
information retained in the five deduction inputs. No screening assumption is
needed. More joint information may narrow the interval further.
-/

namespace Mettapedia.PLN.Comparisons.ScreeningErrorBounds

open Mettapedia.PLN.Core.CompletePLN
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction
open Mettapedia.PLN.Comparisons.ErrorCharacterization

open Mettapedia.ProbabilityTheory
open Mettapedia.ProbabilityTheory.ImpreciseProbability.IntervalError

variable {n : ℕ}

private theorem jointAB_of_readout (J : JointDistribution n) (a b : Fin n)
    (possible : marginalProb J a ≠ 0) :
    deductionJointAB (marginalProb J a) (condProb J b a) = jointProb2 J a b := by
  simp only [deductionJointAB, Mettapedia.PLN.Core.CompletePLN.condProb, possible, if_false, jointProb2_comm J b a]
  field_simp

private theorem jointBC_of_readout (J : JointDistribution n) (b c : Fin n) :
    deductionJointBC (marginalProb J b) (condProb J c b) = jointProb2 J b c :=
  marginal_mul_condProb J c b

private theorem complement_mass (J : JointDistribution n) (b : Fin n) :
    1 - marginalProb J b = marginalProbNeg J b :=
  (marginalProbNeg_eq_one_sub J b).symm

private theorem positive_branch_bounds (J : JointDistribution n) (a b c : Fin n) :
    max 0 (jointProb2 J a b + jointProb2 J b c - marginalProb J b) ≤ jointProb3 J a b c ∧
      jointProb3 J a b c ≤ min (jointProb2 J a b) (jointProb2 J b c) := by
  simpa [FiniteEventMass.mass, jointProb2, marginalProb, jointProb3, Bool.and_eq_true, and_assoc] using
    FiniteEventMass.branch_frechet J.prob J.prob_nonneg
      (worldToAssignment n · a) (worldToAssignment n · b) (worldToAssignment n · c)

private theorem negative_branch_bounds (J : JointDistribution n) (a b c : Fin n) :
    max 0 (jointProb2Neg J a b + jointProb2Neg J c b - marginalProbNeg J b) ≤
        jointProb3Neg J a b c ∧
      jointProb3Neg J a b c ≤ min (jointProb2Neg J a b) (jointProb2Neg J c b) := by
  simpa [FiniteEventMass.mass, jointProb2Neg, marginalProbNeg, jointProb3Neg, Bool.and_eq_true,
    Bool.not_eq_true, and_assoc, and_left_comm, and_comm] using
    FiniteEventMass.branch_frechet J.prob J.prob_nonneg
      (worldToAssignment n · a) (fun w => !worldToAssignment n w b) (worldToAssignment n · c)

/-- Every actual joint model supplies the feasibility certificate needed by
the sharp endpoint constructions. No independent feasibility oracle is needed. -/
theorem query_feasible (J : JointDistribution n) (a b c : Fin n)
    (hA : marginalProb J a ≠ 0) :
    DeductionBranchFeasibility (marginalProb J a) (marginalProb J b)
      (marginalProb J c) (condProb J b a) (condProb J c b) := by
  have joint_nonneg : ∀ i j, 0 ≤ jointProb2 J i j := fun i j => event_mass_nonneg J _
  have joint_le : ∀ i j, jointProb2 J i j ≤ marginalProb J j := fun i j =>
    event_mass_mono J _ _ (fun _ h => h.2)
  have outside_nonneg : ∀ i, 0 ≤ jointProb2Neg J i b := fun i => event_mass_nonneg J _
  have outside_le : ∀ i, jointProb2Neg J i b ≤ marginalProbNeg J b := fun i =>
    event_mass_mono J _ _ (fun _ h => h.2)
  constructor
  · rw [jointAB_of_readout J a b hA]; exact joint_nonneg a b
  · rw [jointAB_of_readout J a b hA]; exact joint_le a b
  · rw [jointBC_of_readout J b c]; exact joint_nonneg b c
  · rw [jointBC_of_readout J b c, jointProb2_comm]; exact joint_le c b
  · rw [jointAB_of_readout J a b hA, marginal_partition J a b]
    simpa using outside_nonneg a
  · rw [jointAB_of_readout J a b hA, marginal_partition J a b, complement_mass]
    simpa using outside_le a
  · rw [jointBC_of_readout J b c, jointProb2_comm J b c, marginal_partition J c b]
    simpa using outside_nonneg c
  · rw [jointBC_of_readout J b c, jointProb2_comm J b c, marginal_partition J c b,
      complement_mass]
    simpa using outside_le c

/-- A concrete joint distribution determines a feasible branch allocation;
the construction is derived from event masses, not assumed. -/
noncomputable def queryAllocation (J : JointDistribution n) (a b c : Fin n)
    (hA : marginalProb J a ≠ 0) :
    DeductionBranchAllocation (marginalProb J a) (marginalProb J b)
      (marginalProb J c) (condProb J b a) (condProb J c b) where
  inB := jointProb3 J a b c
  outNotB := jointProb3Neg J a b c
  inB_lower := by
    simpa [deductionBBranchLower, jointAB_of_readout J a b hA, jointBC_of_readout J b c]
      using (positive_branch_bounds J a b c).1
  inB_upper := by
    simpa [deductionBBranchUpper, jointAB_of_readout J a b hA, jointBC_of_readout J b c]
      using (positive_branch_bounds J a b c).2
  outNotB_lower := by
    have splitA := marginal_partition J a b
    have splitC := marginal_partition J c b
    rw [jointProb2_comm J c b] at splitC
    unfold deductionNotBBranchLower
    rw [jointAB_of_readout J a b hA, jointBC_of_readout J b c, complement_mass J b,
      splitA, splitC]
    simpa using (negative_branch_bounds J a b c).1
  outNotB_upper := by
    have splitA := marginal_partition J a b
    have splitC := marginal_partition J c b
    rw [jointProb2_comm J c b] at splitC
    unfold deductionNotBBranchUpper
    rw [jointAB_of_readout J a b hA, jointBC_of_readout J b c, splitA, splitC]
    simpa using (negative_branch_bounds J a b c).2

theorem queryAllocation_strength_eq (J : JointDistribution n) (a b c : Fin n)
    (hA : marginalProb J a ≠ 0) :
    (queryAllocation J a b c hA).strengthAC = completeDeduction J a b c := by
  simp only [DeductionBranchAllocation.strengthAC, DeductionBranchAllocation.jointAC,
    queryAllocation, completeDeduction, Mettapedia.PLN.Core.CompletePLN.condProb, hA, if_false]
  rw [← joint_partition J a b c, jointProb2_comm J a c]

/-- The actual conditional query lies in the no-independence interval. -/
theorem query_mem_credal_interval (J : JointDistribution n) (a b c : Fin n)
    (hA : 0 < marginalProb J a) :
    completeDeduction J a b c ∈ Set.Icc
      (deductionCredalStrengthLower (marginalProb J a) (marginalProb J b)
        (marginalProb J c) (condProb J b a) (condProb J c b))
      (deductionCredalStrengthUpper (marginalProb J a) (marginalProb J b)
        (marginalProb J c) (condProb J b a) (condProb J c b)) := by
  simpa [queryAllocation_strength_eq] using (queryAllocation J a b c hA.ne').strengthAC_mem_interval hA

/-- Query error relative to any point estimate is bounded by the compatible
joint interval, without requiring that estimate itself be probabilistic. -/
theorem query_error_le_credal_radius (J : JointDistribution n) (a b c : Fin n)
    (hA : 0 < marginalProb J a) (estimate : ℝ) :
    |completeDeduction J a b c - estimate| ≤ intervalErrorRadius
      (deductionCredalStrengthLower (marginalProb J a) (marginalProb J b)
        (marginalProb J c) (condProb J b a) (condProb J c b))
      (deductionCredalStrengthUpper (marginalProb J a) (marginalProb J b)
        (marginalProb J c) (condProb J b a) (condProb J c b)) estimate :=
  error_le_intervalErrorRadius (query_mem_credal_interval J a b c hA)

/-- A compatible endpoint allocation attains the claimed error radius.
The existing `alloc.probDist` realizes it as an eight-atom probability model. -/
theorem credal_radius_attained (pA pB pC sAB sBC estimate : ℝ)
    (feasible : DeductionBranchFeasibility pA pB pC sAB sBC) :
    ∃ alloc : DeductionBranchAllocation pA pB pC sAB sBC,
      |alloc.strengthAC - estimate| = intervalErrorRadius
        (deductionCredalStrengthLower pA pB pC sAB sBC)
        (deductionCredalStrengthUpper pA pB pC sAB sBC) estimate := by
  let lower := deductionLowerEndpointBranchAllocation pA pB pC sAB sBC feasible
  let upper := deductionUpperEndpointBranchAllocation pA pB pC sAB sBC feasible
  have low := deductionLowerEndpointBranchAllocation_strengthAC pA pB pC sAB sBC feasible
  have high := deductionUpperEndpointBranchAllocation_strengthAC pA pB pC sAB sBC feasible
  by_cases farther : |lower.strengthAC - estimate| ≤ |upper.strengthAC - estimate|
  · refine ⟨upper, ?_⟩
    dsimp [upper, lower] at farther ⊢
    simpa [intervalErrorRadius, low, high] using (max_eq_right farther).symm
  · refine ⟨lower, ?_⟩
    dsimp [upper, lower] at farther ⊢
    simpa [intervalErrorRadius, low, high] using (max_eq_left (le_of_not_ge farther)).symm

/-- Sharpness specialized to the five readouts of an actual joint model. -/
theorem query_credal_radius_attained (J : JointDistribution n) (a b c : Fin n)
    (hA : marginalProb J a ≠ 0) (estimate : ℝ) :
    ∃ alloc : DeductionBranchAllocation (marginalProb J a) (marginalProb J b)
        (marginalProb J c) (condProb J b a) (condProb J c b),
      |alloc.strengthAC - estimate| = intervalErrorRadius
        (deductionCredalStrengthLower (marginalProb J a) (marginalProb J b)
          (marginalProb J c) (condProb J b a) (condProb J c b))
        (deductionCredalStrengthUpper (marginalProb J a) (marginalProb J b)
          (marginalProb J c) (condProb J b a) (condProb J c b)) estimate :=
  credal_radius_attained _ _ _ _ _ _ (query_feasible J a b c hA)

/-- No estimate from these five readouts can guarantee less than half the
compatible interval width: an actual eight-atom model defeats that claim. -/
theorem five_readout_minimax_lower_bound (J : JointDistribution n) (a b c : Fin n)
    (hA : 0 < marginalProb J a) (estimate : ℝ) :
    ∃ alloc : DeductionBranchAllocation (marginalProb J a) (marginalProb J b)
        (marginalProb J c) (condProb J b a) (condProb J c b),
      (deductionCredalStrengthUpper (marginalProb J a) (marginalProb J b)
          (marginalProb J c) (condProb J b a) (condProb J c b) -
        deductionCredalStrengthLower (marginalProb J a) (marginalProb J b)
          (marginalProb J c) (condProb J b a) (condProb J c b)) / 2 ≤
        |alloc.strengthAC - estimate| := by
  obtain ⟨alloc, attained⟩ := query_credal_radius_attained J a b c hA.ne' estimate
  refine ⟨alloc, ?_⟩
  rw [attained]
  exact half_width_le_intervalErrorRadius _ _ estimate

end Mettapedia.PLN.Comparisons.ScreeningErrorBounds
