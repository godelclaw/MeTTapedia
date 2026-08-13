import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FieldEightTracePhysicalCompleteness
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenCorrectionRefutation

/-! Regression checks for OUR universal three-cut trace-cycle profile repair. -/

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalRelationBlocks
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16JointQuotientInvariants
open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16FieldEightTracePhysicalLift
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair
open HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction
open HypercubicDimension16WilsonTraceOrderTraceTopologyRepair
open HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair
open HypercubicDimension16FundamentalTraceCycleProfile
open HypercubicDimension16WilsonTraceOrderCycleProfileRepair
open HypercubicDimension16FieldEightTracePhysicalCompleteness
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenMismatch
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenCorrectionRefutation

example : ourDistinctThreeCutLabels.length = 210 :=
  ourDistinctThreeCutLabels_card

example : ∀ numerator ∈ ourDistinctThreeCutProfileNumerators, numerator = 0 :=
  ourDistinctThreeCutProfileNumerators_all_zero

example (labels : OurThreeCutLabels) (hlabels : labels ∈ ourDistinctThreeCutLabels) :
    ourFundamentalThreeCutCycleProfileValue labels = 0 :=
  ourFundamentalThreeCutCycleProfileValue_zero labels hlabels

example (c2 c3 c4 c5 c6 : ℚ)
    (hA : -c2 - 2 * c6 = 0)
    (hB : -c3 - c5 - c6 = 0)
    (hC : -2 * c3 - 2 * c4 - c6 = 0)
    (hD : -2 * c2 - c4 - 2 * c5 = 0)
    (hAnti : (1 / 2 : ℚ) - c2 - c5 = 0) :
    c2 = 6 / 5 ∧ c3 = 13 / 10 ∧ c4 = -1 ∧ c5 = -7 / 10 ∧ c6 = -3 / 5 :=
  ourTraceCycleProfile_forced c2 c3 c4 c5 c6 hA hB hC hD hAnti

example (policy : PhysicalRelationPolicy) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_ourFundamentalThreeCut_zero policy

example (policy : PhysicalRelationPolicy) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_ourTraceAnticommutator_zero policy

example (policy : PhysicalRelationPolicy) :
    ourCycleProfileInvariantTraceOrderCorrection
      (ourInvariantFundamentalThreeCutRow policy).1 = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_invariantFundamentalThreeCut_zero policy

example (policy : PhysicalRelationPolicy) :
    ourCycleProfileInvariantTraceOrderCorrection
      (ourInvariantTraceAnticommutatorRow policy).1 = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_invariantTraceAnticommutator_zero policy

example (policy : PhysicalRelationPolicy)
    (carrier : RelationCarrier) (slot : Fin carrier.1.1) (coefficient : ℚ) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (.antisymmetry carrier slot) coefficient)) = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_antisymmetry_zero
    policy carrier slot coefficient

example (policy : PhysicalRelationPolicy)
    (carrier : RelationCarrier) (slot : Fin carrier.1.1) (coefficient : ℚ) :
    ourCycleProfileInvariantTraceOrderCorrection
      (exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (.antisymmetry carrier slot) coefficient))) = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_invariantAntisymmetry_zero
    policy carrier slot coefficient

example (policy : PhysicalRelationPolicy)
    (generator : PhysicalRelationGenerator policy) (coefficient : ℚ)
    (hsource : physicalRelationGeneratorSourceFieldCount generator =
      ourEightFieldCount) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single generator coefficient)) = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_eq_eight
    policy generator coefficient hsource

example (policy : PhysicalRelationPolicy)
    (generator : PhysicalRelationGenerator policy) (coefficient : ℚ)
    (hsix : physicalRelationGeneratorSourceFieldCount generator ≠ (6 : Fin 9))
    (hseven : physicalRelationGeneratorSourceFieldCount generator ≠ ourSevenFieldCount) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single generator coefficient)) = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_not_six_or_seven
    policy generator coefficient hsix hseven

example (policy : PhysicalRelationPolicy)
    (generator : PhysicalRelationGenerator policy) (coefficient : ℚ)
    (hseven : physicalRelationGeneratorSourceFieldCount generator ≠ ourSevenFieldCount) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single generator coefficient)) = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_ne_seven
    policy generator coefficient hseven

example (policy : PhysicalRelationPolicy) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) ≠ 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_ourSecondaryCommutator_ne_zero policy

example (policy : PhysicalRelationPolicy) :
    incomingQuotientTraceEvaluation ⟨2, by decide⟩
      (ourCycleProfileInvariantTraceOrderCorrection
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1))) =
      (4 : ℚ) / 3 :=
  incomingQuotientTraceEvaluation_cycleProfileCorrection_ourSecondaryCommutator policy

#print axioms HypercubicDimension16FundamentalTraceCycleProfile.ourDistinctThreeCutProfileNumerators_all_zero
#print axioms HypercubicDimension16FundamentalTraceCycleProfile.ourTraceCycleProfile_forced
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileRepair.ourInvariantTraceCycleProfileCoordinate_signed_action
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileRepair.ourCycleProfileInvariantTraceOrderCorrection_ourFundamentalThreeCut_zero
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileRepair.ourCycleProfileInvariantTraceOrderCorrection_ourTraceAnticommutator_zero
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileRepair.ourCycleProfileInvariantTraceOrderCorrection_invariantFundamentalThreeCut_zero
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileRepair.ourCycleProfileInvariantTraceOrderCorrection_invariantTraceAnticommutator_zero
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileRepair.ourCycleProfileInvariantTraceOrderCorrection_antisymmetry_zero
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileRepair.ourCycleProfileInvariantTraceOrderCorrection_invariantAntisymmetry_zero
#print axioms HypercubicDimension16FieldEightTracePhysicalCompleteness.ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_eq_eight
#print axioms HypercubicDimension16FieldEightTracePhysicalCompleteness.ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_not_six_or_seven
#print axioms HypercubicDimension16FieldEightTracePhysicalCompleteness.ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_ne_seven
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenMismatch.rawReynoldsTraceEvaluation_ourSecondaryCommutatorVector
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenCorrectionRefutation.incomingQuotientTraceEvaluation_cycleProfileCorrection_ourSecondaryCommutator
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenCorrectionRefutation.ourCycleProfileInvariantTraceOrderCorrection_ourSecondaryCommutator_ne_zero

end YangMills
end QuantumTheory
end Mettapedia
