import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileRepair

/-! Regression checks for OUR universal three-cut trace-cycle profile repair. -/

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16JointPhysicalQuotient
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

#print axioms HypercubicDimension16FundamentalTraceCycleProfile.ourDistinctThreeCutProfileNumerators_all_zero
#print axioms HypercubicDimension16FundamentalTraceCycleProfile.ourTraceCycleProfile_forced
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileRepair.ourInvariantTraceCycleProfileCoordinate_signed_action
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileRepair.ourCycleProfileInvariantTraceOrderCorrection_ourFundamentalThreeCut_zero
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileRepair.ourCycleProfileInvariantTraceOrderCorrection_ourTraceAnticommutator_zero
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileRepair.ourCycleProfileInvariantTraceOrderCorrection_invariantFundamentalThreeCut_zero
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileRepair.ourCycleProfileInvariantTraceOrderCorrection_invariantTraceAnticommutator_zero

end YangMills
end QuantumTheory
end Mettapedia
