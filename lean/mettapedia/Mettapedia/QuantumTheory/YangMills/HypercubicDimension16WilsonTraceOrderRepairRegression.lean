import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderRepair

/-! Regression checks for OUR local trace-order Wilson-coordinate repair. -/

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16WilsonTraceOrderRepair
open HypercubicDimension16FieldEightPhysicalTrace

example :
    ¬ ∃ descended : CoupledIncomingQuotient →ₗ[ℚ]
        FieldEightPhysicalTraceQuotient,
      descended.comp coupledIncomingQuotientMap =
        ourFieldEightTraceOnlyCoordinate :=
  no_ourFieldEightTraceOnlyCoordinate_descent

example
    (seven : FieldSevenOrbitSpace →ₗ[ℚ] FieldEightPhysicalTraceQuotient)
    (descended : CoupledIncomingQuotient →ₗ[ℚ]
      FieldEightPhysicalTraceQuotient)
    (hdescended : descended.comp coupledIncomingQuotientMap =
      ourTraceOrderCorrectedCoordinate seven) :
    seven ≠ 0 :=
  descended_ourTraceOrderCorrection_forces_seven_ne_zero seven descended hdescended

example (policy : PhysicalRelationPolicy) :
    ourTraceOrderAwareLocalQuotientCoordinate
      (coupledIncomingQuotientMap
        (exactFieldSevenEightProjection
          (orbitPhysicalRelationOperator policy
            (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)))) = 0 :=
  ourTraceOrderAwareLocalQuotientCoordinate_physicalCommutator_zero policy

example :
    ourTraceOrderAwareLocalQuotientCoordinate
      (coupledIncomingQuotientMap
        (0, coupledIncomingCommutatorVector.2)) ≠ 0 :=
  ourTraceOrderAwareLocalQuotientCoordinate_detects_eightComponent_ne_zero

example (a : ℝ) (coordinate : Fin 17) :
    (ourLocalWilsonTraceOrderRepairData a).cartanWilsonPacket coordinate =
      if coordinate = 0 then -(a ^ 12) / 20160 else 0 :=
  ourLocalWilsonTraceOrderRepairData_cartanWilsonPacket a coordinate

#print axioms HypercubicDimension16WilsonTraceOrderRepair.no_ourFieldEightTraceOnlyCoordinate_descent
#print axioms HypercubicDimension16WilsonTraceOrderRepair.descended_ourTraceOrderCorrection_forces_sevenValue
#print axioms HypercubicDimension16WilsonTraceOrderRepair.descended_ourTraceOrderCorrection_forces_seven_ne_zero
#print axioms HypercubicDimension16WilsonTraceOrderRepair.ourTraceOrderAwareLocalQuotientCoordinate_physicalCommutator_zero
#print axioms HypercubicDimension16WilsonTraceOrderRepair.ourTraceOrderAwareLocalQuotientCoordinate_detects_eightComponent_ne_zero
#print axioms HypercubicDimension16WilsonTraceOrderRepair.ourLocalWilsonTraceOrderRepairData_cartanWilsonPacket
#print axioms HypercubicDimension16WilsonTraceOrderRepair.ourLocalWilsonTraceOrderRepairData_traceOrderSignal_ne_zero

end YangMills
end QuantumTheory
end Mettapedia
