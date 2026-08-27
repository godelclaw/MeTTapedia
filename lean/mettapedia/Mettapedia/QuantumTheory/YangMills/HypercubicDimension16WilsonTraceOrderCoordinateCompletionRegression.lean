import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCoordinateCompletion

/-! Regression checks for OUR finite trace-order coordinate completion. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCoordinateCompletionRegression

open HypercubicDimension16WilsonTraceOrderCoordinateCompletion
open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16IncomingCommutatorTraceCoupledColumn
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator

example : Function.Injective ourPhysicalTraceCoordinatePacket :=
  ourPhysicalTraceCoordinatePacket_injective

example : ourPhysicalTraceCoordinatePacket
    literalIncomingCommutatorClass ≠ 0 :=
  ourPhysicalTraceCoordinatePacket_literalIncoming_ne_zero

example (policy : PhysicalRelationPolicy) :
    ourCoupledTraceOrderCoordinatePacket
      (coupledIncomingQuotientMap
        (exactFieldSevenEightProjection
          (orbitPhysicalRelationOperator policy
            (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)))) = 0 :=
  ourCoupledTraceOrderCoordinatePacket_physicalCommutator_zero policy

example : ourCoupledTraceOrderCoordinatePacket
    (coupledIncomingQuotientMap
      (0, coupledIncomingCommutatorVector.2)) ≠ 0 :=
  ourCoupledTraceOrderCoordinatePacket_eightComponent_ne_zero

#print axioms ourPhysicalTraceCoordinateSynthesis_comp_packet
#print axioms ourPhysicalTraceCoordinatePacket_injective
#print axioms ourCoupledTraceOrderCoordinatePacket_physicalCommutator_zero
#print axioms ourCoupledTraceOrderCoordinatePacket_eightComponent_ne_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCoordinateCompletionRegression
