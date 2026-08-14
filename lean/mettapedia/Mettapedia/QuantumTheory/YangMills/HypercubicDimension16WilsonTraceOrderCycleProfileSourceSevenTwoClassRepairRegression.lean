import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair

/-!
# Regression for OUR two-class source-seven repair

The finite selector matrix and both named source-seven cancellations are
replayed here through the public repair interface.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepairRegression

open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenMismatch
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
example (policy : PhysicalRelationPolicy) :
    ourTwoClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 :=
  ourTwoClassSourceSevenTraceOrderCorrection_ourCommutator_zero policy

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
example (policy : PhysicalRelationPolicy) :
    ourTwoClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) = 0 :=
  ourTwoClassSourceSevenTraceOrderCorrection_ourSecondaryCommutator_zero policy

#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair.ourTwoClassSourceSevenTraceOrderCorrection_ourCommutator_zero
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair.ourTwoClassSourceSevenTraceOrderCorrection_ourSecondaryCommutator_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepairRegression
