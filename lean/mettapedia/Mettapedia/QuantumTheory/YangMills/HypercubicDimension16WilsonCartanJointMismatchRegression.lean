import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonCartanJointMismatch

/-! Regression checks for OUR Cartan-Wilson / joint-quotient mismatch. -/

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

open HypercubicDimension16PhysicalTraceQuotient
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicDimension16WilsonCartanJointMismatch

example (a : ℝ) :
    ourRawCartanWilsonEighthJet a ourIncomingRawDifference = 0 :=
  ourRawCartanWilsonEighthJet_incomingRawDifference_zero a

example (a : ℝ) :
    ourRawCartanWilsonEighthJet a ourIncomingRawDifference = 0 ∧
      literalIncomingCommutatorClass ≠ 0 :=
  ourCartanWilson_traceQuotient_explicitMismatch a

example (candidate : FieldEightPhysicalTraceQuotient →ₗ[ℚ] (Fin 17 → ℚ)) :
    ¬ Function.Injective candidate :=
  no_cartan17Coordinate_fullTraceDual_injective candidate

#print axioms HypercubicDimension16WilsonCartanJointMismatch.ourRawLabeledToFieldEightOrbit_incomingRawDifference
#print axioms HypercubicDimension16WilsonCartanJointMismatch.ourRawCartanWilsonEighthJet_incomingRawDifference_zero
#print axioms HypercubicDimension16WilsonCartanJointMismatch.ourCartanWilson_traceQuotient_explicitMismatch
#print axioms HypercubicDimension16WilsonCartanJointMismatch.no_cartan17Coordinate_fullTraceDual_injective

end YangMills
end QuantumTheory
end Mettapedia
