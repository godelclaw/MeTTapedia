import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonCartanTraceOrderFaithfulnessNoGo

/-! Regression checks for OUR trace-order-faithful Cartan Wilson no-go. -/

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

open HypercubicDimension16WilsonCartanTraceOrderFaithfulnessNoGo

example (a : ℝ) :
    ¬ Nonempty (OurIncomingTraceOrderFaithfulCartanWilsonCoordinate a) :=
  no_ourIncomingTraceOrderFaithfulCartanWilsonCoordinate a

example (a : ℝ) :
    ¬ Nonempty (OurTraceOrderFaithfulCartanWilsonCoordinate a) :=
  no_ourTraceOrderFaithfulCartanWilsonCoordinate a

#print axioms HypercubicDimension16WilsonCartanTraceOrderFaithfulnessNoGo.ourRawLabeledToFieldEightTraceClass_incomingRawDifference
#print axioms HypercubicDimension16WilsonCartanTraceOrderFaithfulnessNoGo.no_ourIncomingTraceOrderFaithfulCartanWilsonCoordinate
#print axioms HypercubicDimension16WilsonCartanTraceOrderFaithfulnessNoGo.no_ourTraceOrderFaithfulCartanWilsonCoordinate

end YangMills
end QuantumTheory
end Mettapedia
