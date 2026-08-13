import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTracePhysicalFieldEight

/-! Regression checks for OUR complete physical three-cut field-eight kernel. -/

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16FundamentalTracePhysicalFamily
open HypercubicDimension16FundamentalTracePhysicalFieldEight
open HypercubicDimension16JointTraceRankTransfer

example (policy : PhysicalRelationPolicy) (labels : OurCertifiedThreeCutLabel) :
    ourJointFieldEightInvariantProjection policy
      (ourFundamentalTraceToJointRelation policy
        (Finsupp.single labels 1)) = 0 :=
  ourJointFieldEightInvariantProjection_fundamentalTraceSingle_zero policy labels

example (policy : PhysicalRelationPolicy)
    (cochain : OurFundamentalTraceCochainSpace) :
    ourJointFieldEightInvariantProjection policy
      (ourFundamentalTraceToJointRelation policy cochain) = 0 :=
  ourJointFieldEightInvariantProjection_fundamentalTrace_zero policy cochain

#print axioms HypercubicDimension16FundamentalTracePhysicalFieldEight.ourJointFieldEightInvariantProjection_fundamentalTraceSingle_zero
#print axioms HypercubicDimension16FundamentalTracePhysicalFieldEight.ourJointFieldEightInvariantProjection_fundamentalTrace_zero

end YangMills
end QuantumTheory
end Mettapedia
