import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTracePhysicalFamily

/-! Regression checks for OUR complete physical fundamental-trace family. -/

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

open V14HypercubicFDCensus
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16JointQuotientInvariants
open HypercubicDimension16FundamentalTraceCycleProfile
open HypercubicDimension16FundamentalTracePhysicalFamily
open HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair

example (labels : OurThreeCutLabels) :
    labels ∈ ourDistinctThreeCutLabels ↔
      labels.1 ≠ labels.2.1 ∧ labels.1 ≠ labels.2.2 ∧
        labels.2.1 ≠ labels.2.2 :=
  ourDistinctThreeCutLabels_mem_iff labels

example : Function.Injective ourFundamentalTraceSiteOf :=
  ourFundamentalTraceSiteOf_injective

example (policy : PhysicalRelationPolicy) :
    Function.Injective (ourFundamentalTraceGeneratorAt policy) :=
  ourFundamentalTraceGeneratorAt_injective policy

example (policy : PhysicalRelationPolicy) :
    Function.Injective (ourFundamentalTraceCochainEmbedding policy) :=
  ourFundamentalTraceCochainEmbedding_injective policy

example (policy : PhysicalRelationPolicy) (labels : OurCertifiedThreeCutLabel) :
    ((ourFundamentalTraceToJointRelation policy
      (Finsupp.single labels 1)).1).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFundamentalTraceGeneratorAt policy labels) 1)) :=
  ourFundamentalTraceToJointRelation_single_val policy labels

example (policy : PhysicalRelationPolicy)
    (cochain : OurFundamentalTraceCochainSpace) (h : Hypercubic4) :
    signedExactFieldRelabelOrbitAction h
      ((ourFundamentalTraceToJointRelation policy cochain).1).1 =
      ((ourFundamentalTraceToJointRelation policy cochain).1).1 :=
  ourFundamentalTraceToJointRelation_signed_invariant policy cochain h

example (policy : PhysicalRelationPolicy) :
    ((ourFundamentalTraceToJointRelation policy
      (Finsupp.single ourCanonicalThreeCutLabel 1)).1).1 =
      (ourInvariantFundamentalThreeCutRow policy).1 :=
  ourFundamentalTraceToJointRelation_canonical_val policy

#print axioms HypercubicDimension16FundamentalTracePhysicalFamily.ourFundamentalTraceSiteOf_injective
#print axioms HypercubicDimension16FundamentalTracePhysicalFamily.ourFundamentalTraceGeneratorAt_injective
#print axioms HypercubicDimension16FundamentalTracePhysicalFamily.ourFundamentalTraceCochainEmbedding_injective
#print axioms HypercubicDimension16FundamentalTracePhysicalFamily.ourFundamentalTraceToJointRelation_single_val
#print axioms HypercubicDimension16FundamentalTracePhysicalFamily.ourFundamentalTraceToJointRelation_signed_invariant
#print axioms HypercubicDimension16FundamentalTracePhysicalFamily.ourFundamentalTraceToJointRelation_canonical_val

end YangMills
end QuantumTheory
end Mettapedia
