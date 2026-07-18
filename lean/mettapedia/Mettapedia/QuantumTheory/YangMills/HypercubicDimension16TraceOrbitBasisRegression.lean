import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitBasis

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceOrbitBasisRegression

open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16TraceOrbitChartCore
open HypercubicDimension16TraceOrbitChart
open HypercubicDimension16TraceOrbitChartCertificate
open HypercubicDimension16TraceOrbitChartSignCertificate
open HypercubicDimension16TraceOrbitProductSignatureCertificate
open HypercubicDimension16TraceOrbitHistogramSignCertificate
open HypercubicDimension16TraceOrbitBasis

example {left right : PositiveRepresentativeIndex} (hdifferent : left ≠ right) :
    ∀ h : V14HypercubicFDCensus.Hypercubic4,
      (positiveRepresentativeTarget left).hypercubicAct h ≠
        positiveRepresentativeTarget right :=
  positiveRepresentativeTargets_hypercubic_separated hdifferent

example (index : PositiveRepresentativeIndex)
    (h : V14HypercubicFDCensus.Hypercubic4)
    (hfixed : (positiveRepresentativeTarget index).hypercubicAct h =
      positiveRepresentativeTarget index) :
    (positiveRepresentativeTarget index).tensorSign h = 1 :=
  positiveRepresentativeTarget_stabilizer_sign index h hfixed

example : LinearIndependent ℚ positiveRepresentativeReynoldsVector :=
  positiveRepresentativeReynoldsVector_linearIndependent

example : Module.finrank ℚ FieldEightSignedOrbitCoinvariant = 11654 :=
  fieldEightSignedOrbitCoinvariant_finrank

#print axioms representative_product_signature_replay
#print axioms directRepresentativeCanonicalProductSignature_injective
#print axioms representative_histogram_stabilizers_positive
#print axioms positiveRepresentativeTarget_stabilizer_sign
#print axioms positiveRepresentativeReynoldsVector_linearIndependent
#print axioms positiveRepresentativeReynoldsBasis
#print axioms positiveRepresentativeCoinvariantBasis

end HypercubicDimension16TraceOrbitBasisRegression
end YangMills
end QuantumTheory
end Mettapedia
