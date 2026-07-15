import Mettapedia.QuantumTheory.YangMills.V14HypercubicFDCensus

/-!
# Regression checks for the hypercubic `F,D` census kernel
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace V14HypercubicFDCensusRegression

open V14HypercubicFDCensus

example : Fintype.card Hypercubic4 = 384 :=
  Hypercubic4.card_hypercubic4

example : FDRelationPolicy.o9OffShell.enables
    .equationOfMotion = false := rfl

example : FDRelationPolicy.f43OnShell.enables
    .equationOfMotion = true := rfl

example {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (certificate : ExactCensusCertificate Coordinate) :
    certificate.Checks := certificate.checks

#print axioms Hypercubic4.compose_assoc
#print axioms Hypercubic4.inverse_compose
#print axioms Hypercubic4.compose_inverse
#print axioms Hypercubic4.axisSign_compose
#print axioms Hypercubic4.card_hypercubic4
#print axioms Hypercubic4.orientationSign_compose
#print axioms RawFDMonomial.act_compose
#print axioms RawFDMonomial.tensorSign_compose
#print axioms ContractionParity.character_compose
#print axioms rawFDCensus_finite
#print axioms relationMatrix_indices_finite
#print axioms ExactCensusCertificate.checks

end V14HypercubicFDCensusRegression
end YangMills
end QuantumTheory
end Mettapedia
