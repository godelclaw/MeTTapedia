import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CompressionSemanticBridge

/-!
# Regression and axiom audit for the dimension-sixteen compression census

The checks below pin the exhaustive signed-permutation replay, its semantic
bridge to literal group powers, the fourteen-class Reynolds regrouping, and
the eight exact sector values.  The census concerns the explicitly defined
cycle-index expression; it does not realize a finite carrier and does not
assert equivalence with the physical relation quotient.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CompressionRegression

open V14HypercubicFDCensus
open HypercubicRawFDCharacterCensus
open HypercubicDimension16CompressionCensus

example (h : Hypercubic4) (exponent : ℕ) :
    recurrentVectorPowerCharacter h exponent =
      vectorCharacter (h ^ exponent) :=
  recurrentVectorPowerCharacter_eq h exponent

example (permutation : Fin 24) :
    decodedPowerTraceReplayCheckAt permutation = true :=
  decodedPowerTraceReplayCheckAt_certificate permutation

example (traceClass : PowerTraceClass) :
    decodedClassMultiplicity traceClass = classMultiplicity traceClass :=
  decodedClassMultiplicity_certificate traceClass

example (traceClass : PowerTraceClass) (fieldIndex : Fin 8) :
    classCompressedSectorCharacter traceClass (fieldIndex.1 + 1) =
      expectedClassCompressedSectorCharacter traceClass
        (fieldIndex.1 + 1) :=
  classCompressedSectorCharacter_certificate traceClass fieldIndex

example (fieldIndex : Fin 8) :
    compressedCarrierCardinality (fieldIndex.1 + 1) =
      expectedCompressedCarrierCardinality (fieldIndex.1 + 1) :=
  compressedCarrierCardinality_certificate fieldIndex

example (parity : ContractionParity) (fieldIndex : Fin 8) :
    compressedInvariantMultiplicity parity (fieldIndex.1 + 1) =
      expectedCompressedInvariantMultiplicity parity (fieldIndex.1 + 1) :=
  compressedInvariantMultiplicity_certificate parity fieldIndex

example :
    (∑ fieldCount ∈ Finset.Icc 1 8,
      expectedCompressedCarrierCardinality fieldCount) =
      47231161854 :=
  expectedCompressedCarrierCardinality_total

example :
    (∑ fieldCount ∈ Finset.Icc 1 8,
      expectedCompressedInvariantMultiplicity .scalar fieldCount) =
      246136792 :=
  expectedCompressedScalarMultiplicity_total

example :
    (∑ fieldCount ∈ Finset.Icc 1 8,
      expectedCompressedInvariantMultiplicity .pseudoscalar fieldCount) =
      246121092 :=
  expectedCompressedPseudoscalarMultiplicity_total

#print axioms recurrentVectorPowerCharacter_eq
#print axioms decodedPowerTraceReplayCheckAt_certificate
#print axioms decodedOrientationReplayCheckAt_certificate
#print axioms decodedClassMultiplicity_certificate
#print axioms classCompressedSectorCharacter_certificate
#print axioms compressedCarrierCardinality_certificate
#print axioms compressedInvariantMultiplicity_eq_classCompressed
#print axioms compressedInvariantMultiplicity_certificate
#print axioms expectedCompressedCarrierCardinality_total
#print axioms expectedCompressedScalarMultiplicity_total
#print axioms expectedCompressedPseudoscalarMultiplicity_total

end HypercubicDimension16CompressionRegression
end YangMills
end QuantumTheory
end Mettapedia
